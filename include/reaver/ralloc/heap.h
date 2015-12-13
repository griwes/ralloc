/**
 * libralloc License
 *
 * Copyright © 2015 Michał "Griwes" Dominiak
 *
 * This software is provided 'as-is', without any express or implied
 * warranty. In no event will the authors be held liable for any damages
 * arising from the use of this software.
 *
 * Permission is granted to anyone to use this software for any purpose,
 * including commercial applications, and to alter it and redistribute it
 * freely, subject to the following restrictions:
 *
 * 1. The origin of this software must not be misrepresented; you must not
 *    claim that you wrote the original software. If you use this software
 *    in a product, an acknowledgment in the product documentation is required.
 * 2. Altered source versions must be plainly marked as such, and must not be
 *    misrepresented as being the original software.
 * 3. This notice may not be removed or altered from any source distribution.
 *
 **/

#include <iostream>

#include <cstdint>
#include <list>
#include <memory>
#include <array>
#include <mutex>
#include <cstddef>
#include <cassert>
#include <algorithm>
#include <type_traits>
#include <atomic>

#include <boost/optional.hpp>

#include <reaver/unit.h>
#include <reaver/relaxed_constexpr.h>
#include <reaver/id.h>
#include <reaver/tls.h>

#ifdef __unix__
namespace reaver { namespace ralloc { namespace _unix_detail {
# include <sys/mman.h>
}}}
#endif

namespace reaver
{
    namespace ralloc { inline namespace _v1
    {
        namespace platform
        {
            using memory_allocation_handle = void *;
            using unique_lock = std::mutex;
            using lock = std::recursive_mutex;

            constexpr std::size_t chunk_size = 128 * 1024;
            constexpr std::size_t min_chunk_size = 4096;
        }

        struct allocation_info
        {
            std::uintptr_t address;
            boost::optional<platform::memory_allocation_handle> handle;
        };

        namespace platform
        {
            inline void heap_assert(bool condition, const char * description)
            {
                if (!condition)
                {
                    std::cout << description << std::endl;
                    std::abort();
                }
            }

            inline void terminate()
            {
                std::terminate();
            }

            allocation_info map(std::size_t size)
            {
                assert(size == chunk_size);
                auto address = _unix_detail::mmap(0, chunk_size, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);

                heap_assert(address != MAP_FAILED, "Failed to allocate more memory from the operating system.");

                return { reinterpret_cast<std::uintptr_t>(address), address };
            }

            inline void unmap(memory_allocation_handle handle)
            {
                _unix_detail::munmap(handle, platform::chunk_size);
            }
        }

        // looks like clang (or potentially C++) is insane
        // without this being a dummy template, the constexpr members fail to compile
        // because "function is not defined"
        // looks like the point of instantiation of the functions is too late in the non-template case
        // this is bullshit
        //
        // possibly related (bug report closed as resolved though): http://stackoverflow.com/a/10727719/809387
        template<typename>
        class heap_
        {
        public:
            heap_()
            {
            }

            void * allocate(std::size_t size, std::size_t alignment = alignof(std::max_align_t))
            {
                if (size == 0)
                {
                    return nullptr;
                }

                // align size to 16
                size += 15;
                size &= ~15ull;

                if (size < platform::min_chunk_size)
                {
                    return _microallocate(size);
                }

                if (size > platform::chunk_size)
                {
                    assert(false);
                }

                auto bin = std::find_if(_get_bin(size), _bins.end(), [](_bin & bin)
                {
                    bin.lock.lock();
                    if (bin.first)
                    {
                        return true;
                    }
                    bin.lock.unlock();
                    return false;
                });

                if (bin == _bins.end())
                {
                    _bins.back().lock.lock();
                    _save(_allocate_chunk());
                    bin = &_bins.back();
                }

                auto chunk = bin->first;
                chunk->lock.lock();
                bin->first = chunk->next;

                bin->lock.unlock();

                platform::heap_assert(chunk->state == _chunk_state::free, "found a non-free chunk in bins");

                while (chunk->chunk_size > 2 * size && bin != _bins.begin())
                {
                    chunk = _split(chunk);
                }

                chunk->next = nullptr;
                chunk->prev = nullptr;
                chunk->allocation_size = size;
                platform::heap_assert(chunk->allocation_size <= chunk->chunk_size, "an allocated chunk is too small");
                chunk->state = _chunk_state::allocated;

                chunk->lock.unlock();

                return reinterpret_cast<void *>(chunk->header + 1);
            }

            void * allocate_clean(std::size_t size, std::size_t alignment = alignof(std::max_align_t))
            {
                auto ptr = allocate(size, alignment);
                auto buf = static_cast<unsigned char *>(ptr);
                std::fill(buf, buf + size, 0);
                return ptr;
            }

            void * reallocate(void * ptr, std::size_t new_size);

            void free(void * ptr)
            {
                {
                    auto address = reinterpret_cast<std::uintptr_t>(ptr);
                    auto self = reinterpret_cast<std::uintptr_t>(this);

                    if (self <= address && address < self + sizeof(*this))
                    {
                        return;
                    }
                }

                assert(false);
            }

            void flush();

            template<typename T>
            struct deleter
            {
                void operator()(T * ptr) const
                {
                    ptr->~T();
                    if (heap)
                    {
                        heap->free(static_cast<void *>(ptr));
                    }
                }

                heap_ * heap;
            };

            template<typename T>
            using unique_ptr = std::unique_ptr<T, deleter<T>>;

            template<typename T, typename... Args>
            unique_ptr<T> make_unique(Args &&... args)
            {
                auto ptr = allocate(sizeof(T), alignof(T));
                return { new (ptr) T(std::forward<Args>(args)...), deleter<T>{ this } };
            }

            void assert_magics() const
            {
                _microheaps_lock.lock();
                for (auto & bin : _bins)
                {
                    bin.lock.lock();
                }

                for (auto mh = _microheaps; mh != nullptr; mh = mh->next)
                {
                    _assert_magic(reinterpret_cast<_micro_chunk_header *>(mh + 1), mh->chunk->allocation_size);
                }

                auto * chunk_ptr = &_heap_chunks;
                while (*chunk_ptr)
                {
                    auto & chunk = **chunk_ptr;

                    platform::heap_assert(!!chunk.descriptor, "missing chunk descriptor");
                    _assert_magic(*chunk.descriptor);

                    chunk_ptr = &chunk.next;
                }

                for (auto & bin : _bins)
                {
                    bin.lock.unlock();
                }
                _microheaps_lock.unlock();
            }

        private:
            static constexpr std::uint64_t _magic = 0xDAED4321DAED4321;
            static constexpr std::uint64_t _micro_magic = 0x1234DEAD1234DEAD;
            static constexpr std::size_t _min_microheap_size = 16;

            enum class _chunk_state
            {
                free,
                allocated,
                divided,
                micro_managed
            };

            struct _chunk_descriptor;

            struct _bin
            {
                std::size_t size;
                mutable platform::lock lock;
                _chunk_descriptor * first = nullptr;
            };

            struct _chunk_header;

            struct _chunk_descriptor
            {
                platform::lock lock;
                _chunk_descriptor * prev = nullptr;
                _chunk_descriptor * next = nullptr;
                _chunk_state state = _chunk_state::free;
                _chunk_header * header = nullptr;
                std::size_t allocation_size = 0;
                std::size_t chunk_size = 0;
                _chunk_descriptor * parent = nullptr;
                _chunk_descriptor * left_child = nullptr;
                _chunk_descriptor * right_child = nullptr;
                _bin * bin = nullptr;
            };

            struct _chunk_header
            {
                std::uint64_t magic = _magic;
                _chunk_descriptor * chunk = nullptr;
            };

            void _assert_magic(const _chunk_descriptor & desc) const
            {
                platform::heap_assert(desc.parent || desc.chunk_size == platform::chunk_size - sizeof(_chunk_header), "missing parent pointer");

                if (desc.state == _chunk_state::divided)
                {
                    platform::heap_assert(desc.left_child && desc.right_child, "missing child descriptor of a divided chunk");
                    _assert_magic(*desc.left_child);
                    _assert_magic(*desc.right_child);
                }

                else
                {
                    platform::heap_assert(desc.header->magic == _magic, "invalid magic in chunk header");
                }
            }

            struct _chunk
            {
                _chunk() = default;

                _chunk(const _chunk &) = delete;
                _chunk & operator=(const _chunk &) = delete;

                _chunk(_chunk && other)
                {
                    this->swap(other);
                }

                _chunk & operator=(_chunk && other)
                {
                    _chunk tmp;
                    tmp.swap(other);
                    this->swap(tmp);
                    return *this;
                }

                ~_chunk()
                {
                    if (handle)
                    {
                        platform::unmap(*handle);
                    }
                }

                void swap(_chunk & other)
                {
                    begin = other.begin;
                    end = other.end;
                    size = other.size;
                    std::swap(handle, other.handle);
                    std::swap(descriptor, other.descriptor);
                }

                std::uintptr_t begin;
                std::uintptr_t end;
                std::size_t size;
                boost::optional<platform::memory_allocation_handle> handle;
                unique_ptr<_chunk_descriptor> descriptor;
                unique_ptr<_chunk> next;
            };

            _chunk_descriptor * _allocate_chunk(bool use_reserve = false)
            {
                unique_ptr<_chunk> chunk;
                unique_ptr<_chunk_descriptor> descriptor;

                if (use_reserve)
                {
                    platform::heap_assert(!_reserve_mutex.try_lock(), "tried to use use_reserve descriptors without locking _reserve_mutex!");

                    chunk = std::move(_reserve_chunk);
                    descriptor = std::move(_reserve_descriptor);
                }

                else
                {
                    descriptor = make_unique<_chunk_descriptor>();
                    chunk = make_unique<_chunk>();
                }

                auto area = platform::map(platform::chunk_size);

                chunk->begin = area.address;
                chunk->end = area.address + platform::chunk_size;
                chunk->size = platform::chunk_size;
                chunk->handle = area.handle;

                chunk->descriptor = std::move(descriptor);
                assert(chunk->descriptor);
                auto desc = chunk->descriptor.get();
                desc->chunk_size = chunk->size - sizeof(_chunk_header);
                desc->header = new (reinterpret_cast<void *>(chunk->begin)) _chunk_header{ _magic, desc };

                std::unique_lock<platform::unique_lock> lock{ _heap_chunks_lock };
                chunk->next = std::move(_heap_chunks);
                _heap_chunks = std::move(chunk);

                return desc;
            }

            _chunk_descriptor * _split(_chunk_descriptor * chunk)
            {
                platform::heap_assert(chunk->state == _chunk_state::free, "trying to split a non-free chunk");

                if (chunk->bin)
                {
                    std::lock_guard<platform::lock> lock{ chunk->bin->lock };
                    if (chunk == chunk->bin->first)
                    {
                        chunk->bin->first = chunk->next;
                    }
                    if (chunk->next)
                    {
                        chunk->next->prev = chunk->prev;
                    }
                    if (chunk->prev)
                    {
                        chunk->prev->next = chunk->next;
                    }

                    chunk->bin = nullptr;
                    chunk->prev = nullptr;
                    chunk->next = nullptr;
                }

                chunk->state = _chunk_state::divided;
                chunk->left_child = make_unique<_chunk_descriptor>().release();
                chunk->left_child->parent = chunk;
                chunk->left_child->chunk_size = (chunk->chunk_size + sizeof(_chunk_header)) / 2 - sizeof(_chunk_header);
                chunk->left_child->header = chunk->header;

                chunk->right_child = make_unique<_chunk_descriptor>().release();
                chunk->right_child->parent = chunk;
                chunk->right_child->chunk_size = (chunk->chunk_size + sizeof(_chunk_header)) / 2 - sizeof(_chunk_header);
                chunk->right_child->header = new (reinterpret_cast<void *>(reinterpret_cast<std::uintptr_t>(chunk->header) + chunk->left_child->chunk_size))
                    _chunk_header{ _magic, chunk->right_child };

                chunk->header->chunk = chunk->right_child;
                chunk->header = nullptr;

                _save(chunk->right_child);

                chunk->lock.unlock();
                chunk->left_child->lock.lock();

                chunk->state = _chunk_state::divided;

                return chunk->left_child;
            }

            void _save(_chunk_descriptor * chunk)
            {
                auto bin = _get_bin(chunk->chunk_size);
                std::unique_lock<platform::lock> lock{ bin->lock };
                chunk->prev = nullptr;
                chunk->next = bin->first;
                bin->first = chunk;
                chunk->bin = bin;
            }

        public:
            // the following function is kinda generic
            // but not really at all
            template<typename T, typename std::enable_if<std::is_same<T, _chunk_descriptor>::value || std::is_same<T, _chunk>::value, int>::type = 0>
            unique_ptr<T> make_unique()
            {
                if (_entered)
                {
                    {
                        std::lock_guard<platform::unique_lock> lock{ _reserve_mutex };

                        auto old = _microheaps;
                        _microheaps = _allocate_microheap(true);
                        _microheaps->next = old;

                        _entered = false;

                        if (!_reserve_chunk)
                        {
                            _reserve_chunk = make_unique<_chunk>();
                        }

                        if (!_reserve_descriptor)
                        {
                            _reserve_descriptor = make_unique<_chunk_descriptor>();
                        }
                    }

                    return make_unique<T>();
                }

                _entered = true;
                auto ret = new (allocate(sizeof(T))) T();
                _entered = false;

                return { ret, deleter<T>{ this } };
            }

        private:
            static constexpr std::size_t _log2_ceil(std::size_t value)
            {
                std::size_t ret = -1;
                bool is_power = !(value & (value - 1));
                while (value)
                {
                    value >>= 1;
                    ++ret;
                }
                return ret + !is_power;
            }

            static std::size_t _log2_ceil_fast(std::size_t value)
            {
                bool is_power = !(value & (value - 1));
                return CHAR_BIT * sizeof(unsigned long long) - __builtin_clzll(value) - is_power;
            }

            static constexpr std::size_t _log2_512 = _log2_ceil(512);
            static constexpr std::size_t _log2_min_microheap_size = _log2_ceil(_min_microheap_size);
            static constexpr std::size_t _top_micro_bin = _log2_512 - _log2_min_microheap_size;

            static relaxed_constexpr std::size_t _size_to_microbin_index(std::size_t size)
            {
                // these are not valid allocations size for microallocate
                // but they need to be handled so that microheap chunks can be put into their proper bins
                // (microheap chunks are of the normal chunk size, which is usually going to be different
                // than minimal chunk size, which is the threshold for allocating a whole chunk for a single
                // allocation)
                if (size > platform::min_chunk_size)
                {
                    size = platform::min_chunk_size;
                }

                if (size < _min_microheap_size)
                {
                    size = _min_microheap_size;
                }
                else if (size >= 512)
                {
                    return _top_micro_bin;
                }

                return _log2_ceil(size) - _log2_min_microheap_size;
            }

            static std::size_t _size_to_microbin_index_fast(std::size_t size)
            {
                // these are not valid allocations size for microallocate
                // but they need to be handled so that microheap chunks can be put into their proper bins
                // (microheap chunks are of the normal chunk size, which is usually going to be different
                // than minimal chunk size, which is the threshold for allocating a whole chunk for a single
                // allocation)
                if (size > platform::min_chunk_size)
                {
                    size = platform::min_chunk_size;
                }

                if (size < _min_microheap_size)
                {
                    size = _min_microheap_size;
                }
                else if (size >= 512)
                {
                    return _top_micro_bin;
                }

                return _log2_ceil_fast(size) - _log2_min_microheap_size;
            }

            enum class _micro_chunk_state : std::size_t
            {
                free,
                allocated
            };

            struct _chunk_microheap;

            struct alignas(16) _micro_chunk_header
            {
                std::uint64_t magic = _micro_magic;
                std::size_t size = 0;
                _chunk_microheap * microheap = nullptr;
                _micro_chunk_header * next = nullptr;
                _micro_chunk_state state = _micro_chunk_state::free;
            };

            void _assert_magic(const _micro_chunk_header * mh, std::size_t total) const
            {
                while (total)
                {
                    platform::heap_assert(mh->magic == _micro_magic, "invalid magic in microheap header");
                    total -= mh->size;
                    total -= sizeof(_micro_chunk_header);

                    mh = reinterpret_cast<_micro_chunk_header *>(reinterpret_cast<std::uintptr_t>(mh + 1) + mh->size);
                }
            }

            struct alignas(16) _chunk_microheap : _chunk_header
            {
                _chunk_microheap * next = nullptr;
                platform::lock lock;
                std::array<_micro_chunk_header *, _size_to_microbin_index(512) + 1> _micro_bins{ { nullptr } };
            };

            _chunk_microheap * _allocate_microheap(bool use_reserve = false)
            {
                auto chunk = _allocate_chunk(use_reserve);
                auto microheap = new (chunk->header) _chunk_microheap{};
                microheap->chunk = chunk;
                chunk->allocation_size = chunk->chunk_size - sizeof(_chunk_microheap);
                chunk->state = _chunk_state::micro_managed;
                size_t usable_space = chunk->allocation_size - sizeof(_micro_chunk_header);

                auto header = new (microheap + 1) _micro_chunk_header;
                header->size = usable_space;
                header->microheap = microheap;

                microheap->_micro_bins[_size_to_microbin_index_fast(usable_space)] = header;

                return microheap;
            }

            void * _microallocate(std::size_t size)
            {
                _chunk_microheap * microheap = nullptr;

                {
                    std::lock_guard<platform::unique_lock> lock{ _microheaps_lock };
                    microheap = _microheaps;
                    if (microheap)
                    {
                        if (_entered)
                        {
                            microheap->lock.lock();
                        }

                        else while (microheap && !microheap->lock.try_lock())
                        {
                            microheap = microheap->next;
                        }
                    }
                }

                while (microheap)
                {
                    for (auto bin = _size_to_microbin_index_fast(size); bin != microheap->_micro_bins.size(); ++bin)
                    {
                        if (microheap->_micro_bins[bin])
                        {
                            auto fragment = microheap->_micro_bins[bin];
                            if (fragment->size < size)
                            {
                                continue;
                            }
                            microheap->_micro_bins[bin] = fragment->next;

                            assert(fragment->state == _micro_chunk_state::free);

                            if (fragment->size > sizeof(_micro_chunk_header) + size + 32)
                            {
                                auto next_addr = reinterpret_cast<uintptr_t>(fragment) + sizeof(_micro_chunk_header) + size;
                                auto next = new (reinterpret_cast<void *>(next_addr)) _micro_chunk_header{};
                                next->microheap = fragment->microheap;
                                next->size = fragment->size - sizeof(_micro_chunk_header) - size;

                                auto & bin = next->microheap->_micro_bins[_size_to_microbin_index_fast(next->size)];
                                next->next = bin;
                                bin = next;

                                fragment->size = size;
                            }

                            fragment->state = _micro_chunk_state::allocated;

                            microheap->lock.unlock();

                            return reinterpret_cast<void *>(fragment + 1);
                        }
                    }

                    auto next = microheap->next;
                    if (next)
                    {
                        if (_entered)
                        {
                            next->lock.lock();
                        }

                        else while (next && !next->lock.try_lock())
                        {
                            next = next->next;
                        }
                    }

                    microheap->lock.unlock();
                    microheap = next;
                }

                microheap = _allocate_microheap();
                {
                    std::lock_guard<platform::unique_lock> lock{ _microheaps_lock };
                    microheap->next = _microheaps;
                    _microheaps = microheap;
                }

                return _microallocate(size);
            }

            _chunk_descriptor _bootstrap;
            _chunk _chunk_bootstrap;
            unique_ptr<_chunk_descriptor> _reserve_descriptor{ &_bootstrap, deleter<_chunk_descriptor>{ nullptr } };
            unique_ptr<_chunk> _reserve_chunk{ &_chunk_bootstrap, deleter<_chunk>{ nullptr } };
            platform::unique_lock _reserve_mutex;
            tls_variable<bool> _entered;

            unique_ptr<_chunk> _heap_chunks;
            mutable platform::unique_lock _heap_chunks_lock;
            _chunk_microheap * _microheaps = nullptr;
            mutable platform::unique_lock _microheaps_lock;

            static constexpr std::size_t _log2_min_chunk_size = _log2_ceil(platform::min_chunk_size);

            static relaxed_constexpr std::size_t _size_to_bin_index(std::size_t size)
            {
                assert(size >= platform::min_chunk_size && size <= platform::chunk_size);
                return _log2_ceil(size) - _log2_min_chunk_size;
            }

            static std::size_t _size_to_bin_index_fast(std::size_t size)
            {
                assert(size >= platform::min_chunk_size && size <= platform::chunk_size);
                return _log2_ceil_fast(size) - _log2_min_chunk_size;
            }

            _bin * _get_bin(std::size_t size)
            {
                if (size > platform::chunk_size)
                {
                    return nullptr;
                }

                return &_bins[_size_to_bin_index_fast(size + sizeof(_chunk_header))];
            }

            std::array<_bin, _size_to_bin_index(platform::chunk_size) + 1> _bins;
        };

        using heap = heap_<void>;

        template<typename T>
        class ralloc_allocator
        {
        public:
            template<typename U>
            friend class ralloc_allocator;

            using heap_type = heap;

            template<typename U>
            struct rebind
            {
                using other = ralloc_allocator<U>;
            };

            using value_type = T;

            ralloc_allocator(heap_type * heap) : _heap{ heap }
            {
            }

            ralloc_allocator(const ralloc_allocator &) = default;
            ralloc_allocator(ralloc_allocator &&) = default;

            template<typename U>
            ralloc_allocator(const ralloc_allocator<U> & other) : _heap{ other._heap }
            {
            }

            T * allocate(std::size_t n, const void *)
            {
                return reinterpret_cast<T*>(_heap->allocate(sizeof(T) * n));
            }

            void deallocate(T * ptr, std::size_t)
            {
                _heap->free(ptr);
            }

        private:
            heap_type * _heap;
        };
    }}
}

