#include <thread>
#include <chrono>

#include "ralloc/heap.h"

struct big_struct
{
    std::size_t big_data[12 * 1024] = {};
};

int main(int argc, char ** argv)
{
    srand(time(0));

    if (argc == 2)
    {
        auto start = std::chrono::high_resolution_clock::now();

        auto g = []()
        {
            for (auto i = 0ull; i < 10000ull; ++i)
            {
                //malloc(sizeof(big_struct));
                malloc(rand() % (8 * 1024));
            }
        };

        std::thread t1{ g };
        std::thread t2{ g };
        std::thread t3{ g };
        std::thread t4{ g };

        t1.join();
        t2.join();
        t3.join();
        t4.join();

        auto time = std::chrono::high_resolution_clock::now() - start;
        std::cout << std::chrono::duration_cast<std::chrono::milliseconds>(time).count() << std::endl;

        return 0;
    }

    auto start = std::chrono::high_resolution_clock::now();

    reaver::ralloc::heap h;
    auto f = [&]()
    {
        for (auto i = 0ull; i < 10000ull; ++i)
        {
            //h.make_unique<big_struct>().release();
            h.allocate(rand() % (8 * 1024));
        }
    };

    std::thread t1{ f };
    std::thread t2{ f };
    std::thread t3{ f };
    std::thread t4{ f };

    t1.join();
    t2.join();
    t3.join();
    t4.join();

    auto time = std::chrono::high_resolution_clock::now() - start;
    std::cout << std::chrono::duration_cast<std::chrono::milliseconds>(time).count() << std::endl;

    h.assert_magics();

    exit(0);
}
