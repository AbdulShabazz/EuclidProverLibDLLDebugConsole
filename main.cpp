
#include <iostream>
#include <thread>
#include <atomic>
#include <cstdint>
#include <cstdlib>
#include <array>
#include <chrono>
#include <vector>
#include <deque>
#include <string>
#include <unordered_map>
#include "../boost/multiprecision/cpp_int.hpp"

int main()
{
    const auto start_time_chrono = std::chrono::high_resolution_clock::now();

	cpp_int PrimeComposite = 4; 
	cpp_int PrimeComposite2 = 2; 
	cpp_int PrimeComposite3 = 16;
	cpp_int PrimeComposite_Result;

	if (PrimeComposite % PrimeComposite2 == 0)
	{
		PrimeComposite_Result = PrimeComposite / PrimeComposite2 * PrimeComposite3;
	}

	const auto end_time_chrono = std::chrono::high_resolution_clock::now();
	const auto duration_chrono = std::chrono::duration_cast<std::chrono::nanoseconds>(end_time_chrono - start_time_chrono).count();
	std::cout << "Total Duration (nanoseconds): " << duration_chrono << std::endl;

    return EXIT_SUCCESS;
}
