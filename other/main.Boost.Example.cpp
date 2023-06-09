
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
#include <_boost/multiprecision/cpp_int.hpp>

int main()
{
	const auto start_time_chrono = std::chrono::high_resolution_clock::now();

	boost::multiprecision::cpp_int PrimeComposite = 12345678901234567890;
	boost::multiprecision::cpp_int PrimeComposite2 = 12345678901234567890;
	boost::multiprecision::cpp_int PrimeComposite3 = 12345678901234567890;
	boost::multiprecision::cpp_int PrimeComposite_Result;

	++PrimeComposite2;
	PrimeComposite2--;
	PrimeComposite2++;
	--PrimeComposite2;

	PrimeComposite_Result = PrimeComposite2 + PrimeComposite3 - PrimeComposite3;

	PrimeComposite_Result += PrimeComposite2;

	PrimeComposite_Result -= PrimeComposite2;

	PrimeComposite_Result *= PrimeComposite2;

	std::cout << "PrimeComposite_Result (BigInt): " << PrimeComposite_Result << std::endl;

	PrimeComposite_Result /= PrimeComposite2;

	if (PrimeComposite % PrimeComposite2 == 0)
	{
		PrimeComposite_Result = PrimeComposite / PrimeComposite2 * PrimeComposite3;
	}

	const auto end_time_chrono = std::chrono::high_resolution_clock::now();
	const auto duration_chrono = std::chrono::duration_cast<std::chrono::nanoseconds>(end_time_chrono - start_time_chrono).count();
	
	std::cout << "PrimeComposite_Result (BigInt): " << PrimeComposite_Result << std::endl;
	std::cout << "Total Duration (nanoseconds): " << duration_chrono << std::endl;

	return EXIT_SUCCESS;
}
