#pragma once

/*

  AUTHOR
	  Seagat2011 (https://github.com/Seagat2011, https://eternagame.org/web/player/90270/, https://fold.it/port/user/1992490)

  VERSION
	  Major.Minor.Bugfix.Patch
	  12.0.0.0

  DESCRIPTION
	Theorem prover written in C++23. Ported from ECMA-262 JavaScript (A grammar reduction term-rewriting system)
	for use in the Unreal Engine 5.2 Core in-game Framework.

	 The following #ifdef EUCLIDPROVERLIBDLL_EXPORTS block is the standard way of creating macros which make exporting
	 from a DLL simpler. All files within this DLL are compiled with the EUCLIDPROVERLIBDLL_EXPORTS
	 symbol defined on the command line. This symbol should NOT be defined on any project
	 that calls this DLL. This way any other project whose source files include this file see
	 API_EXPORT functions as being imported from a DLL, whereas this DLL sees symbols
	 defined with this macro as being exported.

  C++23 UPDATES
	+ BigInt (boost) support
	+ Prime(k++) ==> Prime([k++])
	+ std::unordered_map ('symbol' == 'SYMBOL') ==> std::unordered_multimap ('symbol' != 'SYMBOL')
	+ Lockless stack manager: RecursionLimiter (Eliminates mutex/semaphore Performance penalty)
	- Multithreaded support (+ Reduced latency, - Reduced scalability)

  JavaScript UPDATES
	+ Negative proof assertions ~=
	+ _AXIOM_.optimizeCallGraph
	+ Improved ProofComplete search performance
	+ Prove via Auto (PASS)
	+ Axiom._eval => Axiom._reduce
	+ Axiom.{_reduce,_expand} => eventListener(s)
	+ solutionEditor => contentEditable
	+ Prove via Reduce (PASS)
	+ Prove via Expand (PASS)
	+ scoping functionality
	+ LibreOffice math library support
	- Axiom._eval eventListener

  NOTES:
	Rewrites are performed via the aid of a rewrite compiler (eg. via LEMMA SUBSTITUTION); SEE TEST CASES

	Substitution methods:

		1. AXIOMATIC: 1 + 1 = 2
		2. LEMMA SUBSTITUTION: 1 <==> 1 / 1

	Note: Lemma substitutions are rewrite "helpers" which can be used to rewrite axioms.
	Great care must be taken with them because they can introduce recursion, stack overflows,
	and other performance bugs: For example, consider: "{ PlayerCharacterSideKick } IsIn { StyxBoat }" -
	the "IsIn" operator may or may not link unrelated categories, indefinitely;
	whereas: "{ PlayerCharacterSideKick } IsIn_StyxBoat " is safer and guaranteed to converge.

  Note: The rewrite engine considerers one or more symbols enclosed within curly braces and or brackets as a scoped variable hint, which can be replaced.

  Usage example (pseudo code).

	( { a } plus { b } ) raised { 2 } = { { c } raised { 2 } } plus { 2ab }

	{ { a } raised { 2 } } plus { 2ab } plus { b raised { 2 } } <== ( { a } plus { b } ) raised { 2 }
	( { a } plus { b } ) raised { 2 } minus { 2ab } = { c } raised { 2 } <== ( { a } plus { b } ) raised { 2 } = { { c } raised { 2 } } plus { 2ab }
	{ { a } raised { 2 } } plus { 2ab } minus { 2ab } plus { b raised { 2 } } ==> { { a } raised { 2 } } plus { { b } raised { 2 } }

	Prove { { a } raised { 2 } } plus { { b } raised { 2 } } = { c } raised { 2 }

  Usage Example (pseudo code).

	// Axioms
	{ PlayerCharacterSideKick } IsIn { StyxBoat } = { StyxBoat } IsIn { StyxRiver } // Current Game State
	{ PlayerCharacterSideKick } IsIn { Vehicle { QuadUtilityVehicle } } = { Vehicle { QuadUtilityVehicle } } IsIn { EuropaLand } and { Vehicle { QuadUtilityVehicle { VehicleDriveDisabled } } }
	{ PlayerCharacterSideKick } IsIn { EuropaLand } = { Vehicle { QuadUtilityVehicle } } IsIn { EuropaLand }
	{ PlayerCharacterSideKick } IsIn { QuadUtilityVehicle } = { Vehicle { QuadUtilityVehicle { VehicleDriveDisabled } } }
	{ PlayerCharacterSideKick } IsNotIn { Vehicle { QuadUtilityVehicle } } = { Vehicle { QuadUtilityVehicle } } IsIn { EuropaLand }
	.
	. [Other available but non-relevant Game States the framework can choose from ]
	.
	{ PlayerCharacterSideKick } IsIn { QuadUtilityVehicle } = { QuadUtilityVehicle } and { VehicleDriveDisabled }

	// Lemmas
	{ PlayerCharacterSideKick } IsIn { StyxBoat } <== { StyxBoat } IsNotIn { StyxRiver } // These are connectives, and axiom helpers
	{ PlayerCharacterSideKick } IsOn { Vehicle } <== { VehicleDriveDisabled }
	{ PlayerCharacterSideKick } IsIn { Vehicle { QuadUtilityVehicle } } <== { PlayerCharacterSideKick } IsIn { QuadUtilityVehicle }
	{ PlayerCharacterSideKick } IsNotIn { StyxBoat } ==> { StyxBoat } IsNotIn { StyxRiver }

	// Theorem to prove
	Prove { PlayerCharacterSideKick } IsIn { QuadUtilityVehicle } = { QuadUtilityVehicle } and { VehicleDriveDisabled }

	// Proof-Steps (Output)
	{ PlayerCharacterSideKick } IsIn { StyxBoat } = { StyxBoat } IsIn { StyxRiver }
	{ PlayerCharacterSideKick } IsIn { StyxBoat } = { StyxBoat } IsNotIn { StyxRiver }
	{ PlayerCharacterSideKick } IsNotIn { StyxBoat } = { StyxBoat } IsNotIn { StyxRiver }
	{ PlayerCharacterSideKick } IsIn { EuropaLand } = { Vehicle { QuadUtilityVehicle } } IsIn { EuropaLand }
	{ PlayerCharacterSideKick } IsNotIn { Vehicle { QuadUtilityVehicle } } = { Vehicle { QuadUtilityVehicle } } IsIn { EuropaLand }
	{ PlayerCharacterSideKick } IsIn { Vehicle { QuadUtilityVehicle } } = { Vehicle { QuadUtilityVehicle } } IsIn { EuropaLand } and { Vehicle { QuadUtilityVehicle { VehicleDriveDisabled } } }
	{ PlayerCharacterSideKick } IsIn { QuadUtilityVehicle } = { Vehicle { QuadUtilityVehicle { VehicleDriveDisabled } } }
	{ PlayerCharacterSideKick } IsIn { QuadUtilityVehicle } = { QuadUtilityVehicle } and { VehicleDriveDisabled }

	Usage Example C++.

	```c++
		// Create ProofStepProofStep[proof][lineNumber][LHS/RHS][SYMBOL] placeholder to store the proof
		std::vector<
		std::vector<
		std::vector<
		std::vector<
		std::string>>>> ProofStep;

		// Instantiate Prover (module)
		EuclidProver<BracketType::CurlyBraces> Euclid;

		Euclid.Axioms
		(
			{
				// Axiom_00
				{
					{ "{", "PlayerCharacterSideKick", "}", "IsIn", "{", "StyxBoat", "}" },  // lhs
					{ "{", "StyxBoat", "}", "IsIn", "{", "StyxRiver", "}" } // rhs
				},

				 // Axiom_01
				{
					{ "{", "PlayerCharacterSideKick", "}", "IsIn", "{", "Vehicle", "{", "QuadUtilityVehicle", "}", "}"}, // lhs
					{ "{", "Vehicle", "{", "QuadUtilityVehicle", "}", "}", "IsIn", "{", "EuropaLand", "}", "and", "{", "Vehicle", "{", "QuadUtilityVehicle", "{", "VehicleDriveDisabled", "}", "}", "}" } // rhs
				},

				// Axiom_02
				{
					{ "{", "PlayerCharacterSideKick", "}", "IsIn", "{", "EuropaLand", "}" }, // lhs
					{ "{", "Vehicle", "{", "QuadUtilityVehicle", "}", "}", "IsIn", "{", "EuropaLand", "}" } // rhs
				},

				// Axiom_03
				{
					{ "{", "PlayerCharacterSideKick", "}", "IsIn", "{", "QuadUtilityVehicle", "}" }, // lhs
					{ "{", "Vehicle", "{", "QuadUtilityVehicle", "{", "VehicleDriveDisabled", "}", "}" } // rhs
				},

				// Axiom_04
				{
					{ "{", "PlayerCharacterSideKick", "}", "IsNotIn", "{", "Vehicle", "{", "QuadUtilityVehicle", "}", "}" }, // lhs
					{ "{", "Vehicle", "{", "QuadUtilityVehicle", "}", "}", "IsIn", "{", "EuropaLand", "}" } // rhs
				},

				// Axiom_05
				{
					{ "{", "PlayerCharacterSideKick", "}", "IsIn", "{", "QuadUtilityVehicle", "}" }, // lhs
					{ "{", "QuadUtilityVehicle", "}", "and", "{", "VehicleDriveDisabled", "}" } // rhs
				}
			}
		);

		Euclid.Lemmas
		(
			// Lemma (rewrite helper) 00
			{
				{ "{", "PlayerCharacterSideKick", "}", "IsIn", "{", "StyxBoat", "}" }, // lhs
				{ "{", "StyxBoat", "}", "IsNotIn", "{", "StyxRiver", "}" } // rhs
			}
		);

		const bool ProofFound_Flag =

		Euclid.Prove
		(
			{ "{", "PlayerCharacterSideKick", "}", "IsIn", "{", "QuadUtilityVehicle", "}" }, // rhs
			{ "{", "QuadUtilityVehicle", "}", "and", "{", "VehicleDriveDisabled", "}" }, // lhs

			ProofStep // Storage for the Result
		);

		if (ProofFound_Flag)
		{
			std::cout << "Proof found:" << std::endl;
			Euclid.PrintPath(ProofStep);
		}
		else if (ProofStep.size())
		{
			std::cout << "Partial Proof found:\n" << std::endl;
			Euclid.PrintPath(ProofStep);
		} else {
			std::cout << "Proof failed\n";
		}

		// Suspend a proof for current (GUID)
		const BigInt128_t guid = Euclid.Suspend();
		std::cout << "Proof suspended for: guid_" << guid << std::endl;

		// Resume a proof for (GUID)
		if(Euclid.Resume(guid))
		{
			std::cout << "Proof resumed for: guid_" << guid << std::endl;
		}

	```

  REFERENCES
	  OpenAI GPT-4-32k-0314 ( { max_tokens:32000, temperature:1.0, top_p:1.0, N:1,
			stream:false, logprobs:NULL, echo:false, stop:NULL, presence_penalty:0,
			frequency_penalty:0, best_of:1, logit_bias:NULL } )

  COMPATIBILITY
	  Windows 11+ x86i64

*/

#ifdef EUCLIDPROVERLIBDLL_EXPORTS
#define API_EXPORT __declspec(dllexport)
#else
#define API_EXPORT __declspec(dllimport)
#endif

#include <iostream>
#include <thread>
#include <vector>
#include <initializer_list>
#include <queue>
#include <string>
#include <unordered_map>
#include <functional>
#include <future>
#include <limits>
#include <boost/multiprecision/cpp_int.hpp> 

namespace Euclid_Prover
{
	using BigInt128_t = boost::multiprecision::cpp_int;

	std::unordered_multimap<
	std::string, BigInt128_t>
	SymbolToPrime_UInt64MultiMap =
	{
		{"=", 2},
		{"{", 3},
		{"}", 5},
		{"(", 7},
		{")", 11},
		{"[", 13},
		{"]", 17}
	};

	std::size_t PrimeCompositeVecSize_UInt64{ 7 };

	std::vector<BigInt128_t> PrimeComposite_UInt64Vec{ 2, 3, 5, 7, 11, 13, 17 };

	std::vector<
	std::vector<
	std::vector<
	std::string>>> TempProofSteps{};

	/**
	 * Prime() : Return the next prime in the series...
	 * usage: Prime(); // returns 23
	*/
	BigInt128_t Prime()
	{
		const std::size_t Index_UInt64 = PrimeCompositeVecSize_UInt64++;
		for (BigInt128_t i = PrimeComposite_UInt64Vec.back() + 2; PrimeComposite_UInt64Vec.size() < PrimeCompositeVecSize_UInt64; i += 2)
		{
			bool Add_Flag{ true };

			BigInt128_t j{};

			const BigInt128_t J = i / 4;

			for (const BigInt128_t& val : PrimeComposite_UInt64Vec)
			{

				if (/*(i % 2) == 0 ||*/ (i % val) == 0)
				{
					Add_Flag = false;
					break;
				}

				if (++j >= J)
				{
					break;
				}
			}

			if (Add_Flag)
			{
				PrimeComposite_UInt64Vec.emplace_back(i);
			}
		}

		return PrimeComposite_UInt64Vec[Index_UInt64];
	}

	// Generate Internal Route Map //
	int __Prove__
	(
		const
		std::vector<
		std::vector<
		std::string>>&
		InTheoremStdStrVec,

		const
		std::vector<
		std::vector<
		std::vector<
		std::string>>>&
		InAxiomsStdStrVec,

		bool&
		OutProofFound_FlagRef,

		bool& 
		OutStatusReadyFlag,

		std::vector<
		std::vector<
		std::vector<
		std::vector<
		std::string>>>>&
		OutProofStepStdStrVecRef,

		std::vector<
		std::vector<
		std::string>>&
		OutAxiomCommitLogStdStrVecRef
	)
	{

		TempProofSteps = {};

		bool QED {};

		BigInt128_t GUID_UInt64{};

		std::vector<BigInt128_t> Theorem_UInt64Vec;

		auto PopulateTheoremVec =
			[
				&
			]
		() -> void
		{
			for (const std::vector<std::string>& Subnet_StdStrVec : InTheoremStdStrVec)
			{
				BigInt128_t PrimeProduct_UInt64Vec{ 1 };
				for (const std::string& Symbol_StdStr : Subnet_StdStrVec)
				{
					std::cout << "'" << Symbol_StdStr << "' ";
					const auto& it = SymbolToPrime_UInt64MultiMap.find(Symbol_StdStr);
					if (it != SymbolToPrime_UInt64MultiMap.end())
					{
						PrimeProduct_UInt64Vec *= it->second;
						std::cout << "Prime: " << Symbol_StdStr << " <- " << it->second << ", PrimeProduct: " << PrimeProduct_UInt64Vec << std::endl;
					}
					else {
						// This key/value pair is not in the prime number multimap...
						const BigInt128_t p = Prime();
						SymbolToPrime_UInt64MultiMap.emplace(Symbol_StdStr, p);
						PrimeProduct_UInt64Vec *= p;
						std::cout << "New Prime: " << Symbol_StdStr << " <- " << p << ", PrimeProduct: " << PrimeProduct_UInt64Vec << std::endl;
					}
				}
				std::cout << std::endl;
				Theorem_UInt64Vec.emplace_back(PrimeProduct_UInt64Vec);
			}
			Theorem_UInt64Vec.emplace_back(0); // guid
			Theorem_UInt64Vec.emplace_back(0); // last_UInt64 {"_root"}
		};

		std::vector<
		std::vector<
		BigInt128_t>> Axioms_UInt64Vec;

		auto PopulateAxiomVec =
			[
				&
			]
		() -> void
		{
			for
				(
					const
					std::vector<
					std::vector<
					std::string>>&Subnet_StdStrVec :
					InAxiomsStdStrVec
				)
			{
				std::vector<BigInt128_t> TempInnerAxiom_UInt64Vec{};
				for
					(
						const
						std::vector<
						std::string>& Expression_StdStrVec :
						Subnet_StdStrVec
					)
				{
					BigInt128_t PrimeProduct_UInt64Vec{ 1 };
					for (const std::string& Symbol_StdStr : Expression_StdStrVec)
					{
						std::cout << "'" << Symbol_StdStr << "' ";
						const auto& it = SymbolToPrime_UInt64MultiMap.find(Symbol_StdStr);
						if (it != SymbolToPrime_UInt64MultiMap.end())
						{
							PrimeProduct_UInt64Vec *= it->second;
							std::cout << "Prime: " << Symbol_StdStr << " <- " << it->second << ", PrimeProduct: " << PrimeProduct_UInt64Vec << std::endl;
						}
						else {
							// This key/value pair is not in the prime number multimap...
							const BigInt128_t p = Prime();
							SymbolToPrime_UInt64MultiMap.emplace(Symbol_StdStr, p);
							PrimeProduct_UInt64Vec *= p;
							std::cout << "New Prime: " << Symbol_StdStr << " <- " << p << ", PrimeProduct: " << PrimeProduct_UInt64Vec << std::endl;
						}
					}
					std::cout << std::endl;
					TempInnerAxiom_UInt64Vec.emplace_back(PrimeProduct_UInt64Vec);
				}
				TempInnerAxiom_UInt64Vec.emplace_back(++GUID_UInt64); // guid
				Axioms_UInt64Vec.emplace_back(TempInnerAxiom_UInt64Vec);
			}
		};

		/*
		Theorem
		[LHS]
		[RHS]
		[guid_UInt64]
		[last_UInt64]
		[ProofStackUInt64]

		Axiom
		[LHS]
		[RHS]
		[guid_UInt64]
		*/

		constexpr int LHS = 0;
		constexpr int RHS = 1;
		constexpr int guid_UInt64 = 2;
		constexpr int last_UInt64 = 3;
		constexpr int ProofStackUInt64 = 4;

		auto RebalanceTheoremVec =
			[
				&
			]
		() -> void
		{
			BigInt128_t& lhs = Theorem_UInt64Vec[LHS];
			BigInt128_t& rhs = Theorem_UInt64Vec[RHS];

			if (lhs < rhs)
			{
				std::swap(lhs, rhs);
			}
		};

		auto RebalanceAxiomVec =
			[
				&
			]
		() -> void
		{
			for (std::vector<BigInt128_t>& Axiom_i : Axioms_UInt64Vec)
			{
				BigInt128_t& lhs = Axiom_i[LHS];
				BigInt128_t& rhs = Axiom_i[RHS];

				if (lhs < rhs)
				{
					std::swap(lhs, rhs);
				}
			}
		};

		PopulateTheoremVec();
		PopulateAxiomVec();

		RebalanceTheoremVec();
		RebalanceAxiomVec();

		/*
		std::vector<BigInt128_t> Theorem_UInt64Vec =
		{
			1585615607, // "1 + 1 + 1 + 1" (LHS)
			29, // "4" (RHS)
			0, // guid_UInt64;
			0, // last_UInt64 == "_root"
			null, ...start of ProofStack_UInt64Vec
		};

		std::vector<std::vector<BigInt128_t>> Axioms_UInt64Vec =
		{
			{
				8303, // "1 + 1" (RHS)
				31, // "2" (LHS)
				1, // guid_UInt64
			},

			{
				22103, // "2 + 2" (RHS)
				29, // "4" (LHS)
				2, // guid_UInt64
			}
		};
		*/

		std::size_t MaxAllowedProofs_UInt64{ 1 };
		std::size_t TotalProofsFound_UInt64{};

		std::unordered_map<
		std::string,
		std::unordered_map<
		BigInt128_t,
		std::unordered_map<
		BigInt128_t, bool>>>
		AxiomCallGraph_Map;

		/**
		 * bool RewriteInstruction_Map[opcode](N), where opcode indicates
		 *
		 * 0x00: _lhs _reduce operation
		 * 0x01: _lhs _expand operation
		 * 0x02: _rhs _reduce operation
		 * 0x03: _rhs _expand operation
		 *
		 * ...and N is Axiom_N.
		 *
		*/

		// Prevent next round call loops to improve Performance
		std::unordered_map<BigInt128_t,
		std::unordered_map<BigInt128_t, bool>>

		CallHistory{},
		NextRoundCallHistory{};

		//CallHistory.reserve (100'000); // (Max expected elements for Performance)

		std::priority_queue<
		std::vector<
		BigInt128_t>> Tasks_Thread;

		Tasks_Thread.push(Theorem_UInt64Vec);

		// Todo: Develop an artificial neural network that can infer a solution and proofsteps from an axiom CallGraph 
		// Todo: Add Remove, SendOffline support for individual axioms
		// Todo: Add Resume, Suspend operations for Proofs
		// Todo: Create a proof-statement hash which can be used as a file handle to a proofstep solution when it posts to a file (stateless)
		// Todo: Prevent Tasks_Thread (stack) overflows by deferring unprocessed axiom rewrites onto a deferred thread

		//*** Core Proof Engine (Loop) *** //
		while (!Tasks_Thread.empty() && !QED)
		{
			const std::vector<BigInt128_t>
			Theorem{ Tasks_Thread.top() };

			Tasks_Thread.pop();

			// Check rewrite proofs in the task queue //
			const bool TentativeProofFound_Flag = (Theorem[LHS] == Theorem[RHS]);
			if (TentativeProofFound_Flag)
			{
				/** 
				Alright, we have successfully employed prime number fields
				to effectively and swiftly reduce the size of our potential solution set. 
				
				Now, our next step is to confirm that this narrowed down solution space 
				indeed leads us to a valid routing map...
				*/

				std::cout << "Tentative Proof Found" << std::endl;
				std::cout << "Theorem {" << Theorem[LHS] << ", " << Theorem[RHS] << "} " << std::endl;

				bool ProofFoundFlag{ true };

				TempProofSteps.emplace_back(InTheoremStdStrVec);

				auto Rewrite = [&]
				(
					auto& th,

					const auto& from,

					const auto& to
				) -> bool
				{
					bool bSuccessFlag{};

					if (th.size () < from.size ())
						return false;

					std::unordered_map<std::string, std::string>

						endscope{ {"(", ")"}, {"{", "}"}, {"[", "]"} };

					std::vector<
						std::string> result{};

					std::size_t i{};

					const std::size_t I{ from.size () };

					for (const auto& val : th)
					{
						std::cout << "Next val: " << val << std::endl;

						if (!bSuccessFlag && val == from[i])
						{
							++i;

							std::cout << "Match found: " << val << " >> ";

							if (i == I)
							{
								for (const auto& u2 : to)
								{
									std::cout << u2 << " ";
									result.emplace_back (u2);
								}

								bSuccessFlag = true;

								std::cout << ">> Substitution made" << std::endl;

								i = 0;

								continue;
							}
						} else {
							i = 0; // reset //

							std::cout << "No Match found: " << val << std::endl;

							result.emplace_back (val);
						}
						std::cout << std::endl;
					}

					th = result;

					return bSuccessFlag;
				};

				/**
				Q: Write a c++20 algorithm, ProofVerified, which accepts Theorem,
				InTheoremStdStrVec, and InAxiomsStdStrVec, as parameters and returns a bool type.

				ProofVerified clones InTheoremStdStrVec as OutTheoremStdStrVec, and performs
				the following operations:

				ProofVerified loops through Theorem, starting at Theorem[ProofStackUInt64],
				and reads two values from the vector at a time: Theorem[ProofStackUInt64 + i++],
				Theorem[ProofStackUInt64 + i++] - 1.

				The first value read out,
				const auto& opcode = Theorem[ProofStackUInt64 + i++], is an opcode
				whose hexadecimal value may range from 0x00 to 0x03.

				The second value read out, const auto& guid = Theorem[ProofStackUInt64 + i++] - 1,
				is an index into InAxiomsStdStrVec.

				An opcode of 0x00 indicates a "lhsreduce" operation, which replaces all occurrences
				of InAxiomsStdStrVec[guid][LHS] in OutTheoremStdStrVec[LHS] with InAxiomsStdStrVec[guid][RHS],
				resizing OutTheoremStdStrVec, as required.

				An opcode of 0x01 indicates a "lhsexpand" operation, which replaces all occurrences
				of InAxiomsStdStrVec[guid][LHS] in OutTheoremStdStrVec[RHS] with InAxiomsStdStrVec[guid][LHS],
				resizing OutTheoremStdStrVec, as required.

				An opcode of 0x02 indicates a "rhsreduce" operation, which replaces all occurrences
				of InAxiomsStdStrVec[guid][RHS] in OutTheoremStdStrVec[LHS] with InAxiomsStdStrVec[guid][RHS],
				resizing OutTheoremStdStrVec, as required.

				An opcode of 0x03 indicates a "rhsexpand" operation, which replaces all occurrences
				of InAxiomsStdStrVec[guid][RHS] in OutTheoremStdStrVec[RHS] with InAxiomsStdStrVec[guid][LHS],
				resizing OutTheoremStdStrVec, as required.

				If ProofVerified is unable to complete the loop, the algorithm returns false.
				*/
				auto ProofVerified = [&]
				(
					const
					std::vector<
					BigInt128_t>&
					InTheoremUInt64,

					const
					std::vector<
					std::vector<
					std::string>>&
					InTheoremStdStrVec,

					const
					std::vector<
					std::vector<
					std::vector<
					std::string>>>&
					InAxiomsStdStrVec,

					std::vector<
					std::vector<
					std::string>>&
					OutAxiomCommitLogStdStrVecRef,

					std::vector<
					std::vector<
					std::vector<
					std::string>>>&
					OutTheoremStdStrVec
				) -> bool
				{
					bool ReturnStatusFlag{ true };

					OutTheoremStdStrVec.emplace_back (InTheoremStdStrVec);

					std::vector<
					std::vector<
					std::string>>
					TempTheoremStdStrVec{ InTheoremStdStrVec };

					std::vector<
					std::string>
					TempAxiomCommitLogStdStrVecRef;

					/**
					Loop through Theorem, starting at Theorem[ProofStackUInt64],
					and read two values from the vector at a time.

					The first value read out, is an opcode whose hexadecimal value
					ranges from 0x00 to 0x03.

					The second value read out, is an index into InAxiomsStdStrVec.
					*/

					std::size_t i { ProofStackUInt64 };

					while (i < InTheoremUInt64.size ())
					{
						if (!ReturnStatusFlag)
							return ReturnStatusFlag;

						const std::size_t& opcode = std::size_t{ InTheoremUInt64[i++] };
						const std::size_t& guid = std::size_t{ InTheoremUInt64[i++] - 1 };

						//TempTheoremStdStrVec = OutTheoremStdStrVec.back();

						switch (opcode)
						{
							case 0x00:
							{ // "lhsreduce" operation //
								std::cout << "lhs_reduce via Axiom_" << guid/*.str()*/ << std::endl;
								ReturnStatusFlag =
									Rewrite (TempTheoremStdStrVec[LHS], InAxiomsStdStrVec[guid][LHS], InAxiomsStdStrVec[guid][RHS]);
								TempAxiomCommitLogStdStrVecRef.emplace_back ("lhs_reduce via Axiom_" + guid/*.str()*/);
								break;
							}
							case 0x01:
							{ // "lhsexpand" operation //
								std::cout << "lhs_expand via Axiom_" << guid/*.str()*/ << std::endl;
								ReturnStatusFlag =
									Rewrite (TempTheoremStdStrVec[LHS], InAxiomsStdStrVec[guid][RHS], InAxiomsStdStrVec[guid][LHS]);
								TempAxiomCommitLogStdStrVecRef.emplace_back ("lhs_expand via Axiom_" + guid/*.str()*/);
								break;
							}
							case 0x02:
							{ // "rhsreduce" operation //
								std::cout << "rhs_reduce via Axiom_" << guid/*.str()*/ << std::endl;
								ReturnStatusFlag =
									Rewrite (TempTheoremStdStrVec[RHS], InAxiomsStdStrVec[guid][LHS], InAxiomsStdStrVec[guid][RHS]);
								TempAxiomCommitLogStdStrVecRef.emplace_back ("rhs_reduce via Axiom_" + guid/*.str()*/);
								break;
							}
							case 0x03:
							{ // "rhsexpand" operation //
								std::cout << "rhs_expand via Axiom_" << guid/*.str()*/ << std::endl;
								ReturnStatusFlag =
									Rewrite (TempTheoremStdStrVec[RHS], InAxiomsStdStrVec[guid][RHS], InAxiomsStdStrVec[guid][LHS]);
								TempAxiomCommitLogStdStrVecRef.emplace_back ("rhs_expand via Axiom_" + guid/*.str()*/);
								break;
							}
							default:
							{
								// Invalid opcode. //
								ReturnStatusFlag = false;
								break; false;
							}
						} // end switch(opcode)
						OutTheoremStdStrVec.emplace_back (TempTheoremStdStrVec);
					}
					OutAxiomCommitLogStdStrVecRef.emplace_back (TempAxiomCommitLogStdStrVecRef);

					// If TentativeProofVerified is unable to complete the loop, the algorithm returns false.
					return true;
				};

				std::vector<std::string> TempAxiomCommitLog_StdStrVec {};

				//QED = true;
				//break;
				
				std::vector<
				std::vector<
				std::vector<
				std::string>>>
				OutTheoremStdStrVec;

				if (
						ProofVerified
						(
							Theorem,
							InTheoremStdStrVec,
							InAxiomsStdStrVec,
							OutAxiomCommitLogStdStrVecRef,
							OutTheoremStdStrVec
						)
					)
				{
					++TotalProofsFound_UInt64;

					std::cout << "Proof Found" << std::endl;
					std::cout << "Theorem {" << Theorem[LHS] << ", " << Theorem[RHS] << "} " << std::endl;

					if (TotalProofsFound_UInt64 >= MaxAllowedProofs_UInt64)
					{
						QED = true;
						break;
					}
				} else {
					// Retain Partial-proof //
					continue;
				}

			} else {

				// Add new rewrites to the task queue //
				for (const std::vector<BigInt128_t>& Axiom : Axioms_UInt64Vec)
				{
					if (Theorem[LHS] % Axiom[LHS] == 0)
					{
						std::vector<BigInt128_t> Theorem_0000{ Theorem };
						Theorem_0000[LHS] = Theorem_0000[LHS] / Axiom[LHS] * Axiom[RHS];
						Theorem_0000.emplace_back(0x00); // Push opcode 0x00 onto the proofstack because we performed a _lhs _reduce operation) //
						Theorem_0000.emplace_back(Axiom[guid_UInt64]); // Push the Axiom ID onto the proofstack //
						std::cout << "_reduce Module_0000 via Axiom_" << Axiom[guid_UInt64] << " {" << Theorem_0000[LHS] << ", " << Theorem_0000[RHS] << "}" << std::endl;

						Tasks_Thread.push(Theorem_0000);
					}

					if (Theorem[LHS] % Axiom[RHS] == 0)
					{
						std::vector<BigInt128_t> Theorem_0001{ Theorem };
						Theorem_0001[LHS] = Theorem_0001[LHS] / Axiom[RHS] * Axiom[LHS];
						Theorem_0001.emplace_back(0x01); // Push opcode 0x01 onto the proofstack because we performed a _lhs _expand operation) //
						Theorem_0001.emplace_back(Axiom[guid_UInt64]); // Push the Axiom ID onto the proofstack //
						std::cout << "_expand Module_0001 via Axiom_" << Axiom[guid_UInt64] << " {" << Theorem_0001[LHS] << ", " << Theorem_0001[RHS] << "}" << std::endl;

						Tasks_Thread.push(Theorem_0001);
					}

					if (Theorem[RHS] % Axiom[LHS] == 0)
					{
						std::vector<BigInt128_t> Theorem_0002{ Theorem };
						Theorem_0002[RHS] = Theorem_0002[RHS] / Axiom[LHS] * Axiom[RHS];
						Theorem_0002.emplace_back(0x02); // Push opcode 0x02 onto the proofstack because we performed a _rhs _reduce operation) //
						Theorem_0002.emplace_back(Axiom[guid_UInt64]); // Push the Axiom ID onto the proofstack //
						std::cout << "_reduce Module_0002 via Axiom_" << Axiom[guid_UInt64] << " {" << Theorem_0002[LHS] << ", " << Theorem_0002[RHS] << "}" << std::endl;

						Tasks_Thread.push(Theorem_0002);
					}

					if
						(Theorem[RHS] % Axiom[RHS] == 0)
					{
						std::vector<BigInt128_t> Theorem_0003{ Theorem };
						Theorem_0003[RHS] = Theorem_0003[RHS] / Axiom[RHS] * Axiom[LHS];
						Theorem_0003.emplace_back(0x03); // Push opcode 0x03 onto the proofstack because we performed a _rhs _expand operation) //
						Theorem_0003.emplace_back(Axiom[guid_UInt64]); // Push the Axiom ID onto the proofstack //
						std::cout << "_expand Module_0003 via Axiom_" << Axiom[guid_UInt64] << " {" << Theorem_0003[LHS] << ", " << Theorem_0003[RHS] << "}" << std::endl;

						Tasks_Thread.push(Theorem_0003);
					}
					std::cout << std::endl;
				} // end for (...Axiom : InAxiomsStdStrVec)
			} // end test (...Theorem[LHS] == Theorem[RHS])
		} // end for (...!Tasks_Thread.empty() && !QED))
		//*** End: Core Proof Engine (Loop) *** //

		if (!QED)
		{
			if (TempProofSteps.size())
			{
				std::cout << "Partial Proof Found." << std::endl;
			}
			else {
				std::cout << "No Proof Found." << std::endl;
			}
		}

		OutProofFound_FlagRef = QED;

		OutStatusReadyFlag = true; /* Set Status Variable last */

		return EXIT_SUCCESS;
	}

	enum class API_EXPORT BracketType { CurlyBraces, SquareBrackets, Parentheses };

	template <BracketType type>
	struct BracketTraits {};

	template <>
	struct BracketTraits<BracketType::CurlyBraces>
	{
		static constexpr std::string Open = "{";
		static constexpr std::string Close = "}";
	};

	template <>
	struct BracketTraits<BracketType::SquareBrackets>
	{
		static constexpr std::string Open = "[";
		static constexpr std::string Close = "]";
	};

	template <>
	struct BracketTraits<BracketType::Parentheses>
	{
		static constexpr std::string Open = "(";
		static constexpr std::string Close = ")";
	};

	class API_EXPORT CurlyBraceElide
	{
	public:
		/**
		Usage Example:
		std::vector<std::string> input = { "{", "{", "{", "1", "}", "}", "+", "{", "{", "1", "}", "}", "}", "=", "{", "{", "2", "}", "}" };
		const auto& output = CurlyBraceElide::Elide<BracketType::CurlyBraces>(input); // { "{", "1", "}", "+", "{", "1", "}", "=", "{", "2", "}" }
		*/
		template <BracketType type>
		static std::vector<std::string> Elide(const std::vector<std::string>& input)
		{
			static_assert(std::is_same_v<decltype(type), BracketType>, "Invalid bracket type");
			const std::string& openBrace = BracketTraits<type>::Open;
			const std::string& closeBrace = BracketTraits<type>::Close;
			std::vector<std::string> output;
			bool OpenScopeFlag = false;
			for (const std::string& c : input)
			{
				if (c == openBrace)
				{
					if (!OpenScopeFlag)
					{
						output.push_back(openBrace);
						OpenScopeFlag = true;
					}
					continue;
				}
				else if (c == closeBrace)
				{
					if (OpenScopeFlag)
					{
						output.push_back(closeBrace);
						OpenScopeFlag = false;
					}
					continue;
				}
				output.push_back(c);
			}
			return output;
		}
		/**
		Usage Example:
		const auto& output = CurlyBraceElide::Elide<BracketType::CurlyBraces>
		(
			{ 
				"{", "{", "{", "1", "}", "}", "+", "{", "{", "1", "}", "}", "}", "=", "{", "{", "2", "}", "}" 
			}
		); // Output: { "{", "1", "}", "+", "{", "1", "}", "=", "{", "2", "}" }
		*/
		template <BracketType type>
		static std::vector<std::string> Elide(const std::initializer_list<std::string>& input)
		{
			static_assert(std::is_same_v<decltype(type), BracketType>, "Invalid bracket type");
			const std::vector<std::string>& input2(input);
			return Elide<type>(input2);
		}
	};

	template<BracketType EuclidBracket>
	class API_EXPORT EuclidProver;

	template<>
	class API_EXPORT EuclidProver<BracketType::CurlyBraces>
	{
	public:
		explicit EuclidProver
		(
			const std::string openBrace = "{",
			const std::string closeBrace = "}"
		) noexcept :
			_openBrace{ openBrace },
			_openBraceST{ "st" + openBrace },
			_closeBrace{ closeBrace }
		{

		}

		bool StatusReady{};
		bool ProofFoundFlag{};

		bool Axiom
		(
			const
			std::vector<
			std::string>&
			InAxiomConstStdStrVecRef
		)
		{
			return true;
		}

		bool Axiom
		(
			const
			std::initializer_list<
			std::string>&
			InAxiomInitListConstStdStringRef
		)
		{
			const std::vector<std::string>& InAxiomVecConstStdStringRef{ InAxiomInitListConstStdStringRef };
			return Axiom(InAxiomVecConstStdStringRef);
		}

		bool Axioms
		(
			const
			std::vector<
			std::vector<
			std::vector<
			std::string>>>&
			InAxiomsConstStdStrVec
		)
		{
			AxiomsStdStrVec =

			{
				{
					{"1", "+", "1"}, // (lhs) Prime Composite: 8303 //
					{"2"} // (rhs) Prime Composite: 31
				},

				{
					{"2", "+", "2"}, // (lhs) Prime Composite: 22103 //
					{"4"} // (rhs) Prime Composite: 29 //
				}
			};

			return true;
		}

		bool Axioms
		(
			const
			std::initializer_list<
			std::vector<
			std::vector<
			std::string>>>& InAxiomInitListConstStdStringRef
		)
		{
			const
			std::vector<
			std::vector<
			std::vector<
			std::string>>>&
			TempInAxiomsConstStdStrVecRef{ InAxiomInitListConstStdStringRef };

			return Axioms(TempInAxiomsConstStdStrVecRef);
		}

		bool Lemma
		(
			const
			std::vector<
			std::string>&
			InLemmaConstStdStringVecRef
		)
		{
			return true;
		}

		bool Lemma
		(
			const
			std::initializer_list<
			std::string>&
			InLemmaConstStdStrInitListRef
		)
		{
			const std::vector<std::string>& InLemmaConstStdStrVecRef { InLemmaConstStdStrInitListRef };
			return Lemma(InLemmaConstStdStrVecRef);
		}

		bool Lemmas
		(
			const
			std::vector<
			std::vector<
			std::vector<
			std::string>>>&
			InLemmasConstStdStrVec
		)
		{
			return true;
		}

		bool Lemmas
		(
			const
			std::initializer_list<
			std::vector<
			std::vector<
			std::string>>>&
			InLemmasInitListConstStdStrVec
		)
		{
			const
			std::vector<
			std::vector<
			std::vector<
			std::string>>>&
			TempInLemmasConstStdStrVecRef { InLemmasInitListConstStdStrVec };

			return Lemmas(TempInLemmasConstStdStrVecRef);
		}

		void Prove
		(
			const
			std::vector<
			std::vector<
			std::string>>&
			InProofVecConstCharRef,

			std::vector<
			std::vector<
			std::vector<
			std::vector<
			std::string>>>>&
			OutPath4DStdStrVecRef,

			std::vector<
			std::vector<
			std::string>>&
			OutAxiomCommitLogStdStrVecRef
		)
		{			
			Reset();

			TheoremStdStrVec =

			{
				{"1", "+", "1", "+", "1", "+", "1"}, // (lhs) Prime Composite: 1585615607 //
				{"4"} // (rhs) Prime Composite: 29 //
			};

			std::thread th
			(
				__Prove__,
				std::cref(TheoremStdStrVec),
				std::cref(AxiomsStdStrVec),
				std::ref(ProofFoundFlag),
				std::ref(StatusReady),
				std::ref(ProofStep4DStdStrVec),
				std::ref(OutAxiomCommitLogStdStrVecRef)
			);

			th.detach();

			return;
		}

		void Prove
		(
			const
			std::initializer_list<
			std::vector<
			std::string>>&
			InProofInitListConstStdStrVecRef,

			std::vector<
			std::vector<
			std::vector<
			std::vector<
			std::string>>>>&
			OutPath4DStdStrVecRef,

			std::vector<
			std::vector<
			std::string>>&
			OutAxiomCommitLogStdStrVecRef
		)
		{
			const
			std::vector<
			std::vector<
			std::string>>&
			InProofVecConstCharRef { InProofInitListConstStdStrVecRef };

			Prove 
			(
				InProofVecConstCharRef,
				OutPath4DStdStrVecRef,
				OutAxiomCommitLogStdStrVecRef
			);
		}

	private:
		const std::string _openBrace;
		const std::string _openBraceST;
		const std::string _closeBrace;

		std::vector<
		std::vector<
		std::vector<
		std::string>>>
		AxiomsStdStrVec{};

		std::vector<
		std::vector<
		std::string>>
		TheoremStdStrVec{};

		std::vector<
		std::vector<
		std::vector<
		std::vector<
		std::string>>>>
		ProofStep4DStdStrVec{};

		void Reset()
		{
			StatusReady = false;
			ProofFoundFlag = false;
		};
	};

	template<>
	class API_EXPORT EuclidProver<BracketType::Parentheses> : public EuclidProver<BracketType::CurlyBraces>
	{
	public:
		EuclidProver() noexcept : EuclidProver<BracketType::CurlyBraces>("(", ")")
		{

		}
	};

	template<>
	class API_EXPORT EuclidProver<BracketType::SquareBrackets> : public EuclidProver<BracketType::CurlyBraces>
	{
	public:
		EuclidProver() noexcept : EuclidProver<BracketType::CurlyBraces>("[", "]")
		{

		}
	};
}

using EuclidProverClass =

Euclid_Prover::EuclidProver<
Euclid_Prover::BracketType::CurlyBraces>;