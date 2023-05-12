#include <cstdlib>
#include <string>
#include <vector>
#include <iostream>
#include <Euclid.h>

int main()
{
    using EuclidProverClass =

        Euclid_Prover::EuclidProver<
        Euclid_Prover::BracketType::CurlyBraces>;

    // Instantiate Prover (module)
    EuclidProverClass Euclid;

    Euclid.Axioms
    (
        {
            // Axiom_1
            {
              {"1", "+", "1"}, // (lhs) Prime Composite: 8303 //
              {"2"} // (rhs) Prime Composite: 31 //
            },

        // Axiom_2
        {
          {"2", "+", "2"}, // (lhs) Prime Composite: 22103 //
          {"4"} // (rhs) Prime Composite: 29 //
        }
        }
    );

    /*

    // OR...

    Euclid.Axiom
    (
      // Axiom_1
      {
        {"1", "+", "1"}, // (lhs) Prime Composite: 8303 //
        {"2"} // (rhs) Prime Composite: 31 //
      },
    );

    Euclid.Axiom
    (
      // Axiom_2
      {
        {"2", "+", "2"}, // (lhs) Prime Composite: 22103 //
        {"4"} // (rhs) Prime Composite: 29 //
      }
    );
    */

    std::vector<
        std::vector<
        std::vector<
        std::vector<
        std::string>>>>

        // Instantiate ProofStep_4DStdStrVec[proof][step][lhs/rhs][token]
        ProofStep_4DStdStrVec;

    std::vector<
        std::vector<
        std::string>>

        // Instantiate AxiomCommitLog_StdStrVec[proof][step]
        AxiomCommitLog_StdStrVec;

    const auto start_time_chrono = std::chrono::high_resolution_clock::now();

    Euclid.Prove
    (
        {
          {"1", "+", "1", "+", "1", "+", "1"}, // (lhs) Prime Composite: 1585615607 //
          {"4"}, // (rhs) Prime Composite: 29 //
        },

        ProofStep_4DStdStrVec,
        AxiomCommitLog_StdStrVec
        );

    while (!Euclid.StatusReady)
    {
        //std::cout << "Performing some other work..." << std::endl;
        //std::this_thread::sleep_for(std::chrono::seconds(1));
    }

    if (Euclid.ProofFound_Flag)
    {
        std::cout << "Proof Found." << std::endl;
        ProofStep_4DStdStrVec;
        AxiomCommitLog_StdStrVec;
    }
    else if (ProofStep_4DStdStrVec.size()) {
        std::cout << "Partial Proof Found." << std::endl;
        ProofStep_4DStdStrVec;
        AxiomCommitLog_StdStrVec;
    }
    else {
        std::cout << "No Proof Found." << std::endl;
    }

    std::cout << std::endl;
    const auto end_time_chrono = std::chrono::high_resolution_clock::now();
    const auto duration_chrono = std::chrono::duration_cast<std::chrono::nanoseconds>(end_time_chrono - start_time_chrono).count();
    std::cout << "Total Duration (nanoseconds): " << duration_chrono << std::endl;

    // Hold for user-input //
    std::string inChar;
    std::cin >> inChar;

    return EXIT_SUCCESS;
}

/*
Output:

ProofStep_4DStdStrVec:
{
  {
    // Step 1 (Original).
    {
      {"1", "+", "1", "+", "1", "+", "1"}, // (lhs) Prime Composite: 1585615607 //
      {"4"} // (rhs) Prime Composite: 29 //
    },

    // Step 2. (rhs_expand via Axiom_2)
    {
      {"1", "+", "1", "+", "1", "+", "1"}, // (lhs) Prime Composite: 1585615607 //
      {"2", "+", "2"} // (rhs) Prime Composite: 22103 //
    },

    // Step 3. (rhs_expand via Axiom_1)
    {
      {"1", "+", "1", "+", "1", "+", "1"}, // (lhs) Prime Composite: 1585615607 //
      {"1", "+", "1", "+", "2"} // (rhs) Prime Composite: 5920039 //
    },

    // Step 4. (rhs_expand via Axiom_1)
    {
      {"1", "+", "1", "+", "1", "+", "1"}, // (lhs) Prime Composite: 1585615607 //
      {"1", "+", "1", "+", "1", "+", "1"} // (rhs) Prime Composite: 1585615607 (QED) //
    }
  }
}

AxiomCommitLog_StdStrVec:
{
  {
    "rhs_expand via Axiom_2",
    "rhs_expand via Axiom_1",
    "rhs_expand via Axiom_1"
  }
}
*/
