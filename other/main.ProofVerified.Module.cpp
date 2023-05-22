#include <iostream>
#include <cstdlib>
#include <chrono>
#include <vector>
#include <string>
#include <unordered_map>

/*
Q: Write a c++20 algorithm, TentativeProofVerified, which accepts Theorem,
InTheoremStdStrVec, and InAxiomsStdStrVec, as parameters and returns a bool type.

TentativeProofVerified clones InTheoremStdStrVec as OutTheoremStdStrVec, and performs
the following operations:

TentativeProofVerified loops through Theorem, starting at Theorem[ProofStackUInt64],
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

If TentativeProofVerified is unable to complete the loop, the algorithm returns false.

*/

const int LHS = 0;
const int RHS = 1;

const
uint64_t
ProofStackUInt64 = 4;

const
std::vector<
    uint64_t> Theorem =
{
    1585615607, // (lhs) Prime Composite: 1585615607 // {"1", "+", "1", "+", "1", "+", "1"}
    29, // (rhs) Prime Composite: 29 // {"4"}
    0, // guid // 
    0, // last //
    0x03, // Begin ProofStackUInt64... //
    2,
    0x03,
    1,
    0x03,
    1
};

const
std::vector<
    std::vector<
    std::string>>
    InTheoremStdStrVec =
{
    {"1", "+", "1", "+", "1", "+", "1"}, // (lhs) Prime Composite: 1585615607 //
    {"4"} // (rhs) Prime Composite: 29 //   
};

const
std::vector<
    std::vector<
    std::vector<
    std::string>>>
    InAxiomsStdStrVec =
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

void RemoveEmptyStrings(auto& vec)
{
    // Remove empty strings from-, and resize-, the vec.
    vec.erase(
        std::remove_if(
            vec.begin(),
            vec.end(),
            [](const std::string& s)
            {
                return s.empty();
            }), vec.end());
}

bool Rewrite
(
    std::vector<
    std::string>& th,

    const
    std::vector<
    std::string>& from,

    const
    std::vector<
    std::string>& to
)
{
    bool bSuccessFlag{};

    if (th.size() < from.size())
        return false;

    std::unordered_map<std::string, std::string>

        endscope{ {"(", ")"}, {"{", "}"}, {"[", "]"} };

    std::vector<
        std::string> result{};

    uint64_t i{};

    const uint64_t I{ from.size() };

    for (const std::string& val : th)
    {
        std::cout << "Next val: " << val << std::endl;

        if (val == from[i])
        {
            ++i;

            std::cout << "Match found: " << val;

            if (i == I)
            {
                for (const std::string& u2 : to)
                {
                    std::cout << u2 << " ";
                    result.emplace_back(u2);
                }

                bSuccessFlag = true;

                std::cout << "\nSubstitution found" << std::endl;

                i = 0;
            }
        }
        else {
            i = 0; // reset //

            std::cout << "No Match found: " << val << std::endl;

            result.emplace_back(val);
        }
        std::cout << std::endl;
    }

    th = result;

    return bSuccessFlag;
}#include <iostream>
#include <cstdlib>
#include <chrono>
#include <vector>
#include <string>
#include <unordered_map>

/*
Q: Write a c++20 algorithm, TentativeProofVerified, which accepts Theorem,
InTheoremStdStrVec, and InAxiomsStdStrVec, as parameters and returns a bool type.

TentativeProofVerified clones InTheoremStdStrVec as OutTheoremStdStrVec, and performs
the following operations:

TentativeProofVerified loops through Theorem, starting at Theorem[ProofStackUInt64],
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

If TentativeProofVerified is unable to complete the loop, the algorithm returns false.

*/

const int LHS = 0;
const int RHS = 1;

const
uint64_t
ProofStackUInt64 = 4;

const
std::vector<
    uint64_t> Theorem =
{
    1585615607, // (lhs) Prime Composite: 1585615607 // {"1", "+", "1", "+", "1", "+", "1"}
    29, // (rhs) Prime Composite: 29 // {"4"}
    0, // guid // 
    0, // last //
    0x03, // Begin ProofStackUInt64... //
    2,
    0x03,
    1,
    0x03,
    1
};

const
std::vector<
    std::vector<
    std::string>>
    InTheoremStdStrVec =
{
    {"1", "+", "1", "+", "1", "+", "1"}, // (lhs) Prime Composite: 1585615607 //
    {"4"} // (rhs) Prime Composite: 29 //   
};

const
std::vector<
    std::vector<
    std::vector<
    std::string>>>
    InAxiomsStdStrVec =
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

bool Rewrite
(
    auto& th,

    const auto& from,

    const auto& to
)
{
    bool bSuccessFlag{};

    if (th.size() < from.size())
        return false;

    std::unordered_map<std::string, std::string>

        endscope{ {"(", ")"}, {"{", "}"}, {"[", "]"} };

    std::vector<
        std::string> result{};

    uint64_t i{};

    const uint64_t I{ from.size() };

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
                    result.emplace_back(u2);
                }

                bSuccessFlag = true;

                std::cout << ">> Substitution made" << std::endl;

                i = 0;

                continue;
            }
        }
        else {
            i = 0; // reset //

            std::cout << "No Match found: " << val << std::endl;

            result.emplace_back(val);
        }
        std::cout << std::endl;
    }

    th = result;

    return bSuccessFlag;
}

bool ProofVerified
(
    const
    std::vector<
    uint64_t>&
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
)
{
    bool ReturnStatusFlag{ true };

    OutTheoremStdStrVec.emplace_back(InTheoremStdStrVec);

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

    uint64_t i{ ProofStackUInt64 };

    while (i < Theorem.size())
    {
        if (!ReturnStatusFlag)
            return ReturnStatusFlag;

        const uint64_t& opcode = Theorem[i++];
        const uint64_t& guid = Theorem[i++] - 1;

        //TempTheoremStdStrVec = OutTheoremStdStrVec.back();

        switch (opcode)
        {
        case 0x00: { // "lhsreduce" operation //
            std::cout << "lhs_reduce via Axiom_" << guid/*.str()*/ << std::endl;
            ReturnStatusFlag =
                Rewrite(TempTheoremStdStrVec[LHS], InAxiomsStdStrVec[guid][LHS], InAxiomsStdStrVec[guid][RHS]);
            TempAxiomCommitLogStdStrVecRef.emplace_back("lhs_reduce via Axiom_" + guid/*.str()*/);
            break;
        }
        case 0x01: { // "lhsexpand" operation //
            std::cout << "lhs_expand via Axiom_" << guid/*.str()*/ << std::endl;
            ReturnStatusFlag =
                Rewrite(TempTheoremStdStrVec[LHS], InAxiomsStdStrVec[guid][RHS], InAxiomsStdStrVec[guid][LHS]);
            TempAxiomCommitLogStdStrVecRef.emplace_back("lhs_expand via Axiom_" + guid/*.str()*/);
            break;
        }
        case 0x02: { // "rhsreduce" operation //
            std::cout << "rhs_reduce via Axiom_" << guid/*.str()*/ << std::endl;
            ReturnStatusFlag =
                Rewrite(TempTheoremStdStrVec[RHS], InAxiomsStdStrVec[guid][LHS], InAxiomsStdStrVec[guid][RHS]);
            TempAxiomCommitLogStdStrVecRef.emplace_back("rhs_reduce via Axiom_" + guid/*.str()*/);
            break;
        }
        case 0x03: { // "rhsexpand" operation //
            std::cout << "rhs_expand via Axiom_" << guid/*.str()*/ << std::endl;
            ReturnStatusFlag =
                Rewrite(TempTheoremStdStrVec[RHS], InAxiomsStdStrVec[guid][RHS], InAxiomsStdStrVec[guid][LHS]);
            TempAxiomCommitLogStdStrVecRef.emplace_back("rhs_expand via Axiom_" + guid/*.str()*/);
            break;
        }
        default: {
            // Invalid opcode. //
            ReturnStatusFlag = false;
            break; false;
        }
        } // end switch(opcode)
        OutTheoremStdStrVec.emplace_back(TempTheoremStdStrVec);
    }
    OutAxiomCommitLogStdStrVecRef.emplace_back(TempAxiomCommitLogStdStrVecRef);

    // If TentativeProofVerified is unable to complete the loop, the algorithm returns false.
    return true;
}

int main()
{
    std::vector<
        std::vector<
        std::vector<
        std::string>>>
        OutTheoremStdStrVec;

    std::vector<
        std::vector<
        std::string>>
        OutAxiomCommitLogStdStrVecRef;

    ProofVerified
    (
        Theorem,
        InTheoremStdStrVec,
        InAxiomsStdStrVec,
        OutAxiomCommitLogStdStrVecRef,
        OutTheoremStdStrVec
    );

    return EXIT_SUCCESS;
}

