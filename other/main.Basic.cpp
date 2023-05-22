
/*

  AUTHOR
      Seagat2011 www.gitub.com/Seagat2011
      eterna.cmu.edu/web/player/90270/
      fold.it/port/user/1992490

  VERSION
      Major.Minor.Bugfix.Patch
      12.0.0.0

  DESCRIPTION
    Theorem prover written in C++20 ported from JavaScript (An E-normalization to normal form, term-rewriting system)
    for use in the Unreal Engine 5.2 Core Lib.

  UPDATES (C++20)
    +_lhs/_rhs RouteSource_EnumClass support for all subnet route maps (Improved branch Performance)
    +Specialization templates - for the primary "Auto" template function declaration (Improved branch Performance)
    +Lockless stack manager: RecursionLimiter (Eliminates mutex/semaphore Performance penalty)
    -Multithread support (Increased latency, reduced scalability)

  UPDATES (JavaScript)
    +Negative proof assertions ~=
    +_AXIOM_.optimizeCallGraph
    +Improved ProofComplete search performance
    +Prove via Auto (PASS)
    +Axiom._eval => Axiom._reduce
    +Axiom.{_reduce,_expand} => eventListener(s)
    +solutionEditor => contentEditable
    +Prove via Reduce (PASS)
    +Prove via Expand (PASS)
    +scoping functionality
    +LibreOffice math library support
    -Axiom._eval eventListener

  NOTES:
    Term rewrites are performed with the aid of a compiler (ie. via LEMMA SUBSTITUTION); SEE TEST CASES

    Substitution methods:
    1. (direct) AXIOMATIC: 1 + 1 = 2
    2. (helper) LEMMA SUBSTITUTION: 1 <==> 1 / 1
    Note: Lemma substitutions rewrite axioms, which can introduce recursion, stack overflow, and other bugs:
    Consider "{ PlayerCharacterSideKick } IsIn { StyxBoat }" - the IsIn operator may or may not link unrelated categories,
    whereas "{ PlayerCharacterSideKick } IsIn_StyxBoat " is guaranteed to converge !!!

  Usage Example. // Lemma substitutions //

    { { a } raised { 2 } } plus { 2ab } plus { b raised { 2 } } <== ( { a } plus { b } ) raised { 2 }
    ( { a } plus { b } ) raised { 2 } minus { 2ab } = { c } raised { 2 } <== ( { a } plus { b } ) raised { 2 } = { { c } raised { 2 } } plus { 2ab }
    { { a } raised { 2 } } plus { 2ab } minus { 2ab } plus { b raised { 2 } } ==> { { a } raised { 2 } } plus { { b } raised { 2 } }
    ( { a } plus { b } ) raised { 2 } = { { c } raised { 2 } } plus { 2ab }
    Prove { { a } raised { 2 } } plus { { b } raised { 2 } } = { c } raised { 2 }

  Usage Example. // Lemma substitution //

    // Axiom
    { PlayerCharacterSideKick } IsIn { StyxBoat } = { StyxBoat } IsIn { StyxRiver } // Current Game State
    { PlayerCharacterSideKick } IsIn { Vehicle { QuadUtilityVehicle } } = { Vehicle { QuadUtilityVehicle } } IsIn { EuropaLand } and { Vehicle { QuadUtilityVehicle { VehicleDriveDisabled } } }
    { PlayerCharacterSideKick } IsIn { EuropaLand } = { Vehicle { QuadUtilityVehicle } } IsIn { EuropaLand }
    { PlayerCharacterSideKick } IsIn { QuadUtilityVehicle } = { Vehicle { QuadUtilityVehicle { VehicleDriveDisabled } } }
    { PlayerCharacterSideKick } IsNotIn { Vehicle { QuadUtilityVehicle } } = { Vehicle { QuadUtilityVehicle } } IsIn { EuropaLand }
    .
    . [Other available non-relevant Game States, in the current environment, for the PlayerCharacterSideKick to choose from ]
    .
    { PlayerCharacterSideKick } IsIn { QuadUtilityVehicle } = { QuadUtilityVehicle } and { VehicleDriveDisabled }

    // Lemma
    { PlayerCharacterSideKick } IsIn { StyxBoat } <== { StyxBoat } IsNotIn { StyxRiver } // These are connectives, and axiom helpers
    { PlayerCharacterSideKick } IsOn { Vehicle } <== { VehicleDriveDisabled }
    { PlayerCharacterSideKick } IsIn { Vehicle { QuadUtilityVehicle } } <== { PlayerCharacterSideKick } IsIn { QuadUtilityVehicle }
    { PlayerCharacterSideKick } IsNotIn { StyxBoat } ==> { StyxBoat } IsNotIn { StyxRiver }

    // Theorem
    Prove { PlayerCharacterSideKick } IsIn { QuadUtilityVehicle } = { QuadUtilityVehicle } and { VehicleDriveDisabled }

    // Output (Proof-Steps)
    { PlayerCharacterSideKick } IsIn { StyxBoat } = { StyxBoat } IsIn { StyxRiver }
    { PlayerCharacterSideKick } IsIn { StyxBoat } = { StyxBoat } IsNotIn { StyxRiver }
    { PlayerCharacterSideKick } IsNotIn { StyxBoat } = { StyxBoat } IsNotIn { StyxRiver }
    { PlayerCharacterSideKick } IsIn { EuropaLand } = { Vehicle { QuadUtilityVehicle } } IsIn { EuropaLand }
    { PlayerCharacterSideKick } IsNotIn { Vehicle { QuadUtilityVehicle } } = { Vehicle { QuadUtilityVehicle } } IsIn { EuropaLand }
    { PlayerCharacterSideKick } IsIn { Vehicle { QuadUtilityVehicle } } = { Vehicle { QuadUtilityVehicle } } IsIn { EuropaLand } and { Vehicle { QuadUtilityVehicle { VehicleDriveDisabled } } }
    { PlayerCharacterSideKick } IsIn { QuadUtilityVehicle } = { Vehicle { QuadUtilityVehicle { VehicleDriveDisabled } } }
    { PlayerCharacterSideKick } IsIn { QuadUtilityVehicle } = { QuadUtilityVehicle } and { VehicleDriveDisabled }

  REFERENCES
      OpenAI GPT-4-32k-0314 max_tokens:32000 temperature:1.0 top_p:1.0
          N:1 stream:false logprobs:NULL echo:false stop:NULL
          presence_penalty:0 frequency_penalty:0 best_of:1 logit_bias:NULL

  COMPATIBILITY
      Windows 11+ x86i64

*/

#include <iostream>
#include <thread>
#include <atomic>
#include <cstdint>
#include <functional>
#include <cstdlib>
#include <array>
#include <chrono>

enum class MaxCPUCores : int
{
    _1,
    _Max,
    _GPU_Enabled
};

enum class RouteGoal_EnumClass : int
{
    _lhs,
    _rhs,
    _root
};

enum class Indirection_EnumClass : int
{
    _auto,
    _reduce,
    _expand
};

struct AxiomProto_Struct
{
    uint64_t LHSPrimaryKey_UInt64{};
    uint64_t RHSPrimaryKey_UInt64{};

    std::vector<std::string> LHS_StdStrVec;
    std::vector<std::string> RHS_StdStrVec;

    std::unordered_map<RouteGoal_EnumClass,
        std::unordered_map<uint64_t, bool>>
        LHSCallHistory;

    std::unordered_map<RouteGoal_EnumClass,
        std::unordered_map<uint64_t, bool>>
        RHSCallHistory;

    std::unordered_map<RouteGoal_EnumClass,
        std::unordered_map<uint64_t, bool>>
        LHSCallGraph_UInt64Map;

    std::unordered_map<RouteGoal_EnumClass,
        std::unordered_map<uint64_t, bool>>
        RHSCallGraph_UInt64Map;

    bool SubnetFound_LHS(const uint64_t& PKeyFind) const noexcept
    {
        const bool ret = (LHSPrimaryKey_UInt64 % PKeyFind) == 0;
        return ret;
    }

    bool SubnetFound_RHS(const uint64_t& PKeyFind) const noexcept
    {
        const bool ret = (RHSPrimaryKey_UInt64 % PKeyFind) == 0;
        return ret;
    }

    bool bParseStrict_Flag{};

    uint64_t guid{};
};

struct Theorem_Struct : public AxiomProto_Struct
{
    uint64_t TotalProofsFound_UInt64{};
    uint64_t MaxAllowedProofs_UInt64 = 1;

    bool ProofFound_Flag{};

    std::vector<uint64_t> ProofStack_VecUInt64;

    std::vector<std::string> ProofString_StdStrVec;

    Indirection_EnumClass Indir_EnumClass = Indirection_EnumClass::_auto;

    bool UpdatePrimaryKey_LHS(const uint64_t& PKeyFind, const uint64_t& PKeyReplace) noexcept
    {
        bool ReturnStatus_Flag{};
        LHSPrimaryKey_UInt64 = LHSPrimaryKey_UInt64 / PKeyFind * PKeyReplace;
        ReturnStatus_Flag = true;
        return ReturnStatus_Flag;
    }

    bool UpdatePrimaryKey_RHS(const uint64_t& PKeyFind, const uint64_t& PKeyReplace) noexcept
    {
        bool ReturnStatus_Flag{};
        RHSPrimaryKey_UInt64 = RHSPrimaryKey_UInt64 / PKeyFind * PKeyReplace;
        ReturnStatus_Flag = true;
        return ReturnStatus_Flag;
    }
};

struct Axiom_Struct : public AxiomProto_Struct
{

};

struct NextRound_Struct
{
    bool OddRoundFlag{};

    uint8_t NextRound_UInt8()
    {
        uint8_t ret{};

        if (OddRoundFlag)
        {
            ret = 1;
        }

        OddRoundFlag = !OddRoundFlag;

        return ret;
    };

    uint8_t CurrentRound_UInt8()
    {
        uint8_t ret{ 1 };

        if (OddRoundFlag)
        {
            ret = 0;
        }

        return ret;
    };
};

uint64_t GUID{};

const uint64_t MaxStackSize_UInt64 = std::numeric_limits<unsigned long long>::max();

int main()
{
    const auto start_time_chrono = std::chrono::high_resolution_clock::now();

    /*
    token: [ "1" "2" "4" "+" ]
    prime: [  2   3   5   7 ]
    */

    Theorem_Struct Theorem;

    const uint64_t N = 2; // Update as needed;

    std::array < Axiom_Struct, N > Axioms_Vec;

    std::unordered_map <uint64_t, Axiom_Struct> Axioms_LibraryMap;

    std::vector<std::array<uint64_t, 2>> Axioms_UInt64Vec = // const (global) task list
    {
        {//std::vector<uint64_t> _1p1p1p1e4 =
            5488, // "1 + 1 + 1 + 1"
            5 // "4"
        },//;

        {//std::vector<uint64_t> _1p1e2 =
            28, // "1 + 1"
            3 // "2"
        },//;

        {//std::vector<uint64_t> _2p2e4 =
            63, // "2 + 2"
            5 // "4"
        }
    };

    for (const std::array<uint64_t, 2>& Axiom_i : Axioms_UInt64Vec)
    {
        uint64_t  lhs = Axiom_i[0];
        uint64_t  rhs = Axiom_i[1];

        const uint64_t _lhs = Axiom_i[0];
        const uint64_t _rhs = Axiom_i[1];

        if (_lhs < _rhs)
        {
            lhs = _rhs;
            rhs = _lhs;
        }

        if (GUID < 1)
        {
            Theorem.guid = ++GUID;
            Theorem.LHSPrimaryKey_UInt64 = lhs;
            Theorem.RHSPrimaryKey_UInt64 = rhs;
            continue;
        }

        Axiom_Struct Axiom;
        Axiom.guid = ++GUID;
        Axiom.LHSPrimaryKey_UInt64 = lhs;
        Axiom.RHSPrimaryKey_UInt64 = rhs;

        /*
        Authorize qualifying axiom subnets by adding
        their netlists to the outbound route map
        */

        if (Theorem.SubnetFound_LHS(lhs))
        {
            Theorem.LHSCallGraph_UInt64Map[RouteGoal_EnumClass::_rhs][Axiom.guid] = true;
        }

        if (Theorem.SubnetFound_LHS(rhs))
        {
            Theorem.LHSCallGraph_UInt64Map[RouteGoal_EnumClass::_lhs][Axiom.guid] = true;
        }

        if (Theorem.SubnetFound_RHS(lhs))
        {
            Theorem.RHSCallGraph_UInt64Map[RouteGoal_EnumClass::_rhs][Axiom.guid] = true;
        }

        if (Theorem.SubnetFound_RHS(rhs))
        {
            Theorem.RHSCallGraph_UInt64Map[RouteGoal_EnumClass::_lhs][Axiom.guid] = true;
        }

        Axioms_Vec[Axiom.guid - 1] = Axiom;
    }

    for (Axiom_Struct& Axiom_i : Axioms_Vec)
    {
        for (const Axiom_Struct& Axiom_j : Axioms_Vec)
        {
            /*
            Authorize qualifying axiom subnets by adding
            their netlists to the outbound route map
            */
            const bool ijAvoidsACallLoop_Flag = (Axiom_i.guid != Axiom_j.guid); // Avoid CallGraph loops
            if (ijAvoidsACallLoop_Flag)
            {
                if (Axiom_i.SubnetFound_LHS(Axiom_j.LHSPrimaryKey_UInt64))
                {
                    Axiom_i.LHSCallGraph_UInt64Map[RouteGoal_EnumClass::_rhs][Axiom_j.guid] = true;
                }

                if (Axiom_i.SubnetFound_LHS(Axiom_j.RHSPrimaryKey_UInt64))
                {
                    Axiom_i.LHSCallGraph_UInt64Map[RouteGoal_EnumClass::_lhs][Axiom_j.guid] = true;
                }

                if (Axiom_i.SubnetFound_RHS(Axiom_j.LHSPrimaryKey_UInt64))
                {
                    Axiom_i.RHSCallGraph_UInt64Map[RouteGoal_EnumClass::_rhs][Axiom_j.guid] = true;
                }

                if (Axiom_i.SubnetFound_RHS(Axiom_j.RHSPrimaryKey_UInt64))
                {
                    Axiom_i.RHSCallGraph_UInt64Map[RouteGoal_EnumClass::_lhs][Axiom_j.guid] = true;
                }
            }
        }
    }

    for (Axiom_Struct& Axiom_i : Axioms_Vec)
    {
        Axioms_LibraryMap[Axiom_i.guid] = Axiom_i;
    }

    NextRound_Struct Round;

    std::array < std::vector < Theorem_Struct >, 2 > Tasks_Thread;

    Tasks_Thread[0].push_back(Theorem);

    uint64_t MaxAllowedProofs_UInt64{ 1 };
    uint64_t TotalProofsFound_UInt64{};

    uint8_t Read = Round.NextRound_UInt8();

    //while(Tasks_Thread[Read].size())
    //{
    const uint8_t Write = Round.CurrentRound_UInt8();

    for (Theorem_Struct InTheorem : Tasks_Thread[Read])
    {
        if (InTheorem.LHSPrimaryKey_UInt64 == InTheorem.RHSPrimaryKey_UInt64)
        {
            for (const uint64_t& nID_UInt64 : InTheorem.ProofStack_VecUInt64)
            {
                std::cout << "Axiom_" << static_cast<uint64_t>(nID_UInt64) << std::endl;
            }

            std::cout << "\n\n";
            std::cout << "Q.E.D.";

            ++TotalProofsFound_UInt64;

            if (TotalProofsFound_UInt64 >= MaxAllowedProofs_UInt64)
                break;
        }

        const bool CallLHSRouteLHS_Flag =
            InTheorem.LHSCallGraph_UInt64Map.find(RouteGoal_EnumClass::_lhs) !=
            InTheorem.LHSCallGraph_UInt64Map.begin();

        const bool CallLHSRouteRHS_Flag =
            InTheorem.LHSCallGraph_UInt64Map.find(RouteGoal_EnumClass::_rhs) !=
            InTheorem.LHSCallGraph_UInt64Map.begin();

        const bool CallRHSRouteLHS_Flag =
            InTheorem.RHSCallGraph_UInt64Map.find(RouteGoal_EnumClass::_lhs) !=
            InTheorem.RHSCallGraph_UInt64Map.begin();

        const bool CallRHSRouteRHS_Flag =
            InTheorem.RHSCallGraph_UInt64Map.find(RouteGoal_EnumClass::_rhs) !=
            InTheorem.RHSCallGraph_UInt64Map.begin();

        const bool CallLHSRouteAll_CallRHSRouteAll_Flag =
            (CallLHSRouteLHS_Flag &&
                CallLHSRouteRHS_Flag &&
                CallRHSRouteLHS_Flag &&
                CallRHSRouteRHS_Flag);

        const bool CallLHSRouteAll_CallRHSRouteLHS_Flag =
            (CallLHSRouteLHS_Flag &&
                CallLHSRouteRHS_Flag &&
                CallRHSRouteLHS_Flag &&
               !CallRHSRouteRHS_Flag);

        const bool CallLHSRouteAll_CallRHSRouteRHS_Flag =
            (CallLHSRouteLHS_Flag &&
                CallLHSRouteRHS_Flag &&
               !CallRHSRouteLHS_Flag &&
                CallRHSRouteRHS_Flag);

        const bool CallLHSRouteLHS_CallRHSRouteAll_Flag =
            (CallLHSRouteLHS_Flag &&
               !CallLHSRouteRHS_Flag &&
                CallRHSRouteLHS_Flag &&
                CallRHSRouteRHS_Flag);

        const bool CallLHSRouteLHS_CallRHSRouteLHS_Flag =
            (CallLHSRouteLHS_Flag &&
               !CallLHSRouteRHS_Flag &&
                CallRHSRouteLHS_Flag &&
               !CallRHSRouteRHS_Flag);

        const bool CallLHSRouteLHS_CallRHSRouteRHS_Flag =
            (CallLHSRouteLHS_Flag &&
               !CallLHSRouteRHS_Flag &&
               !CallRHSRouteLHS_Flag &&
                CallRHSRouteRHS_Flag);

        const bool CallLHSRouteRHS_CallRHSRouteAll_Flag =
            (!CallLHSRouteLHS_Flag &&
                CallLHSRouteRHS_Flag &&
                CallRHSRouteLHS_Flag &&
                CallRHSRouteRHS_Flag);

        const bool CallLHSRouteRHS_CallRHSRouteLHS_Flag =
            (!CallLHSRouteLHS_Flag &&
                CallLHSRouteRHS_Flag &&
                CallRHSRouteLHS_Flag &&
               !CallRHSRouteRHS_Flag);

        const bool CallLHSRouteRHS_CallRHSRouteRHS_Flag =
            (!CallLHSRouteLHS_Flag &&
                CallLHSRouteRHS_Flag &&
               !CallRHSRouteLHS_Flag &&
                CallRHSRouteRHS_Flag);

        const bool CallLHSRouteAll_Flag =
            (CallLHSRouteLHS_Flag &&
                CallLHSRouteRHS_Flag &&
               !CallRHSRouteLHS_Flag &&
               !CallRHSRouteRHS_Flag);

        const bool CallLHSRouteLHS_Flag =
            (CallLHSRouteLHS_Flag &&
               !CallLHSRouteRHS_Flag &&
               !CallRHSRouteLHS_Flag &&
               !CallRHSRouteRHS_Flag);

        const bool CallLHSRouteRHS_Flag =
            (!CallLHSRouteLHS_Flag &&
                CallLHSRouteRHS_Flag &&
               !CallRHSRouteLHS_Flag &&
               !CallRHSRouteRHS_Flag);

        const bool CallRHSRouteAll_Flag =
            (!CallLHSRouteLHS_Flag &&
               !CallLHSRouteRHS_Flag &&
                CallRHSRouteLHS_Flag &&
                CallRHSRouteRHS_Flag);

        const bool CallRHSRouteLHS_Flag =
            (!CallLHSRouteLHS_Flag &&
               !CallLHSRouteRHS_Flag &&
                CallRHSRouteLHS_Flag &&
               !CallRHSRouteRHS_Flag);

        const bool CallRHSRouteRHS_Flag =
            (!CallLHSRouteLHS_Flag &&
               !CallLHSRouteRHS_Flag &&
               !CallRHSRouteLHS_Flag &&
                CallRHSRouteRHS_Flag);

        switch (InTheorem.Indir_EnumClass)
        {
        case Indirection_EnumClass::_reduce:
            if (CallLHSRouteLHS_Flag)
            {
                // no solution //
                continue;
            }

            else if (CallLHSRouteRHS_Flag)
            {

            }

            else if (CallRHSRouteLHS_Flag)
            {
                // no solution //
                continue;
            }

            else if (CallRHSRouteRHS_Flag)
            {

            }

            else if (CallAllRouteAll_Flag)
            {
                for (const auto& idw_pair : InTheorem.LHSCallGraph_UInt64Map [ RouteGoal_EnumClass :: _lhs ])
                {
                    for (const auto& idx_pair : InTheorem.LHSCallGraph_UInt64Map [ RouteGoal_EnumClass :: _rhs ])
                    {
                        for (const auto& idy_pair : InTheorem.RHSCallGraph_UInt64Map [ RouteGoal_EnumClass :: _lhs ])
                        {
                            for (const auto& idz_pair : InTheorem.RHSCallGraph_UInt64Map [ RouteGoal_EnumClass :: _rhs ])
                            {
                                // guid
                                const uint64_t& idw_UInt64 = idw_pair.first;
                                const uint64_t& idx_UInt64 = idx_pair.first;
                                const uint64_t& idy_UInt64 = idy_pair.first;
                                const uint64_t& idz_UInt64 = idz_pair.first;

                                // Flags
                                const bool& idw_read_Flag =
                                    InTheorem.LHSCallHistory [ RouteGoal_EnumClass :: _lhs ].find( idw_UInt64 ) !=
                                    InTheorem.LHSCallHistory [ RouteGoal_EnumClass :: _lhs ].begin();

                                const bool& idx_read_Flag =
                                    InTheorem.LHSCallHistory [ RouteGoal_EnumClass :: _rhs ].find( idx_UInt64 ) !=
                                    InTheorem.LHSCallHistory [ RouteGoal_EnumClass :: _rhs ].begin();

                                const bool& idy_read_Flag =
                                    InTheorem.RHSCallHistory [ RouteGoal_EnumClass :: _lhs ].find( idy_UInt64 ) !=
                                    InTheorem.RHSCallHistory [ RouteGoal_EnumClass :: _lhs ].begin();

                                const bool& idz_read_Flag =
                                    InTheorem.RHSCallHistory [ RouteGoal_EnumClass :: _rhs ].find( idz_UInt64 ) !=
                                    InTheorem.RHSCallHistory [ RouteGoal_EnumClass :: _rhs ].begin();

                                // _reduce

                                if (idx_read_Flag)
                                {
                                    Theorem_Struct th_0000 = InTheorem;
                                    const Axiom_Struct& Axiom = Axioms_LibraryMap [ idx_UInt64 ];

                                    th_0000.UpdatePrimaryKey_LHS(
                                        Axiom.LHSPrimaryKey_UInt64, 
                                        Axiom.RHSPrimaryKey_UInt64);

                                    th_0000.LHSCallGraph_UInt64Map =
                                        Axiom.LHSCallGraph_UInt64Map;

                                    th_0000.LHSCallHistory [ RouteGoal_EnumClass :: _rhs ][ Axiom.guid ] = true;

                                    Tasks_Thread [ Write ].push_back( th_0000 );
                                }

                                if (idz_read_Flag)
                                {
                                    Theorem_Struct th_0001 = InTheorem;
                                    const Axiom_Struct& Axiom = Axioms_LibraryMap [ idz_UInt64 ];

                                    th_0001.UpdatePrimaryKey_RHS(
                                        Axiom.LHSPrimaryKey_UInt64, 
                                        Axiom.RHSPrimaryKey_UInt64);

                                    th_0001.RHSCallGraph_UInt64Map =
                                        Axiom.RHSCallGraph_UInt64Map;

                                    th_0001.RHSCallHistory [ RouteGoal_EnumClass :: _rhs ][ Axiom.guid ] = true;

                                    Tasks_Thread[ Write ].push_back( th_0001 );
                                }

                                if (idx_read_Flag &&
                                    idz_read_Flag)
                                {
                                    Theorem_Struct th_0002 = InTheorem;
                                    Theorem_Struct th_0003 = InTheorem;

                                    const Axiom_Struct& Axiom = Axioms_LibraryMap[idx_UInt64];
                                    const Axiom_Struct& Axiom = Axioms_LibraryMap[idx_UInt64];

                                    th_0002.UpdatePrimaryKey_LHS(
                                        Axiom.LHSPrimaryKey_UInt64,
                                        Axiom.RHSPrimaryKey_UInt64);
                                    th_0003.UpdatePrimaryKey_RHS(
                                        Axiom.LHSPrimaryKey_UInt64,
                                        Axiom.RHSPrimaryKey_UInt64);

                                    th_0002.LHSCallGraph_UInt64Map =
                                        Axiom.LHSCallGraph_UInt64Map;
                                    th_0003.RHSCallGraph_UInt64Map =
                                        Axiom.LHSCallGraph_UInt64Map;

                                    th_0002.LHSCallHistory[RouteGoal_EnumClass::_rhs][Axiom.guid] = true;
                                    th_0003.RHSCallHistory[RouteGoal_EnumClass::_rhs][Axiom.guid] = true;

                                    Tasks_Thread[Write].push_back(th_0002);
                                    Tasks_Thread[Write].push_back(th_0003);
                                }

                                // _expand

                                if (idw_read_Flag)
                                {
                                    Theorem_Struct th_0000 = InTheorem;
                                    const Axiom_Struct& Axiom = 
                                        Axioms_LibraryMap [ idw_UInt64 ];

                                    th_0000.UpdatePrimaryKey_LHS(
                                        Axiom.RHSPrimaryKey_UInt64, 
                                        Axiom.LHSPrimaryKey_UInt64);

                                    th_0000.LHSCallGraph_UInt64Map =
                                        Axiom.LHSCallGraph_UInt64Map;

                                    th_0000.LHSCallHistory [ RouteGoal_EnumClass :: _lhs ][ Axiom.guid ] = true;

                                    Tasks_Thread[Write].push_back(th_0000);
                                }

                                if (idy_read_Flag)
                                {
                                    Theorem_Struct th_0001 = InTheorem;
                                    const Axiom_Struct& Axiom = 
                                        Axioms_LibraryMap [ idy_UInt64 ];

                                    th_0001.UpdatePrimaryKey_RHS(
                                        Axiom.RHSPrimaryKey_UInt64,
                                        Axiom.LHSPrimaryKey_UInt64);

                                    th_0001.RHSCallGraph_UInt64Map =
                                        Axiom.RHSCallGraph_UInt64Map;

                                    th_0001.RHSCallHistory [ RouteGoal_EnumClass :: _lhs ][ Axiom.guid ] = true;

                                    Tasks_Thread [ Write ].push_back( th_0001 );
                                }

                                if (idw_read_Flag &&
                                    idy_read_Flag)
                                {
                                    Theorem_Struct th_0002 = InTheorem;
                                    Theorem_Struct th_0003 = InTheorem;

                                    const Axiom_Struct& Axiom_i =
                                        Axioms_LibraryMap[idw_UInt64];
                                    const Axiom_Struct& Axiom_j =
                                        Axioms_LibraryMap[idy_UInt64];

                                    th_0002.UpdatePrimaryKey_LHS(
                                        Axiom_i.RHSPrimaryKey_UInt64,
                                        Axiom_i.LHSPrimaryKey_UInt64);
                                    th_0003.UpdatePrimaryKey_RHS(
                                        Axiom_j.RHSPrimaryKey_UInt64,
                                        Axiom_j.LHSPrimaryKey_UInt64);

                                    th_0002.LHSCallGraph_UInt64Map =
                                        Axiom_i.LHSCallGraph_UInt64Map;
                                    th_0003.RHSCallGraph_UInt64Map =
                                        Axiom_j.RHSCallGraph_UInt64Map;

                                    th_0002.LHSCallHistory[RouteGoal_EnumClass::_lhs][Axiom_i.guid] = true;
                                    th_0003.RHSCallHistory[RouteGoal_EnumClass::_lhs][Axiom_j.guid] = true;

                                    Tasks_Thread[Write].push_back(th_0002);
                                    Tasks_Thread[Write].push_back(th_0003);
                                }
                            }
                        }
                    }
                }
            }

            else if (CallLHSRouteAll_Flag)
            {

            }

            else if (CallRHSRouteAll_Flag)
            {

            }

            else if (CallLHSRouteLHS_CallRHSRouteAll_Flag)
            {

            }

            else if (CallLHSRouteRHS_CallRHSRouteAll_Flag)
            {

            }

            else if (CallLHSRouteAll_CallRHSRouteLHS_Flag)
            {

            }

            else if (CallLHSRouteAll_CallRHSRouteRHS_Flag)
            {

            }

            else if (CallLHSRouteLHS_CallRHSRouteRHS_Flag)
            {

            }

            else if (CallLHSRouteRHS_CallRHSRouteLHS_Flag)
            {

            }

            else if (CallLHSRouteLHS_CallRHSRouteLHS_Flag)
            {
                // no solution //
                continue;
            }

            else if (CallLHSRouteRHS_CallRHSRouteRHS_Flag)
            {

            }
            break;

        case Indirection_EnumClass::_expand:
            if (CallLHSRouteLHS_Flag)
            {

            }

            else if (CallLHSRouteRHS_Flag)
            {
                // no solution //
                continue;
            }

            else if (CallRHSRouteLHS_Flag)
            {

            }

            else if (CallRHSRouteRHS_Flag)
            {
                // no solution //
                continue;
            }

            else if (CallAllRouteAll_Flag)
            {

            }

            else if (CallLHSRouteAll_Flag)
            {

            }

            else if (CallRHSRouteAll_Flag)
            {

            }

            else if (CallLHSRouteLHS_CallRHSRouteAll_Flag)
            {

            }

            else if (CallLHSRouteRHS_CallRHSRouteAll_Flag)
            {

            }

            else if (CallLHSRouteAll_CallRHSRouteLHS_Flag)
            {

            }

            else if (CallLHSRouteAll_CallRHSRouteRHS_Flag)
            {

            }

            else if (CallLHSRouteLHS_CallRHSRouteRHS_Flag)
            {

            }

            else if (CallLHSRouteRHS_CallRHSRouteLHS_Flag)
            {

            }

            else if (CallLHSRouteLHS_CallRHSRouteLHS_Flag)
            {

            }

            else if (CallLHSRouteRHS_CallRHSRouteRHS_Flag)
            {
                // no solution //
                continue;
            }
            break;

        case Indirection_EnumClass::_auto:
        default:
            if (CallLHSRouteLHS_Flag)
            {

            }

            else if (CallLHSRouteRHS_Flag)
            {

            }

            else if (CallRHSRouteLHS_Flag)
            {

            }

            else if (CallRHSRouteRHS_Flag)
            {

            }

            else if (CallAllRouteAll_Flag)
            {

            }

            else if (CallLHSRouteAll_Flag)
            {

            }

            else if (CallRHSRouteAll_Flag)
            {

            }

            else if (CallLHSRouteLHS_CallRHSRouteAll_Flag)
            {

            }

            else if (CallLHSRouteRHS_CallRHSRouteAll_Flag)
            {

            }

            else if (CallLHSRouteAll_CallRHSRouteLHS_Flag)
            {

            }

            else if (CallLHSRouteAll_CallRHSRouteRHS_Flag)
            {

            }

            else if (CallLHSRouteLHS_CallRHSRouteRHS_Flag)
            {

            }

            else if (CallLHSRouteRHS_CallRHSRouteLHS_Flag)
            {

            }

            else if (CallLHSRouteLHS_CallRHSRouteLHS_Flag)
            {

            }

            else if (CallLHSRouteRHS_CallRHSRouteRHS_Flag)
            {

            }
            break;
        }

    } // for(_ : Tasks_Thread [ read ])

    Tasks_Thread[Read] = {};

    Read = Round.NextRound_UInt8();
    //}

    return EXIT_SUCCESS;
}
