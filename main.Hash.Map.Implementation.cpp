
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
    Consider "{ PlayerCharacterSideKick } IsIn { StyxBoat }" where the IsIn operator may or may not link unrelated categories,
    versus "{ PlayerCharacterSideKick } IsIn_StyxBoat " which is guaranteed to converge !!!

  Usage Example. // Lemma substitution //

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
#include <future>
#include <atomic>
#include <cstdint>
#include <unordered_map>
#include <functional>
#include <mutex>
#include <vector>
#include <string>
#include <sstream>
#include <algorithm>
#include <iterator>
#include <chrono>
#include <cstdlib>
#include <execution>
#include <array>

std::mutex mtx;

uint64_t GUID = 0;

std::array<uint64_t,0> Axioms_Vec;

const std::size_t num_threads = std::thread::hardware_concurrency() - 1; // Minus the main thread

class RecursionLimiter
{
public:
    static void set_recursion_limit(uint64_t limit)
    {
        recursion_limit = limit;
    }

    class Invoke
    {
    public:
        Invoke(uint64_t initial_depth)
            : depth(initial_depth),
            recursion_count(thread_local_recursion_count())
        {
            if (depth)
            {
                *recursion_count += depth;
            }
        }

        ~Invoke()
        {
            if (recursion_count)
            {
                *recursion_count -= depth;
            }
        }

        bool acquired()
        {
            if (!recursion_count)
            {
                recursion_count = thread_local_recursion_count();
                return true;
            }

            if (*recursion_count + depth < recursion_limit)
            {
                *recursion_count += depth;
                return true;
            }

            return false;
        }

        bool release()
        {
            bool retval{};

            if (recursion_count)
            {
                *recursion_count -= depth;
                retval = true;
            }

            return retval;
        }

    private:
        uint64_t depth;
        std::atomic<uint64_t>* thread_local_recursion_count()
        {
            thread_local std::atomic<uint64_t> rc{ 0 };
            return &rc;
        }

        std::atomic<uint64_t>* recursion_count;
    };

private:
    static inline std::atomic<uint64_t> recursion_limit;
};

enum class RouteSource_EnumClass : int
{
    _lhs,
    _rhs,
    _root
};

enum class Indirection_EnumClass : int
{
    _auto = 10000,
    _reduce,
    _expand
};

struct AxiomProto_Struct
{
    uint64_t LHSPrimaryKey_UInt64{};
    uint64_t RHSPrimaryKey_UInt64{};

    std::vector<std::string> LHS_StdStrVec;
    std::vector<std::string> RHS_StdStrVec;

    std::unordered_map<uint64_t, bool> LHSCallHistory;
    std::unordered_map<uint64_t, bool> RHSCallHistory;

    std::unordered_map<RouteSource_EnumClass,
        std::unordered_map<uint64_t, bool>>
        LHSCallGraph_UInt64Map;

    std::unordered_map<RouteSource_EnumClass,
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

// Auto[ProofFound_Flag][ProofsFoundGreaterEqualToMaxAllowedProofs_Flag][RouteSource_EnumClass][Indirection_EnumClass]
std::unordered_map <bool, 
    std::unordered_map <bool, 
        std::unordered_map <RouteSource_EnumClass, 
            std::unordered_map <Indirection_EnumClass, 
                std::function<void(Theorem_Struct, const Axiom_Struct&)>>>>> Auto;

Auto
[false]
[false]
[RouteSource_EnumClass::_root]
[Indirection_EnumClass::_auto] =
[](Theorem_Struct InTheorem, const Axiom_Struct& InAxiom) -> void
{
    InTheorem.ProofStack_VecUInt64.push_back(InAxiom);

    if (InTheorem.LHSPrimaryKey_UInt64 == InTheorem.RHSPrimaryKey_UInt64)
    {
        InTheorem.ProofFound_Flag = true;
        ++InTheorem.TotalProofsFound_UInt64;
    }

    if (InTheorem.TotalProofsFound_UInt64 >= InTheorem.MaxAllowedProofs_UInt64)
        return;

    Theorem_Struct TheoremProto_0000 = InTheorem;
    Theorem_Struct TheoremProto_0001 = InTheorem;
    Theorem_Struct TheoremProto_0002 = InTheorem;
    Theorem_Struct TheoremProto_0003 = InTheorem;
    Theorem_Struct TheoremProto_0004 = InTheorem;
    Theorem_Struct TheoremProto_0005 = InTheorem;

    if (TheoremProto_0000.SubnetFound_LHS(InAxiom.LHSPrimaryKey_UInt64))
        TheoremProto_0000.UpdatePrimaryKey_LHS(InAxiom.LHSPrimaryKey_UInt64);

    TheoremProto_0001.UpdatePrimaryKey_RHS(InAxiom.LHSPrimaryKey_UInt64);
    TheoremProto_0002.UpdatePrimaryKey_LHS(InAxiom.LHSPrimaryKey_UInt64);
    TheoremProto_0002.UpdatePrimaryKey_RHS(InAxiom.RHSPrimaryKey_UInt64);

    TheoremProto_0003.UpdatePrimaryKey_LHS(InAxiom.RHSPrimaryKey_UInt64);
    TheoremProto_0004.UpdatePrimaryKey_RHS(InAxiom.RHSPrimaryKey_UInt64);
    TheoremProto_0005.UpdatePrimaryKey_LHS(InAxiom.RHSPrimaryKey_UInt64);
    TheoremProto_0005.UpdatePrimaryKey_RHS(InAxiom.LHSPrimaryKey_UInt64);

    std::for_each(std::execution::par_unseq,
        Axioms_Vec.begin(),
        Axioms_Vec.end(),
        [&](const Axiom_Struct& Axiom)
        {
            RecursionLimiter::Invoke limiter(6);
            if (limiter.acquired())
            {
                Auto
                [TheoremProto_0000.LHSPrimaryKey_UInt64 == TheoremProto_0000.RHSPrimaryKey_UInt64]
                [TheoremProto_0000.TotalProofsFound_UInt64 >= TheoremProto_0000.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0000, Axiom);

                Auto
                [TheoremProto_0000.LHSPrimaryKey_UInt64 == TheoremProto_0000.RHSPrimaryKey_UInt64]
                [TheoremProto_0000.TotalProofsFound_UInt64 >= TheoremProto_0000.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0000, Axiom);

                Auto
                [TheoremProto_0001.LHSPrimaryKey_UInt64 == TheoremProto_0001.RHSPrimaryKey_UInt64]
                [TheoremProto_0001.TotalProofsFound_UInt64 >= TheoremProto_0001.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0001, Axiom);

                Auto
                [TheoremProto_0001.LHSPrimaryKey_UInt64 == TheoremProto_0001.RHSPrimaryKey_UInt64]
                [TheoremProto_0001.TotalProofsFound_UInt64 >= TheoremProto_0001.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0001, Axiom);

                Auto
                [TheoremProto_0002.LHSPrimaryKey_UInt64 == TheoremProto_0002.RHSPrimaryKey_UInt64]
                [TheoremProto_0002.TotalProofsFound_UInt64 >= TheoremProto_0002.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0002, Axiom);

                Auto
                [TheoremProto_0002.LHSPrimaryKey_UInt64 == TheoremProto_0002.RHSPrimaryKey_UInt64]
                [TheoremProto_0002.TotalProofsFound_UInt64 >= TheoremProto_0002.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0002, Axiom);

                limiter.release();
            }

        });

    std::for_each(std::execution::par_unseq,
        Axioms_Vec.begin(),
        Axioms_Vec.end(),
        [&](const Axiom_Struct& Axiom)
        {
            RecursionLimiter::Invoke limiter(6);
            if (limiter.acquired())
            {
                Auto
                [TheoremProto_0003.LHSPrimaryKey_UInt64 == TheoremProto_0003.RHSPrimaryKey_UInt64]
                [TheoremProto_0003.TotalProofsFound_UInt64 >= TheoremProto_0003.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0003, Axiom);

                Auto
                [TheoremProto_0003.LHSPrimaryKey_UInt64 == TheoremProto_0003.RHSPrimaryKey_UInt64]
                [TheoremProto_0003.TotalProofsFound_UInt64 >= TheoremProto_0003.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0003, Axiom);

                Auto
                [TheoremProto_0004.LHSPrimaryKey_UInt64 == TheoremProto_0004.RHSPrimaryKey_UInt64]
                [TheoremProto_0004.TotalProofsFound_UInt64 >= TheoremProto_0004.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0004, Axiom);

                Auto
                [TheoremProto_0004.LHSPrimaryKey_UInt64 == TheoremProto_0004.RHSPrimaryKey_UInt64]
                [TheoremProto_0004.TotalProofsFound_UInt64 >= TheoremProto_0004.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0004, Axiom);

                Auto
                [TheoremProto_0005.LHSPrimaryKey_UInt64 == TheoremProto_0005.RHSPrimaryKey_UInt64]
                [TheoremProto_0005.TotalProofsFound_UInt64 >= TheoremProto_0005.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0005, Axiom);

                Auto
                [TheoremProto_0005.LHSPrimaryKey_UInt64 == TheoremProto_0005.RHSPrimaryKey_UInt64]
                [TheoremProto_0005.TotalProofsFound_UInt64 >= TheoremProto_0005.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0005, Axiom);

                limiter.release();
            }

        });

    std::for_each(std::execution::par_unseq,
        Axioms_Vec.begin(),
        Axioms_Vec.end(),
        [&](const Axiom_Struct& Axiom)
        {
            RecursionLimiter::Invoke limiter(12);
            if (limiter.acquired())
            {
                Auto
                [TheoremProto_0000.LHSPrimaryKey_UInt64 == TheoremProto_0000.RHSPrimaryKey_UInt64]
                [TheoremProto_0000.TotalProofsFound_UInt64 >= TheoremProto_0000.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0000, Axiom);

                Auto
                [TheoremProto_0000.LHSPrimaryKey_UInt64 == TheoremProto_0000.RHSPrimaryKey_UInt64]
                [TheoremProto_0000.TotalProofsFound_UInt64 >= TheoremProto_0000.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0000, Axiom);

                Auto
                [TheoremProto_0001.LHSPrimaryKey_UInt64 == TheoremProto_0001.RHSPrimaryKey_UInt64]
                [TheoremProto_0001.TotalProofsFound_UInt64 >= TheoremProto_0001.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0001, Axiom);

                Auto
                [TheoremProto_0001.LHSPrimaryKey_UInt64 == TheoremProto_0001.RHSPrimaryKey_UInt64]
                [TheoremProto_0001.TotalProofsFound_UInt64 >= TheoremProto_0001.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0001, Axiom);

                Auto
                [TheoremProto_0002.LHSPrimaryKey_UInt64 == TheoremProto_0002.RHSPrimaryKey_UInt64]
                [TheoremProto_0002.TotalProofsFound_UInt64 >= TheoremProto_0002.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0002, Axiom);

                Auto
                [TheoremProto_0002.LHSPrimaryKey_UInt64 == TheoremProto_0002.RHSPrimaryKey_UInt64]
                [TheoremProto_0002.TotalProofsFound_UInt64 >= TheoremProto_0002.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0002, Axiom);


                Auto
                [TheoremProto_0003.LHSPrimaryKey_UInt64 == TheoremProto_0003.RHSPrimaryKey_UInt64]
                [TheoremProto_0003.TotalProofsFound_UInt64 >= TheoremProto_0003.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0003, Axiom);

                Auto
                [TheoremProto_0003.LHSPrimaryKey_UInt64 == TheoremProto_0003.RHSPrimaryKey_UInt64]
                [TheoremProto_0003.TotalProofsFound_UInt64 >= TheoremProto_0003.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0003, Axiom);

                Auto
                [TheoremProto_0004.LHSPrimaryKey_UInt64 == TheoremProto_0004.RHSPrimaryKey_UInt64]
                [TheoremProto_0004.TotalProofsFound_UInt64 >= TheoremProto_0004.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0004, Axiom);

                Auto
                [TheoremProto_0004.LHSPrimaryKey_UInt64 == TheoremProto_0004.RHSPrimaryKey_UInt64]
                [TheoremProto_0004.TotalProofsFound_UInt64 >= TheoremProto_0004.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0004, Axiom);

                Auto
                [TheoremProto_0005.LHSPrimaryKey_UInt64 == TheoremProto_0005.RHSPrimaryKey_UInt64]
                [TheoremProto_0005.TotalProofsFound_UInt64 >= TheoremProto_0005.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0005, Axiom);

                Auto
                [TheoremProto_0005.LHSPrimaryKey_UInt64 == TheoremProto_0005.RHSPrimaryKey_UInt64]
                [TheoremProto_0005.TotalProofsFound_UInt64 >= TheoremProto_0005.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0005, Axiom);

                limiter.release();
            }

        });

};

Auto
[false]
[false]
[RouteSource_EnumClass::_root]
[Indirection_EnumClass::_reduce] =
[](Theorem_Struct InTheorem, const Axiom_Struct& InAxiom) -> void
{
    InTheorem.ProofStack_VecUInt64.push_back(InAxiom);

    if (InTheorem.LHSPrimaryKey_UInt64 == InTheorem.RHSPrimaryKey_UInt64)
    {
        InTheorem.ProofFound_Flag = true;
        ++InTheorem.TotalProofsFound_UInt64;
    }

    if (InTheorem.TotalProofsFound_UInt64 >= InTheorem.MaxAllowedProofs_UInt64)
        return;

    Theorem_Struct TheoremProto_0000 = InTheorem;
    Theorem_Struct TheoremProto_0001 = InTheorem;
    Theorem_Struct TheoremProto_0002 = InTheorem;
    Theorem_Struct TheoremProto_0003 = InTheorem;
    Theorem_Struct TheoremProto_0004 = InTheorem;
    Theorem_Struct TheoremProto_0005 = InTheorem;

    if (TheoremProto_0000.SubnetFound_LHS(InAxiom.LHSPrimaryKey_UInt64))
        TheoremProto_0000.UpdatePrimaryKey_LHS(InAxiom.LHSPrimaryKey_UInt64);

    TheoremProto_0001.UpdatePrimaryKey_RHS(InAxiom.LHSPrimaryKey_UInt64);
    TheoremProto_0002.UpdatePrimaryKey_LHS(InAxiom.LHSPrimaryKey_UInt64);
    TheoremProto_0002.UpdatePrimaryKey_RHS(InAxiom.RHSPrimaryKey_UInt64);

    TheoremProto_0003.UpdatePrimaryKey_LHS(InAxiom.RHSPrimaryKey_UInt64);
    TheoremProto_0004.UpdatePrimaryKey_RHS(InAxiom.RHSPrimaryKey_UInt64);
    TheoremProto_0005.UpdatePrimaryKey_LHS(InAxiom.RHSPrimaryKey_UInt64);
    TheoremProto_0005.UpdatePrimaryKey_RHS(InAxiom.LHSPrimaryKey_UInt64);

    std::for_each(std::execution::par_unseq,
        Axioms_Vec.begin(),
        Axioms_Vec.end(),
        [&](const Axiom_Struct& Axiom)
        {
            RecursionLimiter::Invoke limiter(6);
            if (limiter.acquired())
            {
                Auto
                [TheoremProto_0000.LHSPrimaryKey_UInt64 == TheoremProto_0000.RHSPrimaryKey_UInt64]
                [TheoremProto_0000.TotalProofsFound_UInt64 >= TheoremProto_0000.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0000, Axiom);

                Auto
                [TheoremProto_0000.LHSPrimaryKey_UInt64 == TheoremProto_0000.RHSPrimaryKey_UInt64]
                [TheoremProto_0000.TotalProofsFound_UInt64 >= TheoremProto_0000.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0000, Axiom);

                Auto
                [TheoremProto_0001.LHSPrimaryKey_UInt64 == TheoremProto_0001.RHSPrimaryKey_UInt64]
                [TheoremProto_0001.TotalProofsFound_UInt64 >= TheoremProto_0001.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0001, Axiom);

                Auto
                [TheoremProto_0001.LHSPrimaryKey_UInt64 == TheoremProto_0001.RHSPrimaryKey_UInt64]
                [TheoremProto_0001.TotalProofsFound_UInt64 >= TheoremProto_0001.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0001, Axiom);

                Auto
                [TheoremProto_0002.LHSPrimaryKey_UInt64 == TheoremProto_0002.RHSPrimaryKey_UInt64]
                [TheoremProto_0002.TotalProofsFound_UInt64 >= TheoremProto_0002.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0002, Axiom);

                Auto
                [TheoremProto_0002.LHSPrimaryKey_UInt64 == TheoremProto_0002.RHSPrimaryKey_UInt64]
                [TheoremProto_0002.TotalProofsFound_UInt64 >= TheoremProto_0002.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0002, Axiom);

                limiter.release();
            }

        });

    std::for_each(std::execution::par_unseq,
        Axioms_Vec.begin(),
        Axioms_Vec.end(),
        [&](const Axiom_Struct& Axiom)
        {
            RecursionLimiter::Invoke limiter(6);
            if (limiter.acquired())
            {
                Auto
                [TheoremProto_0003.LHSPrimaryKey_UInt64 == TheoremProto_0003.RHSPrimaryKey_UInt64]
                [TheoremProto_0003.TotalProofsFound_UInt64 >= TheoremProto_0003.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0003, Axiom);

                Auto
                [TheoremProto_0003.LHSPrimaryKey_UInt64 == TheoremProto_0003.RHSPrimaryKey_UInt64]
                [TheoremProto_0003.TotalProofsFound_UInt64 >= TheoremProto_0003.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0003, Axiom);

                Auto
                [TheoremProto_0004.LHSPrimaryKey_UInt64 == TheoremProto_0004.RHSPrimaryKey_UInt64]
                [TheoremProto_0004.TotalProofsFound_UInt64 >= TheoremProto_0004.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0004, Axiom);

                Auto
                [TheoremProto_0004.LHSPrimaryKey_UInt64 == TheoremProto_0004.RHSPrimaryKey_UInt64]
                [TheoremProto_0004.TotalProofsFound_UInt64 >= TheoremProto_0004.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0004, Axiom);

                Auto
                [TheoremProto_0005.LHSPrimaryKey_UInt64 == TheoremProto_0005.RHSPrimaryKey_UInt64]
                [TheoremProto_0005.TotalProofsFound_UInt64 >= TheoremProto_0005.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0005, Axiom);

                Auto
                [TheoremProto_0005.LHSPrimaryKey_UInt64 == TheoremProto_0005.RHSPrimaryKey_UInt64]
                [TheoremProto_0005.TotalProofsFound_UInt64 >= TheoremProto_0005.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0005, Axiom);

                limiter.release();
            }

        });

    std::for_each(std::execution::par_unseq,
        Axioms_Vec.begin(),
        Axioms_Vec.end(),
        [&](const Axiom_Struct& Axiom)
        {
            RecursionLimiter::Invoke limiter(12);
            if (limiter.acquired())
            {
                Auto
                [TheoremProto_0000.LHSPrimaryKey_UInt64 == TheoremProto_0000.RHSPrimaryKey_UInt64]
                [TheoremProto_0000.TotalProofsFound_UInt64 >= TheoremProto_0000.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0000, Axiom);

                Auto
                [TheoremProto_0000.LHSPrimaryKey_UInt64 == TheoremProto_0000.RHSPrimaryKey_UInt64]
                [TheoremProto_0000.TotalProofsFound_UInt64 >= TheoremProto_0000.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0000, Axiom);

                Auto
                [TheoremProto_0001.LHSPrimaryKey_UInt64 == TheoremProto_0001.RHSPrimaryKey_UInt64]
                [TheoremProto_0001.TotalProofsFound_UInt64 >= TheoremProto_0001.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0001, Axiom);

                Auto
                [TheoremProto_0001.LHSPrimaryKey_UInt64 == TheoremProto_0001.RHSPrimaryKey_UInt64]
                [TheoremProto_0001.TotalProofsFound_UInt64 >= TheoremProto_0001.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0001, Axiom);

                Auto
                [TheoremProto_0002.LHSPrimaryKey_UInt64 == TheoremProto_0002.RHSPrimaryKey_UInt64]
                [TheoremProto_0002.TotalProofsFound_UInt64 >= TheoremProto_0002.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0002, Axiom);

                Auto
                [TheoremProto_0002.LHSPrimaryKey_UInt64 == TheoremProto_0002.RHSPrimaryKey_UInt64]
                [TheoremProto_0002.TotalProofsFound_UInt64 >= TheoremProto_0002.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0002, Axiom);


                Auto
                [TheoremProto_0003.LHSPrimaryKey_UInt64 == TheoremProto_0003.RHSPrimaryKey_UInt64]
                [TheoremProto_0003.TotalProofsFound_UInt64 >= TheoremProto_0003.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0003, Axiom);

                Auto
                [TheoremProto_0003.LHSPrimaryKey_UInt64 == TheoremProto_0003.RHSPrimaryKey_UInt64]
                [TheoremProto_0003.TotalProofsFound_UInt64 >= TheoremProto_0003.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0003, Axiom);

                Auto
                [TheoremProto_0004.LHSPrimaryKey_UInt64 == TheoremProto_0004.RHSPrimaryKey_UInt64]
                [TheoremProto_0004.TotalProofsFound_UInt64 >= TheoremProto_0004.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0004, Axiom);

                Auto
                [TheoremProto_0004.LHSPrimaryKey_UInt64 == TheoremProto_0004.RHSPrimaryKey_UInt64]
                [TheoremProto_0004.TotalProofsFound_UInt64 >= TheoremProto_0004.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0004, Axiom);

                Auto
                [TheoremProto_0005.LHSPrimaryKey_UInt64 == TheoremProto_0005.RHSPrimaryKey_UInt64]
                [TheoremProto_0005.TotalProofsFound_UInt64 >= TheoremProto_0005.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0005, Axiom);

                Auto
                [TheoremProto_0005.LHSPrimaryKey_UInt64 == TheoremProto_0005.RHSPrimaryKey_UInt64]
                [TheoremProto_0005.TotalProofsFound_UInt64 >= TheoremProto_0005.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0005, Axiom);

                limiter.release();
            }

        });

};

Auto
[false]
[false]
[RouteSource_EnumClass::_root]
[Indirection_EnumClass::_expand] =
[](Theorem_Struct InTheorem, const Axiom_Struct& InAxiom) -> void
{
    InTheorem.ProofStack_VecUInt64.push_back(InAxiom);

    if (InTheorem.LHSPrimaryKey_UInt64 == InTheorem.RHSPrimaryKey_UInt64)
    {
        InTheorem.ProofFound_Flag = true;
        ++InTheorem.TotalProofsFound_UInt64;
    }

    if (InTheorem.TotalProofsFound_UInt64 >= InTheorem.MaxAllowedProofs_UInt64)
        return;

    Theorem_Struct TheoremProto_0000 = InTheorem;
    Theorem_Struct TheoremProto_0001 = InTheorem;
    Theorem_Struct TheoremProto_0002 = InTheorem;
    Theorem_Struct TheoremProto_0003 = InTheorem;
    Theorem_Struct TheoremProto_0004 = InTheorem;
    Theorem_Struct TheoremProto_0005 = InTheorem;

    if (TheoremProto_0000.SubnetFound_LHS(InAxiom.LHSPrimaryKey_UInt64))
        TheoremProto_0000.UpdatePrimaryKey_LHS(InAxiom.LHSPrimaryKey_UInt64);

    TheoremProto_0001.UpdatePrimaryKey_RHS(InAxiom.LHSPrimaryKey_UInt64);
    TheoremProto_0002.UpdatePrimaryKey_LHS(InAxiom.LHSPrimaryKey_UInt64);
    TheoremProto_0002.UpdatePrimaryKey_RHS(InAxiom.RHSPrimaryKey_UInt64);

    TheoremProto_0003.UpdatePrimaryKey_LHS(InAxiom.RHSPrimaryKey_UInt64);
    TheoremProto_0004.UpdatePrimaryKey_RHS(InAxiom.RHSPrimaryKey_UInt64);
    TheoremProto_0005.UpdatePrimaryKey_LHS(InAxiom.RHSPrimaryKey_UInt64);
    TheoremProto_0005.UpdatePrimaryKey_RHS(InAxiom.LHSPrimaryKey_UInt64);

    std::for_each(std::execution::par_unseq,
        Axioms_Vec.begin(),
        Axioms_Vec.end(),
        [&](const Axiom_Struct& Axiom)
        {
            RecursionLimiter::Invoke limiter(6);
            if (limiter.acquired())
            {
                Auto
                [TheoremProto_0000.LHSPrimaryKey_UInt64 == TheoremProto_0000.RHSPrimaryKey_UInt64]
                [TheoremProto_0000.TotalProofsFound_UInt64 >= TheoremProto_0000.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0000, Axiom);

                Auto
                [TheoremProto_0000.LHSPrimaryKey_UInt64 == TheoremProto_0000.RHSPrimaryKey_UInt64]
                [TheoremProto_0000.TotalProofsFound_UInt64 >= TheoremProto_0000.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0000, Axiom);

                Auto
                [TheoremProto_0001.LHSPrimaryKey_UInt64 == TheoremProto_0001.RHSPrimaryKey_UInt64]
                [TheoremProto_0001.TotalProofsFound_UInt64 >= TheoremProto_0001.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0001, Axiom);

                Auto
                [TheoremProto_0001.LHSPrimaryKey_UInt64 == TheoremProto_0001.RHSPrimaryKey_UInt64]
                [TheoremProto_0001.TotalProofsFound_UInt64 >= TheoremProto_0001.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0001, Axiom);

                Auto
                [TheoremProto_0002.LHSPrimaryKey_UInt64 == TheoremProto_0002.RHSPrimaryKey_UInt64]
                [TheoremProto_0002.TotalProofsFound_UInt64 >= TheoremProto_0002.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0002, Axiom);

                Auto
                [TheoremProto_0002.LHSPrimaryKey_UInt64 == TheoremProto_0002.RHSPrimaryKey_UInt64]
                [TheoremProto_0002.TotalProofsFound_UInt64 >= TheoremProto_0002.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0002, Axiom);

                limiter.release();
            }

        });

    std::for_each(std::execution::par_unseq,
        Axioms_Vec.begin(),
        Axioms_Vec.end(),
        [&](const Axiom_Struct& Axiom)
        {
            RecursionLimiter::Invoke limiter(6);
            if (limiter.acquired())
            {
                Auto
                [TheoremProto_0003.LHSPrimaryKey_UInt64 == TheoremProto_0003.RHSPrimaryKey_UInt64]
                [TheoremProto_0003.TotalProofsFound_UInt64 >= TheoremProto_0003.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0003, Axiom);

                Auto
                [TheoremProto_0003.LHSPrimaryKey_UInt64 == TheoremProto_0003.RHSPrimaryKey_UInt64]
                [TheoremProto_0003.TotalProofsFound_UInt64 >= TheoremProto_0003.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0003, Axiom);

                Auto
                [TheoremProto_0004.LHSPrimaryKey_UInt64 == TheoremProto_0004.RHSPrimaryKey_UInt64]
                [TheoremProto_0004.TotalProofsFound_UInt64 >= TheoremProto_0004.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0004, Axiom);

                Auto
                [TheoremProto_0004.LHSPrimaryKey_UInt64 == TheoremProto_0004.RHSPrimaryKey_UInt64]
                [TheoremProto_0004.TotalProofsFound_UInt64 >= TheoremProto_0004.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0004, Axiom);

                Auto
                [TheoremProto_0005.LHSPrimaryKey_UInt64 == TheoremProto_0005.RHSPrimaryKey_UInt64]
                [TheoremProto_0005.TotalProofsFound_UInt64 >= TheoremProto_0005.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0005, Axiom);

                Auto
                [TheoremProto_0005.LHSPrimaryKey_UInt64 == TheoremProto_0005.RHSPrimaryKey_UInt64]
                [TheoremProto_0005.TotalProofsFound_UInt64 >= TheoremProto_0005.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0005, Axiom);

                limiter.release();
            }

        });

    std::for_each(std::execution::par_unseq,
        Axioms_Vec.begin(),
        Axioms_Vec.end(),
        [&](const Axiom_Struct& Axiom)
        {
            RecursionLimiter::Invoke limiter(12);
            if (limiter.acquired())
            {
                Auto
                [TheoremProto_0000.LHSPrimaryKey_UInt64 == TheoremProto_0000.RHSPrimaryKey_UInt64]
                [TheoremProto_0000.TotalProofsFound_UInt64 >= TheoremProto_0000.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0000, Axiom);

                Auto
                [TheoremProto_0000.LHSPrimaryKey_UInt64 == TheoremProto_0000.RHSPrimaryKey_UInt64]
                [TheoremProto_0000.TotalProofsFound_UInt64 >= TheoremProto_0000.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0000, Axiom);

                Auto
                [TheoremProto_0001.LHSPrimaryKey_UInt64 == TheoremProto_0001.RHSPrimaryKey_UInt64]
                [TheoremProto_0001.TotalProofsFound_UInt64 >= TheoremProto_0001.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0001, Axiom);

                Auto
                [TheoremProto_0001.LHSPrimaryKey_UInt64 == TheoremProto_0001.RHSPrimaryKey_UInt64]
                [TheoremProto_0001.TotalProofsFound_UInt64 >= TheoremProto_0001.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0001, Axiom);

                Auto
                [TheoremProto_0002.LHSPrimaryKey_UInt64 == TheoremProto_0002.RHSPrimaryKey_UInt64]
                [TheoremProto_0002.TotalProofsFound_UInt64 >= TheoremProto_0002.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0002, Axiom);

                Auto
                [TheoremProto_0002.LHSPrimaryKey_UInt64 == TheoremProto_0002.RHSPrimaryKey_UInt64]
                [TheoremProto_0002.TotalProofsFound_UInt64 >= TheoremProto_0002.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0002, Axiom);


                Auto
                [TheoremProto_0003.LHSPrimaryKey_UInt64 == TheoremProto_0003.RHSPrimaryKey_UInt64]
                [TheoremProto_0003.TotalProofsFound_UInt64 >= TheoremProto_0003.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0003, Axiom);

                Auto
                [TheoremProto_0003.LHSPrimaryKey_UInt64 == TheoremProto_0003.RHSPrimaryKey_UInt64]
                [TheoremProto_0003.TotalProofsFound_UInt64 >= TheoremProto_0003.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0003, Axiom);

                Auto
                [TheoremProto_0004.LHSPrimaryKey_UInt64 == TheoremProto_0004.RHSPrimaryKey_UInt64]
                [TheoremProto_0004.TotalProofsFound_UInt64 >= TheoremProto_0004.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0004, Axiom);

                Auto
                [TheoremProto_0004.LHSPrimaryKey_UInt64 == TheoremProto_0004.RHSPrimaryKey_UInt64]
                [TheoremProto_0004.TotalProofsFound_UInt64 >= TheoremProto_0004.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0004, Axiom);

                Auto
                [TheoremProto_0005.LHSPrimaryKey_UInt64 == TheoremProto_0005.RHSPrimaryKey_UInt64]
                [TheoremProto_0005.TotalProofsFound_UInt64 >= TheoremProto_0005.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0005, Axiom);

                Auto
                [TheoremProto_0005.LHSPrimaryKey_UInt64 == TheoremProto_0005.RHSPrimaryKey_UInt64]
                [TheoremProto_0005.TotalProofsFound_UInt64 >= TheoremProto_0005.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0005, Axiom);

                limiter.release();
            }

        });

};

Auto
[false]
[false]
[RouteSource_EnumClass::_lhs]
[Indirection_EnumClass::_auto] =
[](Theorem_Struct InTheorem, const Axiom_Struct& InAxiom) -> void
{
    InTheorem.ProofStack_VecUInt64.push_back(InAxiom);

    if (InTheorem.LHSPrimaryKey_UInt64 == InTheorem.RHSPrimaryKey_UInt64)
    {
        InTheorem.ProofFound_Flag = true;
        ++InTheorem.TotalProofsFound_UInt64;
    }

    if (InTheorem.TotalProofsFound_UInt64 >= InTheorem.MaxAllowedProofs_UInt64)
        return;

    Theorem_Struct TheoremProto_0000 = InTheorem;
    Theorem_Struct TheoremProto_0001 = InTheorem;
    Theorem_Struct TheoremProto_0002 = InTheorem;
    Theorem_Struct TheoremProto_0003 = InTheorem;
    Theorem_Struct TheoremProto_0004 = InTheorem;
    Theorem_Struct TheoremProto_0005 = InTheorem;

    if (TheoremProto_0000.SubnetFound_LHS(InAxiom.LHSPrimaryKey_UInt64))
        TheoremProto_0000.UpdatePrimaryKey_LHS(InAxiom.LHSPrimaryKey_UInt64);

    TheoremProto_0001.UpdatePrimaryKey_RHS(InAxiom.LHSPrimaryKey_UInt64);
    TheoremProto_0002.UpdatePrimaryKey_LHS(InAxiom.LHSPrimaryKey_UInt64);
    TheoremProto_0002.UpdatePrimaryKey_RHS(InAxiom.RHSPrimaryKey_UInt64);

    TheoremProto_0003.UpdatePrimaryKey_LHS(InAxiom.RHSPrimaryKey_UInt64);
    TheoremProto_0004.UpdatePrimaryKey_RHS(InAxiom.RHSPrimaryKey_UInt64);
    TheoremProto_0005.UpdatePrimaryKey_LHS(InAxiom.RHSPrimaryKey_UInt64);
    TheoremProto_0005.UpdatePrimaryKey_RHS(InAxiom.LHSPrimaryKey_UInt64);

    std::for_each(std::execution::par_unseq,
        Axioms_Vec.begin(),
        Axioms_Vec.end(),
        [&](const Axiom_Struct& Axiom)
        {
            RecursionLimiter::Invoke limiter(6);
            if (limiter.acquired())
            {
                Auto
                [TheoremProto_0000.LHSPrimaryKey_UInt64 == TheoremProto_0000.RHSPrimaryKey_UInt64]
                [TheoremProto_0000.TotalProofsFound_UInt64 >= TheoremProto_0000.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0000, Axiom);

                Auto
                [TheoremProto_0000.LHSPrimaryKey_UInt64 == TheoremProto_0000.RHSPrimaryKey_UInt64]
                [TheoremProto_0000.TotalProofsFound_UInt64 >= TheoremProto_0000.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0000, Axiom);

                Auto
                [TheoremProto_0001.LHSPrimaryKey_UInt64 == TheoremProto_0001.RHSPrimaryKey_UInt64]
                [TheoremProto_0001.TotalProofsFound_UInt64 >= TheoremProto_0001.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0001, Axiom);

                Auto
                [TheoremProto_0001.LHSPrimaryKey_UInt64 == TheoremProto_0001.RHSPrimaryKey_UInt64]
                [TheoremProto_0001.TotalProofsFound_UInt64 >= TheoremProto_0001.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0001, Axiom);

                Auto
                [TheoremProto_0002.LHSPrimaryKey_UInt64 == TheoremProto_0002.RHSPrimaryKey_UInt64]
                [TheoremProto_0002.TotalProofsFound_UInt64 >= TheoremProto_0002.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0002, Axiom);

                Auto
                [TheoremProto_0002.LHSPrimaryKey_UInt64 == TheoremProto_0002.RHSPrimaryKey_UInt64]
                [TheoremProto_0002.TotalProofsFound_UInt64 >= TheoremProto_0002.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0002, Axiom);

                limiter.release();
            }

        });

    std::for_each(std::execution::par_unseq,
        Axioms_Vec.begin(),
        Axioms_Vec.end(),
        [&](const Axiom_Struct& Axiom)
        {
            RecursionLimiter::Invoke limiter(6);
            if (limiter.acquired())
            {
                Auto
                [TheoremProto_0003.LHSPrimaryKey_UInt64 == TheoremProto_0003.RHSPrimaryKey_UInt64]
                [TheoremProto_0003.TotalProofsFound_UInt64 >= TheoremProto_0003.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0003, Axiom);

                Auto
                [TheoremProto_0003.LHSPrimaryKey_UInt64 == TheoremProto_0003.RHSPrimaryKey_UInt64]
                [TheoremProto_0003.TotalProofsFound_UInt64 >= TheoremProto_0003.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0003, Axiom);

                Auto
                [TheoremProto_0004.LHSPrimaryKey_UInt64 == TheoremProto_0004.RHSPrimaryKey_UInt64]
                [TheoremProto_0004.TotalProofsFound_UInt64 >= TheoremProto_0004.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0004, Axiom);

                Auto
                [TheoremProto_0004.LHSPrimaryKey_UInt64 == TheoremProto_0004.RHSPrimaryKey_UInt64]
                [TheoremProto_0004.TotalProofsFound_UInt64 >= TheoremProto_0004.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0004, Axiom);

                Auto
                [TheoremProto_0005.LHSPrimaryKey_UInt64 == TheoremProto_0005.RHSPrimaryKey_UInt64]
                [TheoremProto_0005.TotalProofsFound_UInt64 >= TheoremProto_0005.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0005, Axiom);

                Auto
                [TheoremProto_0005.LHSPrimaryKey_UInt64 == TheoremProto_0005.RHSPrimaryKey_UInt64]
                [TheoremProto_0005.TotalProofsFound_UInt64 >= TheoremProto_0005.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0005, Axiom);

                limiter.release();
            }

        });

    std::for_each(std::execution::par_unseq,
        Axioms_Vec.begin(),
        Axioms_Vec.end(),
        [&](const Axiom_Struct& Axiom)
        {
            RecursionLimiter::Invoke limiter(12);
            if (limiter.acquired())
            {
                Auto
                [TheoremProto_0000.LHSPrimaryKey_UInt64 == TheoremProto_0000.RHSPrimaryKey_UInt64]
                [TheoremProto_0000.TotalProofsFound_UInt64 >= TheoremProto_0000.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0000, Axiom);

                Auto
                [TheoremProto_0000.LHSPrimaryKey_UInt64 == TheoremProto_0000.RHSPrimaryKey_UInt64]
                [TheoremProto_0000.TotalProofsFound_UInt64 >= TheoremProto_0000.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0000, Axiom);

                Auto
                [TheoremProto_0001.LHSPrimaryKey_UInt64 == TheoremProto_0001.RHSPrimaryKey_UInt64]
                [TheoremProto_0001.TotalProofsFound_UInt64 >= TheoremProto_0001.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0001, Axiom);

                Auto
                [TheoremProto_0001.LHSPrimaryKey_UInt64 == TheoremProto_0001.RHSPrimaryKey_UInt64]
                [TheoremProto_0001.TotalProofsFound_UInt64 >= TheoremProto_0001.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0001, Axiom);

                Auto
                [TheoremProto_0002.LHSPrimaryKey_UInt64 == TheoremProto_0002.RHSPrimaryKey_UInt64]
                [TheoremProto_0002.TotalProofsFound_UInt64 >= TheoremProto_0002.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0002, Axiom);

                Auto
                [TheoremProto_0002.LHSPrimaryKey_UInt64 == TheoremProto_0002.RHSPrimaryKey_UInt64]
                [TheoremProto_0002.TotalProofsFound_UInt64 >= TheoremProto_0002.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0002, Axiom);


                Auto
                [TheoremProto_0003.LHSPrimaryKey_UInt64 == TheoremProto_0003.RHSPrimaryKey_UInt64]
                [TheoremProto_0003.TotalProofsFound_UInt64 >= TheoremProto_0003.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0003, Axiom);

                Auto
                [TheoremProto_0003.LHSPrimaryKey_UInt64 == TheoremProto_0003.RHSPrimaryKey_UInt64]
                [TheoremProto_0003.TotalProofsFound_UInt64 >= TheoremProto_0003.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0003, Axiom);

                Auto
                [TheoremProto_0004.LHSPrimaryKey_UInt64 == TheoremProto_0004.RHSPrimaryKey_UInt64]
                [TheoremProto_0004.TotalProofsFound_UInt64 >= TheoremProto_0004.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0004, Axiom);

                Auto
                [TheoremProto_0004.LHSPrimaryKey_UInt64 == TheoremProto_0004.RHSPrimaryKey_UInt64]
                [TheoremProto_0004.TotalProofsFound_UInt64 >= TheoremProto_0004.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0004, Axiom);

                Auto
                [TheoremProto_0005.LHSPrimaryKey_UInt64 == TheoremProto_0005.RHSPrimaryKey_UInt64]
                [TheoremProto_0005.TotalProofsFound_UInt64 >= TheoremProto_0005.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0005, Axiom);

                Auto
                [TheoremProto_0005.LHSPrimaryKey_UInt64 == TheoremProto_0005.RHSPrimaryKey_UInt64]
                [TheoremProto_0005.TotalProofsFound_UInt64 >= TheoremProto_0005.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0005, Axiom);

                limiter.release();
            }

        });

};

Auto
[false]
[false]
[RouteSource_EnumClass::_lhs]
[Indirection_EnumClass::_reduce] =
[](Theorem_Struct InTheorem, const Axiom_Struct& InAxiom) -> void
{
    InTheorem.ProofStack_VecUInt64.push_back(InAxiom);

    if (InTheorem.LHSPrimaryKey_UInt64 == InTheorem.RHSPrimaryKey_UInt64)
    {
        InTheorem.ProofFound_Flag = true;
        ++InTheorem.TotalProofsFound_UInt64;
    }

    if (InTheorem.TotalProofsFound_UInt64 >= InTheorem.MaxAllowedProofs_UInt64)
        return;

    Theorem_Struct TheoremProto_0000 = InTheorem;
    Theorem_Struct TheoremProto_0001 = InTheorem;
    Theorem_Struct TheoremProto_0002 = InTheorem;
    Theorem_Struct TheoremProto_0003 = InTheorem;
    Theorem_Struct TheoremProto_0004 = InTheorem;
    Theorem_Struct TheoremProto_0005 = InTheorem;

    if (TheoremProto_0000.SubnetFound_LHS(InAxiom.LHSPrimaryKey_UInt64))
        TheoremProto_0000.UpdatePrimaryKey_LHS(InAxiom.LHSPrimaryKey_UInt64);

    TheoremProto_0001.UpdatePrimaryKey_RHS(InAxiom.LHSPrimaryKey_UInt64);
    TheoremProto_0002.UpdatePrimaryKey_LHS(InAxiom.LHSPrimaryKey_UInt64);
    TheoremProto_0002.UpdatePrimaryKey_RHS(InAxiom.RHSPrimaryKey_UInt64);

    TheoremProto_0003.UpdatePrimaryKey_LHS(InAxiom.RHSPrimaryKey_UInt64);
    TheoremProto_0004.UpdatePrimaryKey_RHS(InAxiom.RHSPrimaryKey_UInt64);
    TheoremProto_0005.UpdatePrimaryKey_LHS(InAxiom.RHSPrimaryKey_UInt64);
    TheoremProto_0005.UpdatePrimaryKey_RHS(InAxiom.LHSPrimaryKey_UInt64);

    std::for_each(std::execution::par_unseq,
        Axioms_Vec.begin(),
        Axioms_Vec.end(),
        [&](const Axiom_Struct& Axiom)
        {
            RecursionLimiter::Invoke limiter(6);
            if (limiter.acquired())
            {
                Auto
                [TheoremProto_0000.LHSPrimaryKey_UInt64 == TheoremProto_0000.RHSPrimaryKey_UInt64]
                [TheoremProto_0000.TotalProofsFound_UInt64 >= TheoremProto_0000.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0000, Axiom);

                Auto
                [TheoremProto_0000.LHSPrimaryKey_UInt64 == TheoremProto_0000.RHSPrimaryKey_UInt64]
                [TheoremProto_0000.TotalProofsFound_UInt64 >= TheoremProto_0000.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0000, Axiom);

                Auto
                [TheoremProto_0001.LHSPrimaryKey_UInt64 == TheoremProto_0001.RHSPrimaryKey_UInt64]
                [TheoremProto_0001.TotalProofsFound_UInt64 >= TheoremProto_0001.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0001, Axiom);

                Auto
                [TheoremProto_0001.LHSPrimaryKey_UInt64 == TheoremProto_0001.RHSPrimaryKey_UInt64]
                [TheoremProto_0001.TotalProofsFound_UInt64 >= TheoremProto_0001.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0001, Axiom);

                Auto
                [TheoremProto_0002.LHSPrimaryKey_UInt64 == TheoremProto_0002.RHSPrimaryKey_UInt64]
                [TheoremProto_0002.TotalProofsFound_UInt64 >= TheoremProto_0002.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0002, Axiom);

                Auto
                [TheoremProto_0002.LHSPrimaryKey_UInt64 == TheoremProto_0002.RHSPrimaryKey_UInt64]
                [TheoremProto_0002.TotalProofsFound_UInt64 >= TheoremProto_0002.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0002, Axiom);

                limiter.release();
            }

        });

    std::for_each(std::execution::par_unseq,
        Axioms_Vec.begin(),
        Axioms_Vec.end(),
        [&](const Axiom_Struct& Axiom)
        {
            RecursionLimiter::Invoke limiter(6);
            if (limiter.acquired())
            {
                Auto
                [TheoremProto_0003.LHSPrimaryKey_UInt64 == TheoremProto_0003.RHSPrimaryKey_UInt64]
                [TheoremProto_0003.TotalProofsFound_UInt64 >= TheoremProto_0003.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0003, Axiom);

                Auto
                [TheoremProto_0003.LHSPrimaryKey_UInt64 == TheoremProto_0003.RHSPrimaryKey_UInt64]
                [TheoremProto_0003.TotalProofsFound_UInt64 >= TheoremProto_0003.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0003, Axiom);

                Auto
                [TheoremProto_0004.LHSPrimaryKey_UInt64 == TheoremProto_0004.RHSPrimaryKey_UInt64]
                [TheoremProto_0004.TotalProofsFound_UInt64 >= TheoremProto_0004.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0004, Axiom);

                Auto
                [TheoremProto_0004.LHSPrimaryKey_UInt64 == TheoremProto_0004.RHSPrimaryKey_UInt64]
                [TheoremProto_0004.TotalProofsFound_UInt64 >= TheoremProto_0004.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0004, Axiom);

                Auto
                [TheoremProto_0005.LHSPrimaryKey_UInt64 == TheoremProto_0005.RHSPrimaryKey_UInt64]
                [TheoremProto_0005.TotalProofsFound_UInt64 >= TheoremProto_0005.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0005, Axiom);

                Auto
                [TheoremProto_0005.LHSPrimaryKey_UInt64 == TheoremProto_0005.RHSPrimaryKey_UInt64]
                [TheoremProto_0005.TotalProofsFound_UInt64 >= TheoremProto_0005.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0005, Axiom);

                limiter.release();
            }

        });

    std::for_each(std::execution::par_unseq,
        Axioms_Vec.begin(),
        Axioms_Vec.end(),
        [&](const Axiom_Struct& Axiom)
        {
            RecursionLimiter::Invoke limiter(12);
            if (limiter.acquired())
            {
                Auto
                [TheoremProto_0000.LHSPrimaryKey_UInt64 == TheoremProto_0000.RHSPrimaryKey_UInt64]
                [TheoremProto_0000.TotalProofsFound_UInt64 >= TheoremProto_0000.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0000, Axiom);

                Auto
                [TheoremProto_0000.LHSPrimaryKey_UInt64 == TheoremProto_0000.RHSPrimaryKey_UInt64]
                [TheoremProto_0000.TotalProofsFound_UInt64 >= TheoremProto_0000.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0000, Axiom);

                Auto
                [TheoremProto_0001.LHSPrimaryKey_UInt64 == TheoremProto_0001.RHSPrimaryKey_UInt64]
                [TheoremProto_0001.TotalProofsFound_UInt64 >= TheoremProto_0001.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0001, Axiom);

                Auto
                [TheoremProto_0001.LHSPrimaryKey_UInt64 == TheoremProto_0001.RHSPrimaryKey_UInt64]
                [TheoremProto_0001.TotalProofsFound_UInt64 >= TheoremProto_0001.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0001, Axiom);

                Auto
                [TheoremProto_0002.LHSPrimaryKey_UInt64 == TheoremProto_0002.RHSPrimaryKey_UInt64]
                [TheoremProto_0002.TotalProofsFound_UInt64 >= TheoremProto_0002.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0002, Axiom);

                Auto
                [TheoremProto_0002.LHSPrimaryKey_UInt64 == TheoremProto_0002.RHSPrimaryKey_UInt64]
                [TheoremProto_0002.TotalProofsFound_UInt64 >= TheoremProto_0002.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0002, Axiom);


                Auto
                [TheoremProto_0003.LHSPrimaryKey_UInt64 == TheoremProto_0003.RHSPrimaryKey_UInt64]
                [TheoremProto_0003.TotalProofsFound_UInt64 >= TheoremProto_0003.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0003, Axiom);

                Auto
                [TheoremProto_0003.LHSPrimaryKey_UInt64 == TheoremProto_0003.RHSPrimaryKey_UInt64]
                [TheoremProto_0003.TotalProofsFound_UInt64 >= TheoremProto_0003.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0003, Axiom);

                Auto
                [TheoremProto_0004.LHSPrimaryKey_UInt64 == TheoremProto_0004.RHSPrimaryKey_UInt64]
                [TheoremProto_0004.TotalProofsFound_UInt64 >= TheoremProto_0004.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0004, Axiom);

                Auto
                [TheoremProto_0004.LHSPrimaryKey_UInt64 == TheoremProto_0004.RHSPrimaryKey_UInt64]
                [TheoremProto_0004.TotalProofsFound_UInt64 >= TheoremProto_0004.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0004, Axiom);

                Auto
                [TheoremProto_0005.LHSPrimaryKey_UInt64 == TheoremProto_0005.RHSPrimaryKey_UInt64]
                [TheoremProto_0005.TotalProofsFound_UInt64 >= TheoremProto_0005.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0005, Axiom);

                Auto
                [TheoremProto_0005.LHSPrimaryKey_UInt64 == TheoremProto_0005.RHSPrimaryKey_UInt64]
                [TheoremProto_0005.TotalProofsFound_UInt64 >= TheoremProto_0005.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0005, Axiom);

                limiter.release();
            }

        });

};

Auto
[false]
[false]
[RouteSource_EnumClass::_lhs]
[Indirection_EnumClass::_expand] =
[](Theorem_Struct InTheorem, const Axiom_Struct& InAxiom) -> void
{
    InTheorem.ProofStack_VecUInt64.push_back(InAxiom);

    if (InTheorem.LHSPrimaryKey_UInt64 == InTheorem.RHSPrimaryKey_UInt64)
    {
        InTheorem.ProofFound_Flag = true;
        ++InTheorem.TotalProofsFound_UInt64;
    }

    if (InTheorem.TotalProofsFound_UInt64 >= InTheorem.MaxAllowedProofs_UInt64)
        return;

    Theorem_Struct TheoremProto_0000 = InTheorem;
    Theorem_Struct TheoremProto_0001 = InTheorem;
    Theorem_Struct TheoremProto_0002 = InTheorem;
    Theorem_Struct TheoremProto_0003 = InTheorem;
    Theorem_Struct TheoremProto_0004 = InTheorem;
    Theorem_Struct TheoremProto_0005 = InTheorem;

    if (TheoremProto_0000.SubnetFound_LHS(InAxiom.LHSPrimaryKey_UInt64))
        TheoremProto_0000.UpdatePrimaryKey_LHS(InAxiom.LHSPrimaryKey_UInt64);

    TheoremProto_0001.UpdatePrimaryKey_RHS(InAxiom.LHSPrimaryKey_UInt64);
    TheoremProto_0002.UpdatePrimaryKey_LHS(InAxiom.LHSPrimaryKey_UInt64);
    TheoremProto_0002.UpdatePrimaryKey_RHS(InAxiom.RHSPrimaryKey_UInt64);

    TheoremProto_0003.UpdatePrimaryKey_LHS(InAxiom.RHSPrimaryKey_UInt64);
    TheoremProto_0004.UpdatePrimaryKey_RHS(InAxiom.RHSPrimaryKey_UInt64);
    TheoremProto_0005.UpdatePrimaryKey_LHS(InAxiom.RHSPrimaryKey_UInt64);
    TheoremProto_0005.UpdatePrimaryKey_RHS(InAxiom.LHSPrimaryKey_UInt64);

    std::for_each(std::execution::par_unseq,
        Axioms_Vec.begin(),
        Axioms_Vec.end(),
        [&](const Axiom_Struct& Axiom)
        {
            RecursionLimiter::Invoke limiter(6);
            if (limiter.acquired())
            {
                Auto
                [TheoremProto_0000.LHSPrimaryKey_UInt64 == TheoremProto_0000.RHSPrimaryKey_UInt64]
                [TheoremProto_0000.TotalProofsFound_UInt64 >= TheoremProto_0000.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0000, Axiom);

                Auto
                [TheoremProto_0000.LHSPrimaryKey_UInt64 == TheoremProto_0000.RHSPrimaryKey_UInt64]
                [TheoremProto_0000.TotalProofsFound_UInt64 >= TheoremProto_0000.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0000, Axiom);

                Auto
                [TheoremProto_0001.LHSPrimaryKey_UInt64 == TheoremProto_0001.RHSPrimaryKey_UInt64]
                [TheoremProto_0001.TotalProofsFound_UInt64 >= TheoremProto_0001.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0001, Axiom);

                Auto
                [TheoremProto_0001.LHSPrimaryKey_UInt64 == TheoremProto_0001.RHSPrimaryKey_UInt64]
                [TheoremProto_0001.TotalProofsFound_UInt64 >= TheoremProto_0001.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0001, Axiom);

                Auto
                [TheoremProto_0002.LHSPrimaryKey_UInt64 == TheoremProto_0002.RHSPrimaryKey_UInt64]
                [TheoremProto_0002.TotalProofsFound_UInt64 >= TheoremProto_0002.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0002, Axiom);

                Auto
                [TheoremProto_0002.LHSPrimaryKey_UInt64 == TheoremProto_0002.RHSPrimaryKey_UInt64]
                [TheoremProto_0002.TotalProofsFound_UInt64 >= TheoremProto_0002.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0002, Axiom);

                limiter.release();
            }

        });

    std::for_each(std::execution::par_unseq,
        Axioms_Vec.begin(),
        Axioms_Vec.end(),
        [&](const Axiom_Struct& Axiom)
        {
            RecursionLimiter::Invoke limiter(6);
            if (limiter.acquired())
            {
                Auto
                [TheoremProto_0003.LHSPrimaryKey_UInt64 == TheoremProto_0003.RHSPrimaryKey_UInt64]
                [TheoremProto_0003.TotalProofsFound_UInt64 >= TheoremProto_0003.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0003, Axiom);

                Auto
                [TheoremProto_0003.LHSPrimaryKey_UInt64 == TheoremProto_0003.RHSPrimaryKey_UInt64]
                [TheoremProto_0003.TotalProofsFound_UInt64 >= TheoremProto_0003.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0003, Axiom);

                Auto
                [TheoremProto_0004.LHSPrimaryKey_UInt64 == TheoremProto_0004.RHSPrimaryKey_UInt64]
                [TheoremProto_0004.TotalProofsFound_UInt64 >= TheoremProto_0004.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0004, Axiom);

                Auto
                [TheoremProto_0004.LHSPrimaryKey_UInt64 == TheoremProto_0004.RHSPrimaryKey_UInt64]
                [TheoremProto_0004.TotalProofsFound_UInt64 >= TheoremProto_0004.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0004, Axiom);

                Auto
                [TheoremProto_0005.LHSPrimaryKey_UInt64 == TheoremProto_0005.RHSPrimaryKey_UInt64]
                [TheoremProto_0005.TotalProofsFound_UInt64 >= TheoremProto_0005.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0005, Axiom);

                Auto
                [TheoremProto_0005.LHSPrimaryKey_UInt64 == TheoremProto_0005.RHSPrimaryKey_UInt64]
                [TheoremProto_0005.TotalProofsFound_UInt64 >= TheoremProto_0005.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0005, Axiom);

                limiter.release();
            }

        });

    std::for_each(std::execution::par_unseq,
        Axioms_Vec.begin(),
        Axioms_Vec.end(),
        [&](const Axiom_Struct& Axiom)
        {
            RecursionLimiter::Invoke limiter(12);
            if (limiter.acquired())
            {
                Auto
                [TheoremProto_0000.LHSPrimaryKey_UInt64 == TheoremProto_0000.RHSPrimaryKey_UInt64]
                [TheoremProto_0000.TotalProofsFound_UInt64 >= TheoremProto_0000.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0000, Axiom);

                Auto
                [TheoremProto_0000.LHSPrimaryKey_UInt64 == TheoremProto_0000.RHSPrimaryKey_UInt64]
                [TheoremProto_0000.TotalProofsFound_UInt64 >= TheoremProto_0000.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0000, Axiom);

                Auto
                [TheoremProto_0001.LHSPrimaryKey_UInt64 == TheoremProto_0001.RHSPrimaryKey_UInt64]
                [TheoremProto_0001.TotalProofsFound_UInt64 >= TheoremProto_0001.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0001, Axiom);

                Auto
                [TheoremProto_0001.LHSPrimaryKey_UInt64 == TheoremProto_0001.RHSPrimaryKey_UInt64]
                [TheoremProto_0001.TotalProofsFound_UInt64 >= TheoremProto_0001.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0001, Axiom);

                Auto
                [TheoremProto_0002.LHSPrimaryKey_UInt64 == TheoremProto_0002.RHSPrimaryKey_UInt64]
                [TheoremProto_0002.TotalProofsFound_UInt64 >= TheoremProto_0002.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0002, Axiom);

                Auto
                [TheoremProto_0002.LHSPrimaryKey_UInt64 == TheoremProto_0002.RHSPrimaryKey_UInt64]
                [TheoremProto_0002.TotalProofsFound_UInt64 >= TheoremProto_0002.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0002, Axiom);


                Auto
                [TheoremProto_0003.LHSPrimaryKey_UInt64 == TheoremProto_0003.RHSPrimaryKey_UInt64]
                [TheoremProto_0003.TotalProofsFound_UInt64 >= TheoremProto_0003.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0003, Axiom);

                Auto
                [TheoremProto_0003.LHSPrimaryKey_UInt64 == TheoremProto_0003.RHSPrimaryKey_UInt64]
                [TheoremProto_0003.TotalProofsFound_UInt64 >= TheoremProto_0003.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0003, Axiom);

                Auto
                [TheoremProto_0004.LHSPrimaryKey_UInt64 == TheoremProto_0004.RHSPrimaryKey_UInt64]
                [TheoremProto_0004.TotalProofsFound_UInt64 >= TheoremProto_0004.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0004, Axiom);

                Auto
                [TheoremProto_0004.LHSPrimaryKey_UInt64 == TheoremProto_0004.RHSPrimaryKey_UInt64]
                [TheoremProto_0004.TotalProofsFound_UInt64 >= TheoremProto_0004.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0004, Axiom);

                Auto
                [TheoremProto_0005.LHSPrimaryKey_UInt64 == TheoremProto_0005.RHSPrimaryKey_UInt64]
                [TheoremProto_0005.TotalProofsFound_UInt64 >= TheoremProto_0005.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0005, Axiom);

                Auto
                [TheoremProto_0005.LHSPrimaryKey_UInt64 == TheoremProto_0005.RHSPrimaryKey_UInt64]
                [TheoremProto_0005.TotalProofsFound_UInt64 >= TheoremProto_0005.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0005, Axiom);

                limiter.release();
            }

        });

};

Auto
[false]
[false]
[RouteSource_EnumClass::_rhs]
[Indirection_EnumClass::_auto] =
[](Theorem_Struct InTheorem, const Axiom_Struct& InAxiom) -> void
{
    InTheorem.ProofStack_VecUInt64.push_back(InAxiom);

    if (InTheorem.LHSPrimaryKey_UInt64 == InTheorem.RHSPrimaryKey_UInt64)
    {
        InTheorem.ProofFound_Flag = true;
        ++InTheorem.TotalProofsFound_UInt64;
    }

    if (InTheorem.TotalProofsFound_UInt64 >= InTheorem.MaxAllowedProofs_UInt64)
        return;

    Theorem_Struct TheoremProto_0000 = InTheorem;
    Theorem_Struct TheoremProto_0001 = InTheorem;
    Theorem_Struct TheoremProto_0002 = InTheorem;
    Theorem_Struct TheoremProto_0003 = InTheorem;
    Theorem_Struct TheoremProto_0004 = InTheorem;
    Theorem_Struct TheoremProto_0005 = InTheorem;

    if (TheoremProto_0000.SubnetFound_LHS(InAxiom.LHSPrimaryKey_UInt64))
        TheoremProto_0000.UpdatePrimaryKey_LHS(InAxiom.LHSPrimaryKey_UInt64);

    TheoremProto_0001.UpdatePrimaryKey_RHS(InAxiom.LHSPrimaryKey_UInt64);
    TheoremProto_0002.UpdatePrimaryKey_LHS(InAxiom.LHSPrimaryKey_UInt64);
    TheoremProto_0002.UpdatePrimaryKey_RHS(InAxiom.RHSPrimaryKey_UInt64);

    TheoremProto_0003.UpdatePrimaryKey_LHS(InAxiom.RHSPrimaryKey_UInt64);
    TheoremProto_0004.UpdatePrimaryKey_RHS(InAxiom.RHSPrimaryKey_UInt64);
    TheoremProto_0005.UpdatePrimaryKey_LHS(InAxiom.RHSPrimaryKey_UInt64);
    TheoremProto_0005.UpdatePrimaryKey_RHS(InAxiom.LHSPrimaryKey_UInt64);

    std::for_each(std::execution::par_unseq,
        Axioms_Vec.begin(),
        Axioms_Vec.end(),
        [&](const Axiom_Struct& Axiom)
        {
            RecursionLimiter::Invoke limiter(6);
            if (limiter.acquired())
            {
                Auto
                [TheoremProto_0000.LHSPrimaryKey_UInt64 == TheoremProto_0000.RHSPrimaryKey_UInt64]
                [TheoremProto_0000.TotalProofsFound_UInt64 >= TheoremProto_0000.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0000, Axiom);

                Auto
                [TheoremProto_0000.LHSPrimaryKey_UInt64 == TheoremProto_0000.RHSPrimaryKey_UInt64]
                [TheoremProto_0000.TotalProofsFound_UInt64 >= TheoremProto_0000.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0000, Axiom);

                Auto
                [TheoremProto_0001.LHSPrimaryKey_UInt64 == TheoremProto_0001.RHSPrimaryKey_UInt64]
                [TheoremProto_0001.TotalProofsFound_UInt64 >= TheoremProto_0001.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0001, Axiom);

                Auto
                [TheoremProto_0001.LHSPrimaryKey_UInt64 == TheoremProto_0001.RHSPrimaryKey_UInt64]
                [TheoremProto_0001.TotalProofsFound_UInt64 >= TheoremProto_0001.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0001, Axiom);

                Auto
                [TheoremProto_0002.LHSPrimaryKey_UInt64 == TheoremProto_0002.RHSPrimaryKey_UInt64]
                [TheoremProto_0002.TotalProofsFound_UInt64 >= TheoremProto_0002.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0002, Axiom);

                Auto
                [TheoremProto_0002.LHSPrimaryKey_UInt64 == TheoremProto_0002.RHSPrimaryKey_UInt64]
                [TheoremProto_0002.TotalProofsFound_UInt64 >= TheoremProto_0002.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0002, Axiom);

                limiter.release();
            }

        });

    std::for_each(std::execution::par_unseq,
        Axioms_Vec.begin(),
        Axioms_Vec.end(),
        [&](const Axiom_Struct& Axiom)
        {
            RecursionLimiter::Invoke limiter(6);
            if (limiter.acquired())
            {
                Auto
                [TheoremProto_0003.LHSPrimaryKey_UInt64 == TheoremProto_0003.RHSPrimaryKey_UInt64]
                [TheoremProto_0003.TotalProofsFound_UInt64 >= TheoremProto_0003.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0003, Axiom);

                Auto
                [TheoremProto_0003.LHSPrimaryKey_UInt64 == TheoremProto_0003.RHSPrimaryKey_UInt64]
                [TheoremProto_0003.TotalProofsFound_UInt64 >= TheoremProto_0003.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0003, Axiom);

                Auto
                [TheoremProto_0004.LHSPrimaryKey_UInt64 == TheoremProto_0004.RHSPrimaryKey_UInt64]
                [TheoremProto_0004.TotalProofsFound_UInt64 >= TheoremProto_0004.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0004, Axiom);

                Auto
                [TheoremProto_0004.LHSPrimaryKey_UInt64 == TheoremProto_0004.RHSPrimaryKey_UInt64]
                [TheoremProto_0004.TotalProofsFound_UInt64 >= TheoremProto_0004.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0004, Axiom);

                Auto
                [TheoremProto_0005.LHSPrimaryKey_UInt64 == TheoremProto_0005.RHSPrimaryKey_UInt64]
                [TheoremProto_0005.TotalProofsFound_UInt64 >= TheoremProto_0005.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0005, Axiom);

                Auto
                [TheoremProto_0005.LHSPrimaryKey_UInt64 == TheoremProto_0005.RHSPrimaryKey_UInt64]
                [TheoremProto_0005.TotalProofsFound_UInt64 >= TheoremProto_0005.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0005, Axiom);

                limiter.release();
            }

        });

    std::for_each(std::execution::par_unseq,
        Axioms_Vec.begin(),
        Axioms_Vec.end(),
        [&](const Axiom_Struct& Axiom)
        {
            RecursionLimiter::Invoke limiter(12);
            if (limiter.acquired())
            {
                Auto
                [TheoremProto_0000.LHSPrimaryKey_UInt64 == TheoremProto_0000.RHSPrimaryKey_UInt64]
                [TheoremProto_0000.TotalProofsFound_UInt64 >= TheoremProto_0000.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0000, Axiom);

                Auto
                [TheoremProto_0000.LHSPrimaryKey_UInt64 == TheoremProto_0000.RHSPrimaryKey_UInt64]
                [TheoremProto_0000.TotalProofsFound_UInt64 >= TheoremProto_0000.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0000, Axiom);

                Auto
                [TheoremProto_0001.LHSPrimaryKey_UInt64 == TheoremProto_0001.RHSPrimaryKey_UInt64]
                [TheoremProto_0001.TotalProofsFound_UInt64 >= TheoremProto_0001.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0001, Axiom);

                Auto
                [TheoremProto_0001.LHSPrimaryKey_UInt64 == TheoremProto_0001.RHSPrimaryKey_UInt64]
                [TheoremProto_0001.TotalProofsFound_UInt64 >= TheoremProto_0001.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0001, Axiom);

                Auto
                [TheoremProto_0002.LHSPrimaryKey_UInt64 == TheoremProto_0002.RHSPrimaryKey_UInt64]
                [TheoremProto_0002.TotalProofsFound_UInt64 >= TheoremProto_0002.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0002, Axiom);

                Auto
                [TheoremProto_0002.LHSPrimaryKey_UInt64 == TheoremProto_0002.RHSPrimaryKey_UInt64]
                [TheoremProto_0002.TotalProofsFound_UInt64 >= TheoremProto_0002.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0002, Axiom);


                Auto
                [TheoremProto_0003.LHSPrimaryKey_UInt64 == TheoremProto_0003.RHSPrimaryKey_UInt64]
                [TheoremProto_0003.TotalProofsFound_UInt64 >= TheoremProto_0003.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0003, Axiom);

                Auto
                [TheoremProto_0003.LHSPrimaryKey_UInt64 == TheoremProto_0003.RHSPrimaryKey_UInt64]
                [TheoremProto_0003.TotalProofsFound_UInt64 >= TheoremProto_0003.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0003, Axiom);

                Auto
                [TheoremProto_0004.LHSPrimaryKey_UInt64 == TheoremProto_0004.RHSPrimaryKey_UInt64]
                [TheoremProto_0004.TotalProofsFound_UInt64 >= TheoremProto_0004.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0004, Axiom);

                Auto
                [TheoremProto_0004.LHSPrimaryKey_UInt64 == TheoremProto_0004.RHSPrimaryKey_UInt64]
                [TheoremProto_0004.TotalProofsFound_UInt64 >= TheoremProto_0004.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0004, Axiom);

                Auto
                [TheoremProto_0005.LHSPrimaryKey_UInt64 == TheoremProto_0005.RHSPrimaryKey_UInt64]
                [TheoremProto_0005.TotalProofsFound_UInt64 >= TheoremProto_0005.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0005, Axiom);

                Auto
                [TheoremProto_0005.LHSPrimaryKey_UInt64 == TheoremProto_0005.RHSPrimaryKey_UInt64]
                [TheoremProto_0005.TotalProofsFound_UInt64 >= TheoremProto_0005.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0005, Axiom);

                limiter.release();
            }

        });

};

Auto
[false]
[false]
[RouteSource_EnumClass::_rhs]
[Indirection_EnumClass::_reduce] =
[](Theorem_Struct InTheorem, const Axiom_Struct& InAxiom) -> void
{
    InTheorem.ProofStack_VecUInt64.push_back(InAxiom);

    if (InTheorem.LHSPrimaryKey_UInt64 == InTheorem.RHSPrimaryKey_UInt64)
    {
        InTheorem.ProofFound_Flag = true;
        ++InTheorem.TotalProofsFound_UInt64;
    }

    if (InTheorem.TotalProofsFound_UInt64 >= InTheorem.MaxAllowedProofs_UInt64)
        return;

    Theorem_Struct TheoremProto_0000 = InTheorem;
    Theorem_Struct TheoremProto_0001 = InTheorem;
    Theorem_Struct TheoremProto_0002 = InTheorem;
    Theorem_Struct TheoremProto_0003 = InTheorem;
    Theorem_Struct TheoremProto_0004 = InTheorem;
    Theorem_Struct TheoremProto_0005 = InTheorem;

    if (TheoremProto_0000.SubnetFound_LHS(InAxiom.LHSPrimaryKey_UInt64))
        TheoremProto_0000.UpdatePrimaryKey_LHS(InAxiom.LHSPrimaryKey_UInt64);

    TheoremProto_0001.UpdatePrimaryKey_RHS(InAxiom.LHSPrimaryKey_UInt64);
    TheoremProto_0002.UpdatePrimaryKey_LHS(InAxiom.LHSPrimaryKey_UInt64);
    TheoremProto_0002.UpdatePrimaryKey_RHS(InAxiom.RHSPrimaryKey_UInt64);

    TheoremProto_0003.UpdatePrimaryKey_LHS(InAxiom.RHSPrimaryKey_UInt64);
    TheoremProto_0004.UpdatePrimaryKey_RHS(InAxiom.RHSPrimaryKey_UInt64);
    TheoremProto_0005.UpdatePrimaryKey_LHS(InAxiom.RHSPrimaryKey_UInt64);
    TheoremProto_0005.UpdatePrimaryKey_RHS(InAxiom.LHSPrimaryKey_UInt64);

    std::for_each(std::execution::par_unseq,
        Axioms_Vec.begin(),
        Axioms_Vec.end(),
        [&](const Axiom_Struct& Axiom)
        {
            RecursionLimiter::Invoke limiter(6);
            if (limiter.acquired())
            {
                Auto
                [TheoremProto_0000.LHSPrimaryKey_UInt64 == TheoremProto_0000.RHSPrimaryKey_UInt64]
                [TheoremProto_0000.TotalProofsFound_UInt64 >= TheoremProto_0000.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0000, Axiom);

                Auto
                [TheoremProto_0000.LHSPrimaryKey_UInt64 == TheoremProto_0000.RHSPrimaryKey_UInt64]
                [TheoremProto_0000.TotalProofsFound_UInt64 >= TheoremProto_0000.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0000, Axiom);

                Auto
                [TheoremProto_0001.LHSPrimaryKey_UInt64 == TheoremProto_0001.RHSPrimaryKey_UInt64]
                [TheoremProto_0001.TotalProofsFound_UInt64 >= TheoremProto_0001.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0001, Axiom);

                Auto
                [TheoremProto_0001.LHSPrimaryKey_UInt64 == TheoremProto_0001.RHSPrimaryKey_UInt64]
                [TheoremProto_0001.TotalProofsFound_UInt64 >= TheoremProto_0001.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0001, Axiom);

                Auto
                [TheoremProto_0002.LHSPrimaryKey_UInt64 == TheoremProto_0002.RHSPrimaryKey_UInt64]
                [TheoremProto_0002.TotalProofsFound_UInt64 >= TheoremProto_0002.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0002, Axiom);

                Auto
                [TheoremProto_0002.LHSPrimaryKey_UInt64 == TheoremProto_0002.RHSPrimaryKey_UInt64]
                [TheoremProto_0002.TotalProofsFound_UInt64 >= TheoremProto_0002.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0002, Axiom);

                limiter.release();
            }

        });

    std::for_each(std::execution::par_unseq,
        Axioms_Vec.begin(),
        Axioms_Vec.end(),
        [&](const Axiom_Struct& Axiom)
        {
            RecursionLimiter::Invoke limiter(6);
            if (limiter.acquired())
            {
                Auto
                [TheoremProto_0003.LHSPrimaryKey_UInt64 == TheoremProto_0003.RHSPrimaryKey_UInt64]
                [TheoremProto_0003.TotalProofsFound_UInt64 >= TheoremProto_0003.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0003, Axiom);

                Auto
                [TheoremProto_0003.LHSPrimaryKey_UInt64 == TheoremProto_0003.RHSPrimaryKey_UInt64]
                [TheoremProto_0003.TotalProofsFound_UInt64 >= TheoremProto_0003.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0003, Axiom);

                Auto
                [TheoremProto_0004.LHSPrimaryKey_UInt64 == TheoremProto_0004.RHSPrimaryKey_UInt64]
                [TheoremProto_0004.TotalProofsFound_UInt64 >= TheoremProto_0004.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0004, Axiom);

                Auto
                [TheoremProto_0004.LHSPrimaryKey_UInt64 == TheoremProto_0004.RHSPrimaryKey_UInt64]
                [TheoremProto_0004.TotalProofsFound_UInt64 >= TheoremProto_0004.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0004, Axiom);

                Auto
                [TheoremProto_0005.LHSPrimaryKey_UInt64 == TheoremProto_0005.RHSPrimaryKey_UInt64]
                [TheoremProto_0005.TotalProofsFound_UInt64 >= TheoremProto_0005.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0005, Axiom);

                Auto
                [TheoremProto_0005.LHSPrimaryKey_UInt64 == TheoremProto_0005.RHSPrimaryKey_UInt64]
                [TheoremProto_0005.TotalProofsFound_UInt64 >= TheoremProto_0005.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0005, Axiom);

                limiter.release();
            }

        });

    std::for_each(std::execution::par_unseq,
        Axioms_Vec.begin(),
        Axioms_Vec.end(),
        [&](const Axiom_Struct& Axiom)
        {
            RecursionLimiter::Invoke limiter(12);
            if (limiter.acquired())
            {
                Auto
                [TheoremProto_0000.LHSPrimaryKey_UInt64 == TheoremProto_0000.RHSPrimaryKey_UInt64]
                [TheoremProto_0000.TotalProofsFound_UInt64 >= TheoremProto_0000.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0000, Axiom);

                Auto
                [TheoremProto_0000.LHSPrimaryKey_UInt64 == TheoremProto_0000.RHSPrimaryKey_UInt64]
                [TheoremProto_0000.TotalProofsFound_UInt64 >= TheoremProto_0000.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0000, Axiom);

                Auto
                [TheoremProto_0001.LHSPrimaryKey_UInt64 == TheoremProto_0001.RHSPrimaryKey_UInt64]
                [TheoremProto_0001.TotalProofsFound_UInt64 >= TheoremProto_0001.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0001, Axiom);

                Auto
                [TheoremProto_0001.LHSPrimaryKey_UInt64 == TheoremProto_0001.RHSPrimaryKey_UInt64]
                [TheoremProto_0001.TotalProofsFound_UInt64 >= TheoremProto_0001.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0001, Axiom);

                Auto
                [TheoremProto_0002.LHSPrimaryKey_UInt64 == TheoremProto_0002.RHSPrimaryKey_UInt64]
                [TheoremProto_0002.TotalProofsFound_UInt64 >= TheoremProto_0002.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0002, Axiom);

                Auto
                [TheoremProto_0002.LHSPrimaryKey_UInt64 == TheoremProto_0002.RHSPrimaryKey_UInt64]
                [TheoremProto_0002.TotalProofsFound_UInt64 >= TheoremProto_0002.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0002, Axiom);


                Auto
                [TheoremProto_0003.LHSPrimaryKey_UInt64 == TheoremProto_0003.RHSPrimaryKey_UInt64]
                [TheoremProto_0003.TotalProofsFound_UInt64 >= TheoremProto_0003.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0003, Axiom);

                Auto
                [TheoremProto_0003.LHSPrimaryKey_UInt64 == TheoremProto_0003.RHSPrimaryKey_UInt64]
                [TheoremProto_0003.TotalProofsFound_UInt64 >= TheoremProto_0003.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0003, Axiom);

                Auto
                [TheoremProto_0004.LHSPrimaryKey_UInt64 == TheoremProto_0004.RHSPrimaryKey_UInt64]
                [TheoremProto_0004.TotalProofsFound_UInt64 >= TheoremProto_0004.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0004, Axiom);

                Auto
                [TheoremProto_0004.LHSPrimaryKey_UInt64 == TheoremProto_0004.RHSPrimaryKey_UInt64]
                [TheoremProto_0004.TotalProofsFound_UInt64 >= TheoremProto_0004.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0004, Axiom);

                Auto
                [TheoremProto_0005.LHSPrimaryKey_UInt64 == TheoremProto_0005.RHSPrimaryKey_UInt64]
                [TheoremProto_0005.TotalProofsFound_UInt64 >= TheoremProto_0005.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0005, Axiom);

                Auto
                [TheoremProto_0005.LHSPrimaryKey_UInt64 == TheoremProto_0005.RHSPrimaryKey_UInt64]
                [TheoremProto_0005.TotalProofsFound_UInt64 >= TheoremProto_0005.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0005, Axiom);

                limiter.release();
            }

        });

};

Auto
[false]
[false]
[RouteSource_EnumClass::_rhs]
[Indirection_EnumClass::_expand] =
[](Theorem_Struct InTheorem, const Axiom_Struct& InAxiom) -> void
{
    InTheorem.ProofStack_VecUInt64.push_back(InAxiom);

    if (InTheorem.LHSPrimaryKey_UInt64 == InTheorem.RHSPrimaryKey_UInt64)
    {
        InTheorem.ProofFound_Flag = true;
        ++InTheorem.TotalProofsFound_UInt64;
    }

    if (InTheorem.TotalProofsFound_UInt64 >= InTheorem.MaxAllowedProofs_UInt64)
        return;

    Theorem_Struct TheoremProto_0000 = InTheorem;
    Theorem_Struct TheoremProto_0001 = InTheorem;
    Theorem_Struct TheoremProto_0002 = InTheorem;
    Theorem_Struct TheoremProto_0003 = InTheorem;
    Theorem_Struct TheoremProto_0004 = InTheorem;
    Theorem_Struct TheoremProto_0005 = InTheorem;

    if (TheoremProto_0000.SubnetFound_LHS(InAxiom.LHSPrimaryKey_UInt64))
        TheoremProto_0000.UpdatePrimaryKey_LHS(InAxiom.LHSPrimaryKey_UInt64);

    TheoremProto_0001.UpdatePrimaryKey_RHS(InAxiom.LHSPrimaryKey_UInt64);
    TheoremProto_0002.UpdatePrimaryKey_LHS(InAxiom.LHSPrimaryKey_UInt64);
    TheoremProto_0002.UpdatePrimaryKey_RHS(InAxiom.RHSPrimaryKey_UInt64);

    TheoremProto_0003.UpdatePrimaryKey_LHS(InAxiom.RHSPrimaryKey_UInt64);
    TheoremProto_0004.UpdatePrimaryKey_RHS(InAxiom.RHSPrimaryKey_UInt64);
    TheoremProto_0005.UpdatePrimaryKey_LHS(InAxiom.RHSPrimaryKey_UInt64);
    TheoremProto_0005.UpdatePrimaryKey_RHS(InAxiom.LHSPrimaryKey_UInt64);

    std::for_each(std::execution::par_unseq,
        Axioms_Vec.begin(),
        Axioms_Vec.end(),
        [&](const Axiom_Struct& Axiom)
        {
            RecursionLimiter::Invoke limiter(6);
            if (limiter.acquired())
            {
                Auto
                [TheoremProto_0000.LHSPrimaryKey_UInt64 == TheoremProto_0000.RHSPrimaryKey_UInt64]
                [TheoremProto_0000.TotalProofsFound_UInt64 >= TheoremProto_0000.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0000, Axiom);

                Auto
                [TheoremProto_0000.LHSPrimaryKey_UInt64 == TheoremProto_0000.RHSPrimaryKey_UInt64]
                [TheoremProto_0000.TotalProofsFound_UInt64 >= TheoremProto_0000.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0000, Axiom);

                Auto
                [TheoremProto_0001.LHSPrimaryKey_UInt64 == TheoremProto_0001.RHSPrimaryKey_UInt64]
                [TheoremProto_0001.TotalProofsFound_UInt64 >= TheoremProto_0001.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0001, Axiom);

                Auto
                [TheoremProto_0001.LHSPrimaryKey_UInt64 == TheoremProto_0001.RHSPrimaryKey_UInt64]
                [TheoremProto_0001.TotalProofsFound_UInt64 >= TheoremProto_0001.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0001, Axiom);

                Auto
                [TheoremProto_0002.LHSPrimaryKey_UInt64 == TheoremProto_0002.RHSPrimaryKey_UInt64]
                [TheoremProto_0002.TotalProofsFound_UInt64 >= TheoremProto_0002.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0002, Axiom);

                Auto
                [TheoremProto_0002.LHSPrimaryKey_UInt64 == TheoremProto_0002.RHSPrimaryKey_UInt64]
                [TheoremProto_0002.TotalProofsFound_UInt64 >= TheoremProto_0002.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0002, Axiom);

                limiter.release();
            }

        });

    std::for_each(std::execution::par_unseq,
        Axioms_Vec.begin(),
        Axioms_Vec.end(),
        [&](const Axiom_Struct& Axiom)
        {
            RecursionLimiter::Invoke limiter(6);
            if (limiter.acquired())
            {
                Auto
                [TheoremProto_0003.LHSPrimaryKey_UInt64 == TheoremProto_0003.RHSPrimaryKey_UInt64]
                [TheoremProto_0003.TotalProofsFound_UInt64 >= TheoremProto_0003.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0003, Axiom);

                Auto
                [TheoremProto_0003.LHSPrimaryKey_UInt64 == TheoremProto_0003.RHSPrimaryKey_UInt64]
                [TheoremProto_0003.TotalProofsFound_UInt64 >= TheoremProto_0003.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0003, Axiom);

                Auto
                [TheoremProto_0004.LHSPrimaryKey_UInt64 == TheoremProto_0004.RHSPrimaryKey_UInt64]
                [TheoremProto_0004.TotalProofsFound_UInt64 >= TheoremProto_0004.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0004, Axiom);

                Auto
                [TheoremProto_0004.LHSPrimaryKey_UInt64 == TheoremProto_0004.RHSPrimaryKey_UInt64]
                [TheoremProto_0004.TotalProofsFound_UInt64 >= TheoremProto_0004.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0004, Axiom);

                Auto
                [TheoremProto_0005.LHSPrimaryKey_UInt64 == TheoremProto_0005.RHSPrimaryKey_UInt64]
                [TheoremProto_0005.TotalProofsFound_UInt64 >= TheoremProto_0005.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0005, Axiom);

                Auto
                [TheoremProto_0005.LHSPrimaryKey_UInt64 == TheoremProto_0005.RHSPrimaryKey_UInt64]
                [TheoremProto_0005.TotalProofsFound_UInt64 >= TheoremProto_0005.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0005, Axiom);

                limiter.release();
            }

        });

    std::for_each(std::execution::par_unseq,
        Axioms_Vec.begin(),
        Axioms_Vec.end(),
        [&](const Axiom_Struct& Axiom)
        {
            RecursionLimiter::Invoke limiter(12);
            if (limiter.acquired())
            {
                Auto
                [TheoremProto_0000.LHSPrimaryKey_UInt64 == TheoremProto_0000.RHSPrimaryKey_UInt64]
                [TheoremProto_0000.TotalProofsFound_UInt64 >= TheoremProto_0000.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0000, Axiom);

                Auto
                [TheoremProto_0000.LHSPrimaryKey_UInt64 == TheoremProto_0000.RHSPrimaryKey_UInt64]
                [TheoremProto_0000.TotalProofsFound_UInt64 >= TheoremProto_0000.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0000, Axiom);

                Auto
                [TheoremProto_0001.LHSPrimaryKey_UInt64 == TheoremProto_0001.RHSPrimaryKey_UInt64]
                [TheoremProto_0001.TotalProofsFound_UInt64 >= TheoremProto_0001.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0001, Axiom);

                Auto
                [TheoremProto_0001.LHSPrimaryKey_UInt64 == TheoremProto_0001.RHSPrimaryKey_UInt64]
                [TheoremProto_0001.TotalProofsFound_UInt64 >= TheoremProto_0001.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0001, Axiom);

                Auto
                [TheoremProto_0002.LHSPrimaryKey_UInt64 == TheoremProto_0002.RHSPrimaryKey_UInt64]
                [TheoremProto_0002.TotalProofsFound_UInt64 >= TheoremProto_0002.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0002, Axiom);

                Auto
                [TheoremProto_0002.LHSPrimaryKey_UInt64 == TheoremProto_0002.RHSPrimaryKey_UInt64]
                [TheoremProto_0002.TotalProofsFound_UInt64 >= TheoremProto_0002.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0002, Axiom);


                Auto
                [TheoremProto_0003.LHSPrimaryKey_UInt64 == TheoremProto_0003.RHSPrimaryKey_UInt64]
                [TheoremProto_0003.TotalProofsFound_UInt64 >= TheoremProto_0003.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0003, Axiom);

                Auto
                [TheoremProto_0003.LHSPrimaryKey_UInt64 == TheoremProto_0003.RHSPrimaryKey_UInt64]
                [TheoremProto_0003.TotalProofsFound_UInt64 >= TheoremProto_0003.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0003, Axiom);

                Auto
                [TheoremProto_0004.LHSPrimaryKey_UInt64 == TheoremProto_0004.RHSPrimaryKey_UInt64]
                [TheoremProto_0004.TotalProofsFound_UInt64 >= TheoremProto_0004.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0004, Axiom);

                Auto
                [TheoremProto_0004.LHSPrimaryKey_UInt64 == TheoremProto_0004.RHSPrimaryKey_UInt64]
                [TheoremProto_0004.TotalProofsFound_UInt64 >= TheoremProto_0004.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0004, Axiom);

                Auto
                [TheoremProto_0005.LHSPrimaryKey_UInt64 == TheoremProto_0005.RHSPrimaryKey_UInt64]
                [TheoremProto_0005.TotalProofsFound_UInt64 >= TheoremProto_0005.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0005, Axiom);

                Auto
                [TheoremProto_0005.LHSPrimaryKey_UInt64 == TheoremProto_0005.RHSPrimaryKey_UInt64]
                [TheoremProto_0005.TotalProofsFound_UInt64 >= TheoremProto_0005.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0005, Axiom);

                limiter.release();
            }

        });

};

Auto
[false]
[true]
[RouteSource_EnumClass::_root]
[Indirection_EnumClass::_auto] =
[](Theorem_Struct InTheorem, const Axiom_Struct& InAxiom) -> void
{
    InTheorem.ProofStack_VecUInt64.push_back(InAxiom);

    if (InTheorem.LHSPrimaryKey_UInt64 == InTheorem.RHSPrimaryKey_UInt64)
    {
        InTheorem.ProofFound_Flag = true;
        ++InTheorem.TotalProofsFound_UInt64;
    }

    if (InTheorem.TotalProofsFound_UInt64 >= InTheorem.MaxAllowedProofs_UInt64)
        return;

    Theorem_Struct TheoremProto_0000 = InTheorem;
    Theorem_Struct TheoremProto_0001 = InTheorem;
    Theorem_Struct TheoremProto_0002 = InTheorem;
    Theorem_Struct TheoremProto_0003 = InTheorem;
    Theorem_Struct TheoremProto_0004 = InTheorem;
    Theorem_Struct TheoremProto_0005 = InTheorem;

    if (TheoremProto_0000.SubnetFound_LHS(InAxiom.LHSPrimaryKey_UInt64))
        TheoremProto_0000.UpdatePrimaryKey_LHS(InAxiom.LHSPrimaryKey_UInt64);

    TheoremProto_0001.UpdatePrimaryKey_RHS(InAxiom.LHSPrimaryKey_UInt64);
    TheoremProto_0002.UpdatePrimaryKey_LHS(InAxiom.LHSPrimaryKey_UInt64);
    TheoremProto_0002.UpdatePrimaryKey_RHS(InAxiom.RHSPrimaryKey_UInt64);

    TheoremProto_0003.UpdatePrimaryKey_LHS(InAxiom.RHSPrimaryKey_UInt64);
    TheoremProto_0004.UpdatePrimaryKey_RHS(InAxiom.RHSPrimaryKey_UInt64);
    TheoremProto_0005.UpdatePrimaryKey_LHS(InAxiom.RHSPrimaryKey_UInt64);
    TheoremProto_0005.UpdatePrimaryKey_RHS(InAxiom.LHSPrimaryKey_UInt64);

    std::for_each(std::execution::par_unseq,
        Axioms_Vec.begin(),
        Axioms_Vec.end(),
        [&](const Axiom_Struct& Axiom)
        {
            RecursionLimiter::Invoke limiter(6);
            if (limiter.acquired())
            {
                Auto
                [TheoremProto_0000.LHSPrimaryKey_UInt64 == TheoremProto_0000.RHSPrimaryKey_UInt64]
                [TheoremProto_0000.TotalProofsFound_UInt64 >= TheoremProto_0000.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0000, Axiom);

                Auto
                [TheoremProto_0000.LHSPrimaryKey_UInt64 == TheoremProto_0000.RHSPrimaryKey_UInt64]
                [TheoremProto_0000.TotalProofsFound_UInt64 >= TheoremProto_0000.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0000, Axiom);

                Auto
                [TheoremProto_0001.LHSPrimaryKey_UInt64 == TheoremProto_0001.RHSPrimaryKey_UInt64]
                [TheoremProto_0001.TotalProofsFound_UInt64 >= TheoremProto_0001.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0001, Axiom);

                Auto
                [TheoremProto_0001.LHSPrimaryKey_UInt64 == TheoremProto_0001.RHSPrimaryKey_UInt64]
                [TheoremProto_0001.TotalProofsFound_UInt64 >= TheoremProto_0001.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0001, Axiom);

                Auto
                [TheoremProto_0002.LHSPrimaryKey_UInt64 == TheoremProto_0002.RHSPrimaryKey_UInt64]
                [TheoremProto_0002.TotalProofsFound_UInt64 >= TheoremProto_0002.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0002, Axiom);

                Auto
                [TheoremProto_0002.LHSPrimaryKey_UInt64 == TheoremProto_0002.RHSPrimaryKey_UInt64]
                [TheoremProto_0002.TotalProofsFound_UInt64 >= TheoremProto_0002.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0002, Axiom);

                limiter.release();
            }

        });

    std::for_each(std::execution::par_unseq,
        Axioms_Vec.begin(),
        Axioms_Vec.end(),
        [&](const Axiom_Struct& Axiom)
        {
            RecursionLimiter::Invoke limiter(6);
            if (limiter.acquired())
            {
                Auto
                [TheoremProto_0003.LHSPrimaryKey_UInt64 == TheoremProto_0003.RHSPrimaryKey_UInt64]
                [TheoremProto_0003.TotalProofsFound_UInt64 >= TheoremProto_0003.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0003, Axiom);

                Auto
                [TheoremProto_0003.LHSPrimaryKey_UInt64 == TheoremProto_0003.RHSPrimaryKey_UInt64]
                [TheoremProto_0003.TotalProofsFound_UInt64 >= TheoremProto_0003.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0003, Axiom);

                Auto
                [TheoremProto_0004.LHSPrimaryKey_UInt64 == TheoremProto_0004.RHSPrimaryKey_UInt64]
                [TheoremProto_0004.TotalProofsFound_UInt64 >= TheoremProto_0004.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0004, Axiom);

                Auto
                [TheoremProto_0004.LHSPrimaryKey_UInt64 == TheoremProto_0004.RHSPrimaryKey_UInt64]
                [TheoremProto_0004.TotalProofsFound_UInt64 >= TheoremProto_0004.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0004, Axiom);

                Auto
                [TheoremProto_0005.LHSPrimaryKey_UInt64 == TheoremProto_0005.RHSPrimaryKey_UInt64]
                [TheoremProto_0005.TotalProofsFound_UInt64 >= TheoremProto_0005.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0005, Axiom);

                Auto
                [TheoremProto_0005.LHSPrimaryKey_UInt64 == TheoremProto_0005.RHSPrimaryKey_UInt64]
                [TheoremProto_0005.TotalProofsFound_UInt64 >= TheoremProto_0005.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0005, Axiom);

                limiter.release();
            }

        });

    std::for_each(std::execution::par_unseq,
        Axioms_Vec.begin(),
        Axioms_Vec.end(),
        [&](const Axiom_Struct& Axiom)
        {
            RecursionLimiter::Invoke limiter(12);
            if (limiter.acquired())
            {
                Auto
                [TheoremProto_0000.LHSPrimaryKey_UInt64 == TheoremProto_0000.RHSPrimaryKey_UInt64]
                [TheoremProto_0000.TotalProofsFound_UInt64 >= TheoremProto_0000.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0000, Axiom);

                Auto
                [TheoremProto_0000.LHSPrimaryKey_UInt64 == TheoremProto_0000.RHSPrimaryKey_UInt64]
                [TheoremProto_0000.TotalProofsFound_UInt64 >= TheoremProto_0000.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0000, Axiom);

                Auto
                [TheoremProto_0001.LHSPrimaryKey_UInt64 == TheoremProto_0001.RHSPrimaryKey_UInt64]
                [TheoremProto_0001.TotalProofsFound_UInt64 >= TheoremProto_0001.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0001, Axiom);

                Auto
                [TheoremProto_0001.LHSPrimaryKey_UInt64 == TheoremProto_0001.RHSPrimaryKey_UInt64]
                [TheoremProto_0001.TotalProofsFound_UInt64 >= TheoremProto_0001.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0001, Axiom);

                Auto
                [TheoremProto_0002.LHSPrimaryKey_UInt64 == TheoremProto_0002.RHSPrimaryKey_UInt64]
                [TheoremProto_0002.TotalProofsFound_UInt64 >= TheoremProto_0002.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0002, Axiom);

                Auto
                [TheoremProto_0002.LHSPrimaryKey_UInt64 == TheoremProto_0002.RHSPrimaryKey_UInt64]
                [TheoremProto_0002.TotalProofsFound_UInt64 >= TheoremProto_0002.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0002, Axiom);


                Auto
                [TheoremProto_0003.LHSPrimaryKey_UInt64 == TheoremProto_0003.RHSPrimaryKey_UInt64]
                [TheoremProto_0003.TotalProofsFound_UInt64 >= TheoremProto_0003.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0003, Axiom);

                Auto
                [TheoremProto_0003.LHSPrimaryKey_UInt64 == TheoremProto_0003.RHSPrimaryKey_UInt64]
                [TheoremProto_0003.TotalProofsFound_UInt64 >= TheoremProto_0003.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0003, Axiom);

                Auto
                [TheoremProto_0004.LHSPrimaryKey_UInt64 == TheoremProto_0004.RHSPrimaryKey_UInt64]
                [TheoremProto_0004.TotalProofsFound_UInt64 >= TheoremProto_0004.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0004, Axiom);

                Auto
                [TheoremProto_0004.LHSPrimaryKey_UInt64 == TheoremProto_0004.RHSPrimaryKey_UInt64]
                [TheoremProto_0004.TotalProofsFound_UInt64 >= TheoremProto_0004.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0004, Axiom);

                Auto
                [TheoremProto_0005.LHSPrimaryKey_UInt64 == TheoremProto_0005.RHSPrimaryKey_UInt64]
                [TheoremProto_0005.TotalProofsFound_UInt64 >= TheoremProto_0005.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0005, Axiom);

                Auto
                [TheoremProto_0005.LHSPrimaryKey_UInt64 == TheoremProto_0005.RHSPrimaryKey_UInt64]
                [TheoremProto_0005.TotalProofsFound_UInt64 >= TheoremProto_0005.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0005, Axiom);

                limiter.release();
            }

        });

};

Auto
[false]
[true]
[RouteSource_EnumClass::_root]
[Indirection_EnumClass::_reduce] =
[](Theorem_Struct InTheorem, const Axiom_Struct& InAxiom) -> void
{
    InTheorem.ProofStack_VecUInt64.push_back(InAxiom);

    if (InTheorem.LHSPrimaryKey_UInt64 == InTheorem.RHSPrimaryKey_UInt64)
    {
        InTheorem.ProofFound_Flag = true;
        ++InTheorem.TotalProofsFound_UInt64;
    }

    if (InTheorem.TotalProofsFound_UInt64 >= InTheorem.MaxAllowedProofs_UInt64)
        return;

    Theorem_Struct TheoremProto_0000 = InTheorem;
    Theorem_Struct TheoremProto_0001 = InTheorem;
    Theorem_Struct TheoremProto_0002 = InTheorem;
    Theorem_Struct TheoremProto_0003 = InTheorem;
    Theorem_Struct TheoremProto_0004 = InTheorem;
    Theorem_Struct TheoremProto_0005 = InTheorem;

    if (TheoremProto_0000.SubnetFound_LHS(InAxiom.LHSPrimaryKey_UInt64))
        TheoremProto_0000.UpdatePrimaryKey_LHS(InAxiom.LHSPrimaryKey_UInt64);

    TheoremProto_0001.UpdatePrimaryKey_RHS(InAxiom.LHSPrimaryKey_UInt64);
    TheoremProto_0002.UpdatePrimaryKey_LHS(InAxiom.LHSPrimaryKey_UInt64);
    TheoremProto_0002.UpdatePrimaryKey_RHS(InAxiom.RHSPrimaryKey_UInt64);

    TheoremProto_0003.UpdatePrimaryKey_LHS(InAxiom.RHSPrimaryKey_UInt64);
    TheoremProto_0004.UpdatePrimaryKey_RHS(InAxiom.RHSPrimaryKey_UInt64);
    TheoremProto_0005.UpdatePrimaryKey_LHS(InAxiom.RHSPrimaryKey_UInt64);
    TheoremProto_0005.UpdatePrimaryKey_RHS(InAxiom.LHSPrimaryKey_UInt64);

    std::for_each(std::execution::par_unseq,
        Axioms_Vec.begin(),
        Axioms_Vec.end(),
        [&](const Axiom_Struct& Axiom)
        {
            RecursionLimiter::Invoke limiter(6);
            if (limiter.acquired())
            {
                Auto
                [TheoremProto_0000.LHSPrimaryKey_UInt64 == TheoremProto_0000.RHSPrimaryKey_UInt64]
                [TheoremProto_0000.TotalProofsFound_UInt64 >= TheoremProto_0000.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0000, Axiom);

                Auto
                [TheoremProto_0000.LHSPrimaryKey_UInt64 == TheoremProto_0000.RHSPrimaryKey_UInt64]
                [TheoremProto_0000.TotalProofsFound_UInt64 >= TheoremProto_0000.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0000, Axiom);

                Auto
                [TheoremProto_0001.LHSPrimaryKey_UInt64 == TheoremProto_0001.RHSPrimaryKey_UInt64]
                [TheoremProto_0001.TotalProofsFound_UInt64 >= TheoremProto_0001.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0001, Axiom);

                Auto
                [TheoremProto_0001.LHSPrimaryKey_UInt64 == TheoremProto_0001.RHSPrimaryKey_UInt64]
                [TheoremProto_0001.TotalProofsFound_UInt64 >= TheoremProto_0001.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0001, Axiom);

                Auto
                [TheoremProto_0002.LHSPrimaryKey_UInt64 == TheoremProto_0002.RHSPrimaryKey_UInt64]
                [TheoremProto_0002.TotalProofsFound_UInt64 >= TheoremProto_0002.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0002, Axiom);

                Auto
                [TheoremProto_0002.LHSPrimaryKey_UInt64 == TheoremProto_0002.RHSPrimaryKey_UInt64]
                [TheoremProto_0002.TotalProofsFound_UInt64 >= TheoremProto_0002.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0002, Axiom);

                limiter.release();
            }

        });

    std::for_each(std::execution::par_unseq,
        Axioms_Vec.begin(),
        Axioms_Vec.end(),
        [&](const Axiom_Struct& Axiom)
        {
            RecursionLimiter::Invoke limiter(6);
            if (limiter.acquired())
            {
                Auto
                [TheoremProto_0003.LHSPrimaryKey_UInt64 == TheoremProto_0003.RHSPrimaryKey_UInt64]
                [TheoremProto_0003.TotalProofsFound_UInt64 >= TheoremProto_0003.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0003, Axiom);

                Auto
                [TheoremProto_0003.LHSPrimaryKey_UInt64 == TheoremProto_0003.RHSPrimaryKey_UInt64]
                [TheoremProto_0003.TotalProofsFound_UInt64 >= TheoremProto_0003.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0003, Axiom);

                Auto
                [TheoremProto_0004.LHSPrimaryKey_UInt64 == TheoremProto_0004.RHSPrimaryKey_UInt64]
                [TheoremProto_0004.TotalProofsFound_UInt64 >= TheoremProto_0004.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0004, Axiom);

                Auto
                [TheoremProto_0004.LHSPrimaryKey_UInt64 == TheoremProto_0004.RHSPrimaryKey_UInt64]
                [TheoremProto_0004.TotalProofsFound_UInt64 >= TheoremProto_0004.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0004, Axiom);

                Auto
                [TheoremProto_0005.LHSPrimaryKey_UInt64 == TheoremProto_0005.RHSPrimaryKey_UInt64]
                [TheoremProto_0005.TotalProofsFound_UInt64 >= TheoremProto_0005.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0005, Axiom);

                Auto
                [TheoremProto_0005.LHSPrimaryKey_UInt64 == TheoremProto_0005.RHSPrimaryKey_UInt64]
                [TheoremProto_0005.TotalProofsFound_UInt64 >= TheoremProto_0005.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0005, Axiom);

                limiter.release();
            }

        });

    std::for_each(std::execution::par_unseq,
        Axioms_Vec.begin(),
        Axioms_Vec.end(),
        [&](const Axiom_Struct& Axiom)
        {
            RecursionLimiter::Invoke limiter(12);
            if (limiter.acquired())
            {
                Auto
                [TheoremProto_0000.LHSPrimaryKey_UInt64 == TheoremProto_0000.RHSPrimaryKey_UInt64]
                [TheoremProto_0000.TotalProofsFound_UInt64 >= TheoremProto_0000.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0000, Axiom);

                Auto
                [TheoremProto_0000.LHSPrimaryKey_UInt64 == TheoremProto_0000.RHSPrimaryKey_UInt64]
                [TheoremProto_0000.TotalProofsFound_UInt64 >= TheoremProto_0000.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0000, Axiom);

                Auto
                [TheoremProto_0001.LHSPrimaryKey_UInt64 == TheoremProto_0001.RHSPrimaryKey_UInt64]
                [TheoremProto_0001.TotalProofsFound_UInt64 >= TheoremProto_0001.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0001, Axiom);

                Auto
                [TheoremProto_0001.LHSPrimaryKey_UInt64 == TheoremProto_0001.RHSPrimaryKey_UInt64]
                [TheoremProto_0001.TotalProofsFound_UInt64 >= TheoremProto_0001.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0001, Axiom);

                Auto
                [TheoremProto_0002.LHSPrimaryKey_UInt64 == TheoremProto_0002.RHSPrimaryKey_UInt64]
                [TheoremProto_0002.TotalProofsFound_UInt64 >= TheoremProto_0002.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0002, Axiom);

                Auto
                [TheoremProto_0002.LHSPrimaryKey_UInt64 == TheoremProto_0002.RHSPrimaryKey_UInt64]
                [TheoremProto_0002.TotalProofsFound_UInt64 >= TheoremProto_0002.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0002, Axiom);


                Auto
                [TheoremProto_0003.LHSPrimaryKey_UInt64 == TheoremProto_0003.RHSPrimaryKey_UInt64]
                [TheoremProto_0003.TotalProofsFound_UInt64 >= TheoremProto_0003.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0003, Axiom);

                Auto
                [TheoremProto_0003.LHSPrimaryKey_UInt64 == TheoremProto_0003.RHSPrimaryKey_UInt64]
                [TheoremProto_0003.TotalProofsFound_UInt64 >= TheoremProto_0003.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0003, Axiom);

                Auto
                [TheoremProto_0004.LHSPrimaryKey_UInt64 == TheoremProto_0004.RHSPrimaryKey_UInt64]
                [TheoremProto_0004.TotalProofsFound_UInt64 >= TheoremProto_0004.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0004, Axiom);

                Auto
                [TheoremProto_0004.LHSPrimaryKey_UInt64 == TheoremProto_0004.RHSPrimaryKey_UInt64]
                [TheoremProto_0004.TotalProofsFound_UInt64 >= TheoremProto_0004.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0004, Axiom);

                Auto
                [TheoremProto_0005.LHSPrimaryKey_UInt64 == TheoremProto_0005.RHSPrimaryKey_UInt64]
                [TheoremProto_0005.TotalProofsFound_UInt64 >= TheoremProto_0005.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0005, Axiom);

                Auto
                [TheoremProto_0005.LHSPrimaryKey_UInt64 == TheoremProto_0005.RHSPrimaryKey_UInt64]
                [TheoremProto_0005.TotalProofsFound_UInt64 >= TheoremProto_0005.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0005, Axiom);

                limiter.release();
            }

        });

};

Auto
[false]
[true]
[RouteSource_EnumClass::_root]
[Indirection_EnumClass::_expand] =
[](Theorem_Struct InTheorem, const Axiom_Struct& InAxiom) -> void
{
    InTheorem.ProofStack_VecUInt64.push_back(InAxiom);

    if (InTheorem.LHSPrimaryKey_UInt64 == InTheorem.RHSPrimaryKey_UInt64)
    {
        InTheorem.ProofFound_Flag = true;
        ++InTheorem.TotalProofsFound_UInt64;
    }

    if (InTheorem.TotalProofsFound_UInt64 >= InTheorem.MaxAllowedProofs_UInt64)
        return;

    Theorem_Struct TheoremProto_0000 = InTheorem;
    Theorem_Struct TheoremProto_0001 = InTheorem;
    Theorem_Struct TheoremProto_0002 = InTheorem;
    Theorem_Struct TheoremProto_0003 = InTheorem;
    Theorem_Struct TheoremProto_0004 = InTheorem;
    Theorem_Struct TheoremProto_0005 = InTheorem;

    if (TheoremProto_0000.SubnetFound_LHS(InAxiom.LHSPrimaryKey_UInt64))
        TheoremProto_0000.UpdatePrimaryKey_LHS(InAxiom.LHSPrimaryKey_UInt64);

    TheoremProto_0001.UpdatePrimaryKey_RHS(InAxiom.LHSPrimaryKey_UInt64);
    TheoremProto_0002.UpdatePrimaryKey_LHS(InAxiom.LHSPrimaryKey_UInt64);
    TheoremProto_0002.UpdatePrimaryKey_RHS(InAxiom.RHSPrimaryKey_UInt64);

    TheoremProto_0003.UpdatePrimaryKey_LHS(InAxiom.RHSPrimaryKey_UInt64);
    TheoremProto_0004.UpdatePrimaryKey_RHS(InAxiom.RHSPrimaryKey_UInt64);
    TheoremProto_0005.UpdatePrimaryKey_LHS(InAxiom.RHSPrimaryKey_UInt64);
    TheoremProto_0005.UpdatePrimaryKey_RHS(InAxiom.LHSPrimaryKey_UInt64);

    std::for_each(std::execution::par_unseq,
        Axioms_Vec.begin(),
        Axioms_Vec.end(),
        [&](const Axiom_Struct& Axiom)
        {
            RecursionLimiter::Invoke limiter(6);
            if (limiter.acquired())
            {
                Auto
                [TheoremProto_0000.LHSPrimaryKey_UInt64 == TheoremProto_0000.RHSPrimaryKey_UInt64]
                [TheoremProto_0000.TotalProofsFound_UInt64 >= TheoremProto_0000.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0000, Axiom);

                Auto
                [TheoremProto_0000.LHSPrimaryKey_UInt64 == TheoremProto_0000.RHSPrimaryKey_UInt64]
                [TheoremProto_0000.TotalProofsFound_UInt64 >= TheoremProto_0000.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0000, Axiom);

                Auto
                [TheoremProto_0001.LHSPrimaryKey_UInt64 == TheoremProto_0001.RHSPrimaryKey_UInt64]
                [TheoremProto_0001.TotalProofsFound_UInt64 >= TheoremProto_0001.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0001, Axiom);

                Auto
                [TheoremProto_0001.LHSPrimaryKey_UInt64 == TheoremProto_0001.RHSPrimaryKey_UInt64]
                [TheoremProto_0001.TotalProofsFound_UInt64 >= TheoremProto_0001.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0001, Axiom);

                Auto
                [TheoremProto_0002.LHSPrimaryKey_UInt64 == TheoremProto_0002.RHSPrimaryKey_UInt64]
                [TheoremProto_0002.TotalProofsFound_UInt64 >= TheoremProto_0002.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0002, Axiom);

                Auto
                [TheoremProto_0002.LHSPrimaryKey_UInt64 == TheoremProto_0002.RHSPrimaryKey_UInt64]
                [TheoremProto_0002.TotalProofsFound_UInt64 >= TheoremProto_0002.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0002, Axiom);

                limiter.release();
            }

        });

    std::for_each(std::execution::par_unseq,
        Axioms_Vec.begin(),
        Axioms_Vec.end(),
        [&](const Axiom_Struct& Axiom)
        {
            RecursionLimiter::Invoke limiter(6);
            if (limiter.acquired())
            {
                Auto
                [TheoremProto_0003.LHSPrimaryKey_UInt64 == TheoremProto_0003.RHSPrimaryKey_UInt64]
                [TheoremProto_0003.TotalProofsFound_UInt64 >= TheoremProto_0003.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0003, Axiom);

                Auto
                [TheoremProto_0003.LHSPrimaryKey_UInt64 == TheoremProto_0003.RHSPrimaryKey_UInt64]
                [TheoremProto_0003.TotalProofsFound_UInt64 >= TheoremProto_0003.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0003, Axiom);

                Auto
                [TheoremProto_0004.LHSPrimaryKey_UInt64 == TheoremProto_0004.RHSPrimaryKey_UInt64]
                [TheoremProto_0004.TotalProofsFound_UInt64 >= TheoremProto_0004.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0004, Axiom);

                Auto
                [TheoremProto_0004.LHSPrimaryKey_UInt64 == TheoremProto_0004.RHSPrimaryKey_UInt64]
                [TheoremProto_0004.TotalProofsFound_UInt64 >= TheoremProto_0004.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0004, Axiom);

                Auto
                [TheoremProto_0005.LHSPrimaryKey_UInt64 == TheoremProto_0005.RHSPrimaryKey_UInt64]
                [TheoremProto_0005.TotalProofsFound_UInt64 >= TheoremProto_0005.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0005, Axiom);

                Auto
                [TheoremProto_0005.LHSPrimaryKey_UInt64 == TheoremProto_0005.RHSPrimaryKey_UInt64]
                [TheoremProto_0005.TotalProofsFound_UInt64 >= TheoremProto_0005.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0005, Axiom);

                limiter.release();
            }

        });

    std::for_each(std::execution::par_unseq,
        Axioms_Vec.begin(),
        Axioms_Vec.end(),
        [&](const Axiom_Struct& Axiom)
        {
            RecursionLimiter::Invoke limiter(12);
            if (limiter.acquired())
            {
                Auto
                [TheoremProto_0000.LHSPrimaryKey_UInt64 == TheoremProto_0000.RHSPrimaryKey_UInt64]
                [TheoremProto_0000.TotalProofsFound_UInt64 >= TheoremProto_0000.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0000, Axiom);

                Auto
                [TheoremProto_0000.LHSPrimaryKey_UInt64 == TheoremProto_0000.RHSPrimaryKey_UInt64]
                [TheoremProto_0000.TotalProofsFound_UInt64 >= TheoremProto_0000.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0000, Axiom);

                Auto
                [TheoremProto_0001.LHSPrimaryKey_UInt64 == TheoremProto_0001.RHSPrimaryKey_UInt64]
                [TheoremProto_0001.TotalProofsFound_UInt64 >= TheoremProto_0001.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0001, Axiom);

                Auto
                [TheoremProto_0001.LHSPrimaryKey_UInt64 == TheoremProto_0001.RHSPrimaryKey_UInt64]
                [TheoremProto_0001.TotalProofsFound_UInt64 >= TheoremProto_0001.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0001, Axiom);

                Auto
                [TheoremProto_0002.LHSPrimaryKey_UInt64 == TheoremProto_0002.RHSPrimaryKey_UInt64]
                [TheoremProto_0002.TotalProofsFound_UInt64 >= TheoremProto_0002.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0002, Axiom);

                Auto
                [TheoremProto_0002.LHSPrimaryKey_UInt64 == TheoremProto_0002.RHSPrimaryKey_UInt64]
                [TheoremProto_0002.TotalProofsFound_UInt64 >= TheoremProto_0002.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0002, Axiom);


                Auto
                [TheoremProto_0003.LHSPrimaryKey_UInt64 == TheoremProto_0003.RHSPrimaryKey_UInt64]
                [TheoremProto_0003.TotalProofsFound_UInt64 >= TheoremProto_0003.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0003, Axiom);

                Auto
                [TheoremProto_0003.LHSPrimaryKey_UInt64 == TheoremProto_0003.RHSPrimaryKey_UInt64]
                [TheoremProto_0003.TotalProofsFound_UInt64 >= TheoremProto_0003.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0003, Axiom);

                Auto
                [TheoremProto_0004.LHSPrimaryKey_UInt64 == TheoremProto_0004.RHSPrimaryKey_UInt64]
                [TheoremProto_0004.TotalProofsFound_UInt64 >= TheoremProto_0004.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0004, Axiom);

                Auto
                [TheoremProto_0004.LHSPrimaryKey_UInt64 == TheoremProto_0004.RHSPrimaryKey_UInt64]
                [TheoremProto_0004.TotalProofsFound_UInt64 >= TheoremProto_0004.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0004, Axiom);

                Auto
                [TheoremProto_0005.LHSPrimaryKey_UInt64 == TheoremProto_0005.RHSPrimaryKey_UInt64]
                [TheoremProto_0005.TotalProofsFound_UInt64 >= TheoremProto_0005.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0005, Axiom);

                Auto
                [TheoremProto_0005.LHSPrimaryKey_UInt64 == TheoremProto_0005.RHSPrimaryKey_UInt64]
                [TheoremProto_0005.TotalProofsFound_UInt64 >= TheoremProto_0005.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0005, Axiom);

                limiter.release();
            }

        });

};

Auto
[false]
[true]
[RouteSource_EnumClass::_lhs]
[Indirection_EnumClass::_auto] =
[](Theorem_Struct InTheorem, const Axiom_Struct& InAxiom) -> void
{
    InTheorem.ProofStack_VecUInt64.push_back(InAxiom);

    if (InTheorem.LHSPrimaryKey_UInt64 == InTheorem.RHSPrimaryKey_UInt64)
    {
        InTheorem.ProofFound_Flag = true;
        ++InTheorem.TotalProofsFound_UInt64;
    }

    if (InTheorem.TotalProofsFound_UInt64 >= InTheorem.MaxAllowedProofs_UInt64)
        return;

    Theorem_Struct TheoremProto_0000 = InTheorem;
    Theorem_Struct TheoremProto_0001 = InTheorem;
    Theorem_Struct TheoremProto_0002 = InTheorem;
    Theorem_Struct TheoremProto_0003 = InTheorem;
    Theorem_Struct TheoremProto_0004 = InTheorem;
    Theorem_Struct TheoremProto_0005 = InTheorem;

    if (TheoremProto_0000.SubnetFound_LHS(InAxiom.LHSPrimaryKey_UInt64))
        TheoremProto_0000.UpdatePrimaryKey_LHS(InAxiom.LHSPrimaryKey_UInt64);

    TheoremProto_0001.UpdatePrimaryKey_RHS(InAxiom.LHSPrimaryKey_UInt64);
    TheoremProto_0002.UpdatePrimaryKey_LHS(InAxiom.LHSPrimaryKey_UInt64);
    TheoremProto_0002.UpdatePrimaryKey_RHS(InAxiom.RHSPrimaryKey_UInt64);

    TheoremProto_0003.UpdatePrimaryKey_LHS(InAxiom.RHSPrimaryKey_UInt64);
    TheoremProto_0004.UpdatePrimaryKey_RHS(InAxiom.RHSPrimaryKey_UInt64);
    TheoremProto_0005.UpdatePrimaryKey_LHS(InAxiom.RHSPrimaryKey_UInt64);
    TheoremProto_0005.UpdatePrimaryKey_RHS(InAxiom.LHSPrimaryKey_UInt64);

    std::for_each(std::execution::par_unseq,
        Axioms_Vec.begin(),
        Axioms_Vec.end(),
        [&](const Axiom_Struct& Axiom)
        {
            RecursionLimiter::Invoke limiter(6);
            if (limiter.acquired())
            {
                Auto
                [TheoremProto_0000.LHSPrimaryKey_UInt64 == TheoremProto_0000.RHSPrimaryKey_UInt64]
                [TheoremProto_0000.TotalProofsFound_UInt64 >= TheoremProto_0000.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0000, Axiom);

                Auto
                [TheoremProto_0000.LHSPrimaryKey_UInt64 == TheoremProto_0000.RHSPrimaryKey_UInt64]
                [TheoremProto_0000.TotalProofsFound_UInt64 >= TheoremProto_0000.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0000, Axiom);

                Auto
                [TheoremProto_0001.LHSPrimaryKey_UInt64 == TheoremProto_0001.RHSPrimaryKey_UInt64]
                [TheoremProto_0001.TotalProofsFound_UInt64 >= TheoremProto_0001.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0001, Axiom);

                Auto
                [TheoremProto_0001.LHSPrimaryKey_UInt64 == TheoremProto_0001.RHSPrimaryKey_UInt64]
                [TheoremProto_0001.TotalProofsFound_UInt64 >= TheoremProto_0001.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0001, Axiom);

                Auto
                [TheoremProto_0002.LHSPrimaryKey_UInt64 == TheoremProto_0002.RHSPrimaryKey_UInt64]
                [TheoremProto_0002.TotalProofsFound_UInt64 >= TheoremProto_0002.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0002, Axiom);

                Auto
                [TheoremProto_0002.LHSPrimaryKey_UInt64 == TheoremProto_0002.RHSPrimaryKey_UInt64]
                [TheoremProto_0002.TotalProofsFound_UInt64 >= TheoremProto_0002.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0002, Axiom);

                limiter.release();
            }

        });

    std::for_each(std::execution::par_unseq,
        Axioms_Vec.begin(),
        Axioms_Vec.end(),
        [&](const Axiom_Struct& Axiom)
        {
            RecursionLimiter::Invoke limiter(6);
            if (limiter.acquired())
            {
                Auto
                [TheoremProto_0003.LHSPrimaryKey_UInt64 == TheoremProto_0003.RHSPrimaryKey_UInt64]
                [TheoremProto_0003.TotalProofsFound_UInt64 >= TheoremProto_0003.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0003, Axiom);

                Auto
                [TheoremProto_0003.LHSPrimaryKey_UInt64 == TheoremProto_0003.RHSPrimaryKey_UInt64]
                [TheoremProto_0003.TotalProofsFound_UInt64 >= TheoremProto_0003.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0003, Axiom);

                Auto
                [TheoremProto_0004.LHSPrimaryKey_UInt64 == TheoremProto_0004.RHSPrimaryKey_UInt64]
                [TheoremProto_0004.TotalProofsFound_UInt64 >= TheoremProto_0004.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0004, Axiom);

                Auto
                [TheoremProto_0004.LHSPrimaryKey_UInt64 == TheoremProto_0004.RHSPrimaryKey_UInt64]
                [TheoremProto_0004.TotalProofsFound_UInt64 >= TheoremProto_0004.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0004, Axiom);

                Auto
                [TheoremProto_0005.LHSPrimaryKey_UInt64 == TheoremProto_0005.RHSPrimaryKey_UInt64]
                [TheoremProto_0005.TotalProofsFound_UInt64 >= TheoremProto_0005.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0005, Axiom);

                Auto
                [TheoremProto_0005.LHSPrimaryKey_UInt64 == TheoremProto_0005.RHSPrimaryKey_UInt64]
                [TheoremProto_0005.TotalProofsFound_UInt64 >= TheoremProto_0005.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0005, Axiom);

                limiter.release();
            }

        });

    std::for_each(std::execution::par_unseq,
        Axioms_Vec.begin(),
        Axioms_Vec.end(),
        [&](const Axiom_Struct& Axiom)
        {
            RecursionLimiter::Invoke limiter(12);
            if (limiter.acquired())
            {
                Auto
                [TheoremProto_0000.LHSPrimaryKey_UInt64 == TheoremProto_0000.RHSPrimaryKey_UInt64]
                [TheoremProto_0000.TotalProofsFound_UInt64 >= TheoremProto_0000.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0000, Axiom);

                Auto
                [TheoremProto_0000.LHSPrimaryKey_UInt64 == TheoremProto_0000.RHSPrimaryKey_UInt64]
                [TheoremProto_0000.TotalProofsFound_UInt64 >= TheoremProto_0000.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0000, Axiom);

                Auto
                [TheoremProto_0001.LHSPrimaryKey_UInt64 == TheoremProto_0001.RHSPrimaryKey_UInt64]
                [TheoremProto_0001.TotalProofsFound_UInt64 >= TheoremProto_0001.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0001, Axiom);

                Auto
                [TheoremProto_0001.LHSPrimaryKey_UInt64 == TheoremProto_0001.RHSPrimaryKey_UInt64]
                [TheoremProto_0001.TotalProofsFound_UInt64 >= TheoremProto_0001.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0001, Axiom);

                Auto
                [TheoremProto_0002.LHSPrimaryKey_UInt64 == TheoremProto_0002.RHSPrimaryKey_UInt64]
                [TheoremProto_0002.TotalProofsFound_UInt64 >= TheoremProto_0002.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0002, Axiom);

                Auto
                [TheoremProto_0002.LHSPrimaryKey_UInt64 == TheoremProto_0002.RHSPrimaryKey_UInt64]
                [TheoremProto_0002.TotalProofsFound_UInt64 >= TheoremProto_0002.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0002, Axiom);


                Auto
                [TheoremProto_0003.LHSPrimaryKey_UInt64 == TheoremProto_0003.RHSPrimaryKey_UInt64]
                [TheoremProto_0003.TotalProofsFound_UInt64 >= TheoremProto_0003.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0003, Axiom);

                Auto
                [TheoremProto_0003.LHSPrimaryKey_UInt64 == TheoremProto_0003.RHSPrimaryKey_UInt64]
                [TheoremProto_0003.TotalProofsFound_UInt64 >= TheoremProto_0003.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0003, Axiom);

                Auto
                [TheoremProto_0004.LHSPrimaryKey_UInt64 == TheoremProto_0004.RHSPrimaryKey_UInt64]
                [TheoremProto_0004.TotalProofsFound_UInt64 >= TheoremProto_0004.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0004, Axiom);

                Auto
                [TheoremProto_0004.LHSPrimaryKey_UInt64 == TheoremProto_0004.RHSPrimaryKey_UInt64]
                [TheoremProto_0004.TotalProofsFound_UInt64 >= TheoremProto_0004.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0004, Axiom);

                Auto
                [TheoremProto_0005.LHSPrimaryKey_UInt64 == TheoremProto_0005.RHSPrimaryKey_UInt64]
                [TheoremProto_0005.TotalProofsFound_UInt64 >= TheoremProto_0005.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0005, Axiom);

                Auto
                [TheoremProto_0005.LHSPrimaryKey_UInt64 == TheoremProto_0005.RHSPrimaryKey_UInt64]
                [TheoremProto_0005.TotalProofsFound_UInt64 >= TheoremProto_0005.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0005, Axiom);

                limiter.release();
            }

        });

};

Auto
[false]
[true]
[RouteSource_EnumClass::_lhs]
[Indirection_EnumClass::_reduce] =
[](Theorem_Struct InTheorem, const Axiom_Struct& InAxiom) -> void
{
    InTheorem.ProofStack_VecUInt64.push_back(InAxiom);

    if (InTheorem.LHSPrimaryKey_UInt64 == InTheorem.RHSPrimaryKey_UInt64)
    {
        InTheorem.ProofFound_Flag = true;
        ++InTheorem.TotalProofsFound_UInt64;
    }

    if (InTheorem.TotalProofsFound_UInt64 >= InTheorem.MaxAllowedProofs_UInt64)
        return;

    Theorem_Struct TheoremProto_0000 = InTheorem;
    Theorem_Struct TheoremProto_0001 = InTheorem;
    Theorem_Struct TheoremProto_0002 = InTheorem;
    Theorem_Struct TheoremProto_0003 = InTheorem;
    Theorem_Struct TheoremProto_0004 = InTheorem;
    Theorem_Struct TheoremProto_0005 = InTheorem;

    if (TheoremProto_0000.SubnetFound_LHS(InAxiom.LHSPrimaryKey_UInt64))
        TheoremProto_0000.UpdatePrimaryKey_LHS(InAxiom.LHSPrimaryKey_UInt64);

    TheoremProto_0001.UpdatePrimaryKey_RHS(InAxiom.LHSPrimaryKey_UInt64);
    TheoremProto_0002.UpdatePrimaryKey_LHS(InAxiom.LHSPrimaryKey_UInt64);
    TheoremProto_0002.UpdatePrimaryKey_RHS(InAxiom.RHSPrimaryKey_UInt64);

    TheoremProto_0003.UpdatePrimaryKey_LHS(InAxiom.RHSPrimaryKey_UInt64);
    TheoremProto_0004.UpdatePrimaryKey_RHS(InAxiom.RHSPrimaryKey_UInt64);
    TheoremProto_0005.UpdatePrimaryKey_LHS(InAxiom.RHSPrimaryKey_UInt64);
    TheoremProto_0005.UpdatePrimaryKey_RHS(InAxiom.LHSPrimaryKey_UInt64);

    std::for_each(std::execution::par_unseq,
        Axioms_Vec.begin(),
        Axioms_Vec.end(),
        [&](const Axiom_Struct& Axiom)
        {
            RecursionLimiter::Invoke limiter(6);
            if (limiter.acquired())
            {
                Auto
                [TheoremProto_0000.LHSPrimaryKey_UInt64 == TheoremProto_0000.RHSPrimaryKey_UInt64]
                [TheoremProto_0000.TotalProofsFound_UInt64 >= TheoremProto_0000.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0000, Axiom);

                Auto
                [TheoremProto_0000.LHSPrimaryKey_UInt64 == TheoremProto_0000.RHSPrimaryKey_UInt64]
                [TheoremProto_0000.TotalProofsFound_UInt64 >= TheoremProto_0000.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0000, Axiom);

                Auto
                [TheoremProto_0001.LHSPrimaryKey_UInt64 == TheoremProto_0001.RHSPrimaryKey_UInt64]
                [TheoremProto_0001.TotalProofsFound_UInt64 >= TheoremProto_0001.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0001, Axiom);

                Auto
                [TheoremProto_0001.LHSPrimaryKey_UInt64 == TheoremProto_0001.RHSPrimaryKey_UInt64]
                [TheoremProto_0001.TotalProofsFound_UInt64 >= TheoremProto_0001.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0001, Axiom);

                Auto
                [TheoremProto_0002.LHSPrimaryKey_UInt64 == TheoremProto_0002.RHSPrimaryKey_UInt64]
                [TheoremProto_0002.TotalProofsFound_UInt64 >= TheoremProto_0002.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0002, Axiom);

                Auto
                [TheoremProto_0002.LHSPrimaryKey_UInt64 == TheoremProto_0002.RHSPrimaryKey_UInt64]
                [TheoremProto_0002.TotalProofsFound_UInt64 >= TheoremProto_0002.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0002, Axiom);

                limiter.release();
            }

        });

    std::for_each(std::execution::par_unseq,
        Axioms_Vec.begin(),
        Axioms_Vec.end(),
        [&](const Axiom_Struct& Axiom)
        {
            RecursionLimiter::Invoke limiter(6);
            if (limiter.acquired())
            {
                Auto
                [TheoremProto_0003.LHSPrimaryKey_UInt64 == TheoremProto_0003.RHSPrimaryKey_UInt64]
                [TheoremProto_0003.TotalProofsFound_UInt64 >= TheoremProto_0003.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0003, Axiom);

                Auto
                [TheoremProto_0003.LHSPrimaryKey_UInt64 == TheoremProto_0003.RHSPrimaryKey_UInt64]
                [TheoremProto_0003.TotalProofsFound_UInt64 >= TheoremProto_0003.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0003, Axiom);

                Auto
                [TheoremProto_0004.LHSPrimaryKey_UInt64 == TheoremProto_0004.RHSPrimaryKey_UInt64]
                [TheoremProto_0004.TotalProofsFound_UInt64 >= TheoremProto_0004.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0004, Axiom);

                Auto
                [TheoremProto_0004.LHSPrimaryKey_UInt64 == TheoremProto_0004.RHSPrimaryKey_UInt64]
                [TheoremProto_0004.TotalProofsFound_UInt64 >= TheoremProto_0004.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0004, Axiom);

                Auto
                [TheoremProto_0005.LHSPrimaryKey_UInt64 == TheoremProto_0005.RHSPrimaryKey_UInt64]
                [TheoremProto_0005.TotalProofsFound_UInt64 >= TheoremProto_0005.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0005, Axiom);

                Auto
                [TheoremProto_0005.LHSPrimaryKey_UInt64 == TheoremProto_0005.RHSPrimaryKey_UInt64]
                [TheoremProto_0005.TotalProofsFound_UInt64 >= TheoremProto_0005.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0005, Axiom);

                limiter.release();
            }

        });

    std::for_each(std::execution::par_unseq,
        Axioms_Vec.begin(),
        Axioms_Vec.end(),
        [&](const Axiom_Struct& Axiom)
        {
            RecursionLimiter::Invoke limiter(12);
            if (limiter.acquired())
            {
                Auto
                [TheoremProto_0000.LHSPrimaryKey_UInt64 == TheoremProto_0000.RHSPrimaryKey_UInt64]
                [TheoremProto_0000.TotalProofsFound_UInt64 >= TheoremProto_0000.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0000, Axiom);

                Auto
                [TheoremProto_0000.LHSPrimaryKey_UInt64 == TheoremProto_0000.RHSPrimaryKey_UInt64]
                [TheoremProto_0000.TotalProofsFound_UInt64 >= TheoremProto_0000.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0000, Axiom);

                Auto
                [TheoremProto_0001.LHSPrimaryKey_UInt64 == TheoremProto_0001.RHSPrimaryKey_UInt64]
                [TheoremProto_0001.TotalProofsFound_UInt64 >= TheoremProto_0001.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0001, Axiom);

                Auto
                [TheoremProto_0001.LHSPrimaryKey_UInt64 == TheoremProto_0001.RHSPrimaryKey_UInt64]
                [TheoremProto_0001.TotalProofsFound_UInt64 >= TheoremProto_0001.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0001, Axiom);

                Auto
                [TheoremProto_0002.LHSPrimaryKey_UInt64 == TheoremProto_0002.RHSPrimaryKey_UInt64]
                [TheoremProto_0002.TotalProofsFound_UInt64 >= TheoremProto_0002.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0002, Axiom);

                Auto
                [TheoremProto_0002.LHSPrimaryKey_UInt64 == TheoremProto_0002.RHSPrimaryKey_UInt64]
                [TheoremProto_0002.TotalProofsFound_UInt64 >= TheoremProto_0002.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0002, Axiom);


                Auto
                [TheoremProto_0003.LHSPrimaryKey_UInt64 == TheoremProto_0003.RHSPrimaryKey_UInt64]
                [TheoremProto_0003.TotalProofsFound_UInt64 >= TheoremProto_0003.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0003, Axiom);

                Auto
                [TheoremProto_0003.LHSPrimaryKey_UInt64 == TheoremProto_0003.RHSPrimaryKey_UInt64]
                [TheoremProto_0003.TotalProofsFound_UInt64 >= TheoremProto_0003.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0003, Axiom);

                Auto
                [TheoremProto_0004.LHSPrimaryKey_UInt64 == TheoremProto_0004.RHSPrimaryKey_UInt64]
                [TheoremProto_0004.TotalProofsFound_UInt64 >= TheoremProto_0004.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0004, Axiom);

                Auto
                [TheoremProto_0004.LHSPrimaryKey_UInt64 == TheoremProto_0004.RHSPrimaryKey_UInt64]
                [TheoremProto_0004.TotalProofsFound_UInt64 >= TheoremProto_0004.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0004, Axiom);

                Auto
                [TheoremProto_0005.LHSPrimaryKey_UInt64 == TheoremProto_0005.RHSPrimaryKey_UInt64]
                [TheoremProto_0005.TotalProofsFound_UInt64 >= TheoremProto_0005.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0005, Axiom);

                Auto
                [TheoremProto_0005.LHSPrimaryKey_UInt64 == TheoremProto_0005.RHSPrimaryKey_UInt64]
                [TheoremProto_0005.TotalProofsFound_UInt64 >= TheoremProto_0005.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0005, Axiom);

                limiter.release();
            }

        });

};

Auto
[false]
[true]
[RouteSource_EnumClass::_lhs]
[Indirection_EnumClass::_expand] =
[](Theorem_Struct InTheorem, const Axiom_Struct& InAxiom) -> void
{
    InTheorem.ProofStack_VecUInt64.push_back(InAxiom);

    if (InTheorem.LHSPrimaryKey_UInt64 == InTheorem.RHSPrimaryKey_UInt64)
    {
        InTheorem.ProofFound_Flag = true;
        ++InTheorem.TotalProofsFound_UInt64;
    }

    if (InTheorem.TotalProofsFound_UInt64 >= InTheorem.MaxAllowedProofs_UInt64)
        return;

    Theorem_Struct TheoremProto_0000 = InTheorem;
    Theorem_Struct TheoremProto_0001 = InTheorem;
    Theorem_Struct TheoremProto_0002 = InTheorem;
    Theorem_Struct TheoremProto_0003 = InTheorem;
    Theorem_Struct TheoremProto_0004 = InTheorem;
    Theorem_Struct TheoremProto_0005 = InTheorem;

    if (TheoremProto_0000.SubnetFound_LHS(InAxiom.LHSPrimaryKey_UInt64))
        TheoremProto_0000.UpdatePrimaryKey_LHS(InAxiom.LHSPrimaryKey_UInt64);

    TheoremProto_0001.UpdatePrimaryKey_RHS(InAxiom.LHSPrimaryKey_UInt64);
    TheoremProto_0002.UpdatePrimaryKey_LHS(InAxiom.LHSPrimaryKey_UInt64);
    TheoremProto_0002.UpdatePrimaryKey_RHS(InAxiom.RHSPrimaryKey_UInt64);

    TheoremProto_0003.UpdatePrimaryKey_LHS(InAxiom.RHSPrimaryKey_UInt64);
    TheoremProto_0004.UpdatePrimaryKey_RHS(InAxiom.RHSPrimaryKey_UInt64);
    TheoremProto_0005.UpdatePrimaryKey_LHS(InAxiom.RHSPrimaryKey_UInt64);
    TheoremProto_0005.UpdatePrimaryKey_RHS(InAxiom.LHSPrimaryKey_UInt64);

    std::for_each(std::execution::par_unseq,
        Axioms_Vec.begin(),
        Axioms_Vec.end(),
        [&](const Axiom_Struct& Axiom)
        {
            RecursionLimiter::Invoke limiter(6);
            if (limiter.acquired())
            {
                Auto
                [TheoremProto_0000.LHSPrimaryKey_UInt64 == TheoremProto_0000.RHSPrimaryKey_UInt64]
                [TheoremProto_0000.TotalProofsFound_UInt64 >= TheoremProto_0000.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0000, Axiom);

                Auto
                [TheoremProto_0000.LHSPrimaryKey_UInt64 == TheoremProto_0000.RHSPrimaryKey_UInt64]
                [TheoremProto_0000.TotalProofsFound_UInt64 >= TheoremProto_0000.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0000, Axiom);

                Auto
                [TheoremProto_0001.LHSPrimaryKey_UInt64 == TheoremProto_0001.RHSPrimaryKey_UInt64]
                [TheoremProto_0001.TotalProofsFound_UInt64 >= TheoremProto_0001.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0001, Axiom);

                Auto
                [TheoremProto_0001.LHSPrimaryKey_UInt64 == TheoremProto_0001.RHSPrimaryKey_UInt64]
                [TheoremProto_0001.TotalProofsFound_UInt64 >= TheoremProto_0001.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0001, Axiom);

                Auto
                [TheoremProto_0002.LHSPrimaryKey_UInt64 == TheoremProto_0002.RHSPrimaryKey_UInt64]
                [TheoremProto_0002.TotalProofsFound_UInt64 >= TheoremProto_0002.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0002, Axiom);

                Auto
                [TheoremProto_0002.LHSPrimaryKey_UInt64 == TheoremProto_0002.RHSPrimaryKey_UInt64]
                [TheoremProto_0002.TotalProofsFound_UInt64 >= TheoremProto_0002.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0002, Axiom);

                limiter.release();
            }

        });

    std::for_each(std::execution::par_unseq,
        Axioms_Vec.begin(),
        Axioms_Vec.end(),
        [&](const Axiom_Struct& Axiom)
        {
            RecursionLimiter::Invoke limiter(6);
            if (limiter.acquired())
            {
                Auto
                [TheoremProto_0003.LHSPrimaryKey_UInt64 == TheoremProto_0003.RHSPrimaryKey_UInt64]
                [TheoremProto_0003.TotalProofsFound_UInt64 >= TheoremProto_0003.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0003, Axiom);

                Auto
                [TheoremProto_0003.LHSPrimaryKey_UInt64 == TheoremProto_0003.RHSPrimaryKey_UInt64]
                [TheoremProto_0003.TotalProofsFound_UInt64 >= TheoremProto_0003.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0003, Axiom);

                Auto
                [TheoremProto_0004.LHSPrimaryKey_UInt64 == TheoremProto_0004.RHSPrimaryKey_UInt64]
                [TheoremProto_0004.TotalProofsFound_UInt64 >= TheoremProto_0004.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0004, Axiom);

                Auto
                [TheoremProto_0004.LHSPrimaryKey_UInt64 == TheoremProto_0004.RHSPrimaryKey_UInt64]
                [TheoremProto_0004.TotalProofsFound_UInt64 >= TheoremProto_0004.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0004, Axiom);

                Auto
                [TheoremProto_0005.LHSPrimaryKey_UInt64 == TheoremProto_0005.RHSPrimaryKey_UInt64]
                [TheoremProto_0005.TotalProofsFound_UInt64 >= TheoremProto_0005.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0005, Axiom);

                Auto
                [TheoremProto_0005.LHSPrimaryKey_UInt64 == TheoremProto_0005.RHSPrimaryKey_UInt64]
                [TheoremProto_0005.TotalProofsFound_UInt64 >= TheoremProto_0005.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0005, Axiom);

                limiter.release();
            }

        });

    std::for_each(std::execution::par_unseq,
        Axioms_Vec.begin(),
        Axioms_Vec.end(),
        [&](const Axiom_Struct& Axiom)
        {
            RecursionLimiter::Invoke limiter(12);
            if (limiter.acquired())
            {
                Auto
                [TheoremProto_0000.LHSPrimaryKey_UInt64 == TheoremProto_0000.RHSPrimaryKey_UInt64]
                [TheoremProto_0000.TotalProofsFound_UInt64 >= TheoremProto_0000.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0000, Axiom);

                Auto
                [TheoremProto_0000.LHSPrimaryKey_UInt64 == TheoremProto_0000.RHSPrimaryKey_UInt64]
                [TheoremProto_0000.TotalProofsFound_UInt64 >= TheoremProto_0000.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0000, Axiom);

                Auto
                [TheoremProto_0001.LHSPrimaryKey_UInt64 == TheoremProto_0001.RHSPrimaryKey_UInt64]
                [TheoremProto_0001.TotalProofsFound_UInt64 >= TheoremProto_0001.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0001, Axiom);

                Auto
                [TheoremProto_0001.LHSPrimaryKey_UInt64 == TheoremProto_0001.RHSPrimaryKey_UInt64]
                [TheoremProto_0001.TotalProofsFound_UInt64 >= TheoremProto_0001.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0001, Axiom);

                Auto
                [TheoremProto_0002.LHSPrimaryKey_UInt64 == TheoremProto_0002.RHSPrimaryKey_UInt64]
                [TheoremProto_0002.TotalProofsFound_UInt64 >= TheoremProto_0002.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0002, Axiom);

                Auto
                [TheoremProto_0002.LHSPrimaryKey_UInt64 == TheoremProto_0002.RHSPrimaryKey_UInt64]
                [TheoremProto_0002.TotalProofsFound_UInt64 >= TheoremProto_0002.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0002, Axiom);


                Auto
                [TheoremProto_0003.LHSPrimaryKey_UInt64 == TheoremProto_0003.RHSPrimaryKey_UInt64]
                [TheoremProto_0003.TotalProofsFound_UInt64 >= TheoremProto_0003.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0003, Axiom);

                Auto
                [TheoremProto_0003.LHSPrimaryKey_UInt64 == TheoremProto_0003.RHSPrimaryKey_UInt64]
                [TheoremProto_0003.TotalProofsFound_UInt64 >= TheoremProto_0003.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0003, Axiom);

                Auto
                [TheoremProto_0004.LHSPrimaryKey_UInt64 == TheoremProto_0004.RHSPrimaryKey_UInt64]
                [TheoremProto_0004.TotalProofsFound_UInt64 >= TheoremProto_0004.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0004, Axiom);

                Auto
                [TheoremProto_0004.LHSPrimaryKey_UInt64 == TheoremProto_0004.RHSPrimaryKey_UInt64]
                [TheoremProto_0004.TotalProofsFound_UInt64 >= TheoremProto_0004.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0004, Axiom);

                Auto
                [TheoremProto_0005.LHSPrimaryKey_UInt64 == TheoremProto_0005.RHSPrimaryKey_UInt64]
                [TheoremProto_0005.TotalProofsFound_UInt64 >= TheoremProto_0005.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0005, Axiom);

                Auto
                [TheoremProto_0005.LHSPrimaryKey_UInt64 == TheoremProto_0005.RHSPrimaryKey_UInt64]
                [TheoremProto_0005.TotalProofsFound_UInt64 >= TheoremProto_0005.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0005, Axiom);

                limiter.release();
            }

        });

};

Auto
[false]
[true]
[RouteSource_EnumClass::_rhs]
[Indirection_EnumClass::_auto] =
[](Theorem_Struct InTheorem, const Axiom_Struct& InAxiom) -> void
{
    InTheorem.ProofStack_VecUInt64.push_back(InAxiom);

    if (InTheorem.LHSPrimaryKey_UInt64 == InTheorem.RHSPrimaryKey_UInt64)
    {
        InTheorem.ProofFound_Flag = true;
        ++InTheorem.TotalProofsFound_UInt64;
    }

    if (InTheorem.TotalProofsFound_UInt64 >= InTheorem.MaxAllowedProofs_UInt64)
        return;

    Theorem_Struct TheoremProto_0000 = InTheorem;
    Theorem_Struct TheoremProto_0001 = InTheorem;
    Theorem_Struct TheoremProto_0002 = InTheorem;
    Theorem_Struct TheoremProto_0003 = InTheorem;
    Theorem_Struct TheoremProto_0004 = InTheorem;
    Theorem_Struct TheoremProto_0005 = InTheorem;

    if (TheoremProto_0000.SubnetFound_LHS(InAxiom.LHSPrimaryKey_UInt64))
        TheoremProto_0000.UpdatePrimaryKey_LHS(InAxiom.LHSPrimaryKey_UInt64);

    TheoremProto_0001.UpdatePrimaryKey_RHS(InAxiom.LHSPrimaryKey_UInt64);
    TheoremProto_0002.UpdatePrimaryKey_LHS(InAxiom.LHSPrimaryKey_UInt64);
    TheoremProto_0002.UpdatePrimaryKey_RHS(InAxiom.RHSPrimaryKey_UInt64);

    TheoremProto_0003.UpdatePrimaryKey_LHS(InAxiom.RHSPrimaryKey_UInt64);
    TheoremProto_0004.UpdatePrimaryKey_RHS(InAxiom.RHSPrimaryKey_UInt64);
    TheoremProto_0005.UpdatePrimaryKey_LHS(InAxiom.RHSPrimaryKey_UInt64);
    TheoremProto_0005.UpdatePrimaryKey_RHS(InAxiom.LHSPrimaryKey_UInt64);

    std::for_each(std::execution::par_unseq,
        Axioms_Vec.begin(),
        Axioms_Vec.end(),
        [&](const Axiom_Struct& Axiom)
        {
            RecursionLimiter::Invoke limiter(6);
            if (limiter.acquired())
            {
                Auto
                [TheoremProto_0000.LHSPrimaryKey_UInt64 == TheoremProto_0000.RHSPrimaryKey_UInt64]
                [TheoremProto_0000.TotalProofsFound_UInt64 >= TheoremProto_0000.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0000, Axiom);

                Auto
                [TheoremProto_0000.LHSPrimaryKey_UInt64 == TheoremProto_0000.RHSPrimaryKey_UInt64]
                [TheoremProto_0000.TotalProofsFound_UInt64 >= TheoremProto_0000.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0000, Axiom);

                Auto
                [TheoremProto_0001.LHSPrimaryKey_UInt64 == TheoremProto_0001.RHSPrimaryKey_UInt64]
                [TheoremProto_0001.TotalProofsFound_UInt64 >= TheoremProto_0001.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0001, Axiom);

                Auto
                [TheoremProto_0001.LHSPrimaryKey_UInt64 == TheoremProto_0001.RHSPrimaryKey_UInt64]
                [TheoremProto_0001.TotalProofsFound_UInt64 >= TheoremProto_0001.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0001, Axiom);

                Auto
                [TheoremProto_0002.LHSPrimaryKey_UInt64 == TheoremProto_0002.RHSPrimaryKey_UInt64]
                [TheoremProto_0002.TotalProofsFound_UInt64 >= TheoremProto_0002.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0002, Axiom);

                Auto
                [TheoremProto_0002.LHSPrimaryKey_UInt64 == TheoremProto_0002.RHSPrimaryKey_UInt64]
                [TheoremProto_0002.TotalProofsFound_UInt64 >= TheoremProto_0002.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0002, Axiom);

                limiter.release();
            }

        });

    std::for_each(std::execution::par_unseq,
        Axioms_Vec.begin(),
        Axioms_Vec.end(),
        [&](const Axiom_Struct& Axiom)
        {
            RecursionLimiter::Invoke limiter(6);
            if (limiter.acquired())
            {
                Auto
                [TheoremProto_0003.LHSPrimaryKey_UInt64 == TheoremProto_0003.RHSPrimaryKey_UInt64]
                [TheoremProto_0003.TotalProofsFound_UInt64 >= TheoremProto_0003.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0003, Axiom);

                Auto
                [TheoremProto_0003.LHSPrimaryKey_UInt64 == TheoremProto_0003.RHSPrimaryKey_UInt64]
                [TheoremProto_0003.TotalProofsFound_UInt64 >= TheoremProto_0003.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0003, Axiom);

                Auto
                [TheoremProto_0004.LHSPrimaryKey_UInt64 == TheoremProto_0004.RHSPrimaryKey_UInt64]
                [TheoremProto_0004.TotalProofsFound_UInt64 >= TheoremProto_0004.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0004, Axiom);

                Auto
                [TheoremProto_0004.LHSPrimaryKey_UInt64 == TheoremProto_0004.RHSPrimaryKey_UInt64]
                [TheoremProto_0004.TotalProofsFound_UInt64 >= TheoremProto_0004.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0004, Axiom);

                Auto
                [TheoremProto_0005.LHSPrimaryKey_UInt64 == TheoremProto_0005.RHSPrimaryKey_UInt64]
                [TheoremProto_0005.TotalProofsFound_UInt64 >= TheoremProto_0005.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0005, Axiom);

                Auto
                [TheoremProto_0005.LHSPrimaryKey_UInt64 == TheoremProto_0005.RHSPrimaryKey_UInt64]
                [TheoremProto_0005.TotalProofsFound_UInt64 >= TheoremProto_0005.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0005, Axiom);

                limiter.release();
            }

        });

    std::for_each(std::execution::par_unseq,
        Axioms_Vec.begin(),
        Axioms_Vec.end(),
        [&](const Axiom_Struct& Axiom)
        {
            RecursionLimiter::Invoke limiter(12);
            if (limiter.acquired())
            {
                Auto
                [TheoremProto_0000.LHSPrimaryKey_UInt64 == TheoremProto_0000.RHSPrimaryKey_UInt64]
                [TheoremProto_0000.TotalProofsFound_UInt64 >= TheoremProto_0000.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0000, Axiom);

                Auto
                [TheoremProto_0000.LHSPrimaryKey_UInt64 == TheoremProto_0000.RHSPrimaryKey_UInt64]
                [TheoremProto_0000.TotalProofsFound_UInt64 >= TheoremProto_0000.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0000, Axiom);

                Auto
                [TheoremProto_0001.LHSPrimaryKey_UInt64 == TheoremProto_0001.RHSPrimaryKey_UInt64]
                [TheoremProto_0001.TotalProofsFound_UInt64 >= TheoremProto_0001.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0001, Axiom);

                Auto
                [TheoremProto_0001.LHSPrimaryKey_UInt64 == TheoremProto_0001.RHSPrimaryKey_UInt64]
                [TheoremProto_0001.TotalProofsFound_UInt64 >= TheoremProto_0001.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0001, Axiom);

                Auto
                [TheoremProto_0002.LHSPrimaryKey_UInt64 == TheoremProto_0002.RHSPrimaryKey_UInt64]
                [TheoremProto_0002.TotalProofsFound_UInt64 >= TheoremProto_0002.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0002, Axiom);

                Auto
                [TheoremProto_0002.LHSPrimaryKey_UInt64 == TheoremProto_0002.RHSPrimaryKey_UInt64]
                [TheoremProto_0002.TotalProofsFound_UInt64 >= TheoremProto_0002.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0002, Axiom);


                Auto
                [TheoremProto_0003.LHSPrimaryKey_UInt64 == TheoremProto_0003.RHSPrimaryKey_UInt64]
                [TheoremProto_0003.TotalProofsFound_UInt64 >= TheoremProto_0003.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0003, Axiom);

                Auto
                [TheoremProto_0003.LHSPrimaryKey_UInt64 == TheoremProto_0003.RHSPrimaryKey_UInt64]
                [TheoremProto_0003.TotalProofsFound_UInt64 >= TheoremProto_0003.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0003, Axiom);

                Auto
                [TheoremProto_0004.LHSPrimaryKey_UInt64 == TheoremProto_0004.RHSPrimaryKey_UInt64]
                [TheoremProto_0004.TotalProofsFound_UInt64 >= TheoremProto_0004.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0004, Axiom);

                Auto
                [TheoremProto_0004.LHSPrimaryKey_UInt64 == TheoremProto_0004.RHSPrimaryKey_UInt64]
                [TheoremProto_0004.TotalProofsFound_UInt64 >= TheoremProto_0004.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0004, Axiom);

                Auto
                [TheoremProto_0005.LHSPrimaryKey_UInt64 == TheoremProto_0005.RHSPrimaryKey_UInt64]
                [TheoremProto_0005.TotalProofsFound_UInt64 >= TheoremProto_0005.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0005, Axiom);

                Auto
                [TheoremProto_0005.LHSPrimaryKey_UInt64 == TheoremProto_0005.RHSPrimaryKey_UInt64]
                [TheoremProto_0005.TotalProofsFound_UInt64 >= TheoremProto_0005.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0005, Axiom);

                limiter.release();
            }

        });

};

Auto
[false]
[true]
[RouteSource_EnumClass::_rhs]
[Indirection_EnumClass::_reduce] =
[](Theorem_Struct InTheorem, const Axiom_Struct& InAxiom) -> void
{
    InTheorem.ProofStack_VecUInt64.push_back(InAxiom);

    if (InTheorem.LHSPrimaryKey_UInt64 == InTheorem.RHSPrimaryKey_UInt64)
    {
        InTheorem.ProofFound_Flag = true;
        ++InTheorem.TotalProofsFound_UInt64;
    }

    if (InTheorem.TotalProofsFound_UInt64 >= InTheorem.MaxAllowedProofs_UInt64)
        return;

    Theorem_Struct TheoremProto_0000 = InTheorem;
    Theorem_Struct TheoremProto_0001 = InTheorem;
    Theorem_Struct TheoremProto_0002 = InTheorem;
    Theorem_Struct TheoremProto_0003 = InTheorem;
    Theorem_Struct TheoremProto_0004 = InTheorem;
    Theorem_Struct TheoremProto_0005 = InTheorem;

    if (TheoremProto_0000.SubnetFound_LHS(InAxiom.LHSPrimaryKey_UInt64))
        TheoremProto_0000.UpdatePrimaryKey_LHS(InAxiom.LHSPrimaryKey_UInt64);

    TheoremProto_0001.UpdatePrimaryKey_RHS(InAxiom.LHSPrimaryKey_UInt64);
    TheoremProto_0002.UpdatePrimaryKey_LHS(InAxiom.LHSPrimaryKey_UInt64);
    TheoremProto_0002.UpdatePrimaryKey_RHS(InAxiom.RHSPrimaryKey_UInt64);

    TheoremProto_0003.UpdatePrimaryKey_LHS(InAxiom.RHSPrimaryKey_UInt64);
    TheoremProto_0004.UpdatePrimaryKey_RHS(InAxiom.RHSPrimaryKey_UInt64);
    TheoremProto_0005.UpdatePrimaryKey_LHS(InAxiom.RHSPrimaryKey_UInt64);
    TheoremProto_0005.UpdatePrimaryKey_RHS(InAxiom.LHSPrimaryKey_UInt64);

    std::for_each(std::execution::par_unseq,
        Axioms_Vec.begin(),
        Axioms_Vec.end(),
        [&](const Axiom_Struct& Axiom)
        {
            RecursionLimiter::Invoke limiter(6);
            if (limiter.acquired())
            {
                Auto
                [TheoremProto_0000.LHSPrimaryKey_UInt64 == TheoremProto_0000.RHSPrimaryKey_UInt64]
                [TheoremProto_0000.TotalProofsFound_UInt64 >= TheoremProto_0000.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0000, Axiom);

                Auto
                [TheoremProto_0000.LHSPrimaryKey_UInt64 == TheoremProto_0000.RHSPrimaryKey_UInt64]
                [TheoremProto_0000.TotalProofsFound_UInt64 >= TheoremProto_0000.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0000, Axiom);

                Auto
                [TheoremProto_0001.LHSPrimaryKey_UInt64 == TheoremProto_0001.RHSPrimaryKey_UInt64]
                [TheoremProto_0001.TotalProofsFound_UInt64 >= TheoremProto_0001.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0001, Axiom);

                Auto
                [TheoremProto_0001.LHSPrimaryKey_UInt64 == TheoremProto_0001.RHSPrimaryKey_UInt64]
                [TheoremProto_0001.TotalProofsFound_UInt64 >= TheoremProto_0001.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0001, Axiom);

                Auto
                [TheoremProto_0002.LHSPrimaryKey_UInt64 == TheoremProto_0002.RHSPrimaryKey_UInt64]
                [TheoremProto_0002.TotalProofsFound_UInt64 >= TheoremProto_0002.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0002, Axiom);

                Auto
                [TheoremProto_0002.LHSPrimaryKey_UInt64 == TheoremProto_0002.RHSPrimaryKey_UInt64]
                [TheoremProto_0002.TotalProofsFound_UInt64 >= TheoremProto_0002.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0002, Axiom);

                limiter.release();
            }

        });

    std::for_each(std::execution::par_unseq,
        Axioms_Vec.begin(),
        Axioms_Vec.end(),
        [&](const Axiom_Struct& Axiom)
        {
            RecursionLimiter::Invoke limiter(6);
            if (limiter.acquired())
            {
                Auto
                [TheoremProto_0003.LHSPrimaryKey_UInt64 == TheoremProto_0003.RHSPrimaryKey_UInt64]
                [TheoremProto_0003.TotalProofsFound_UInt64 >= TheoremProto_0003.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0003, Axiom);

                Auto
                [TheoremProto_0003.LHSPrimaryKey_UInt64 == TheoremProto_0003.RHSPrimaryKey_UInt64]
                [TheoremProto_0003.TotalProofsFound_UInt64 >= TheoremProto_0003.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0003, Axiom);

                Auto
                [TheoremProto_0004.LHSPrimaryKey_UInt64 == TheoremProto_0004.RHSPrimaryKey_UInt64]
                [TheoremProto_0004.TotalProofsFound_UInt64 >= TheoremProto_0004.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0004, Axiom);

                Auto
                [TheoremProto_0004.LHSPrimaryKey_UInt64 == TheoremProto_0004.RHSPrimaryKey_UInt64]
                [TheoremProto_0004.TotalProofsFound_UInt64 >= TheoremProto_0004.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0004, Axiom);

                Auto
                [TheoremProto_0005.LHSPrimaryKey_UInt64 == TheoremProto_0005.RHSPrimaryKey_UInt64]
                [TheoremProto_0005.TotalProofsFound_UInt64 >= TheoremProto_0005.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0005, Axiom);

                Auto
                [TheoremProto_0005.LHSPrimaryKey_UInt64 == TheoremProto_0005.RHSPrimaryKey_UInt64]
                [TheoremProto_0005.TotalProofsFound_UInt64 >= TheoremProto_0005.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0005, Axiom);

                limiter.release();
            }

        });

    std::for_each(std::execution::par_unseq,
        Axioms_Vec.begin(),
        Axioms_Vec.end(),
        [&](const Axiom_Struct& Axiom)
        {
            RecursionLimiter::Invoke limiter(12);
            if (limiter.acquired())
            {
                Auto
                [TheoremProto_0000.LHSPrimaryKey_UInt64 == TheoremProto_0000.RHSPrimaryKey_UInt64]
                [TheoremProto_0000.TotalProofsFound_UInt64 >= TheoremProto_0000.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0000, Axiom);

                Auto
                [TheoremProto_0000.LHSPrimaryKey_UInt64 == TheoremProto_0000.RHSPrimaryKey_UInt64]
                [TheoremProto_0000.TotalProofsFound_UInt64 >= TheoremProto_0000.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0000, Axiom);

                Auto
                [TheoremProto_0001.LHSPrimaryKey_UInt64 == TheoremProto_0001.RHSPrimaryKey_UInt64]
                [TheoremProto_0001.TotalProofsFound_UInt64 >= TheoremProto_0001.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0001, Axiom);

                Auto
                [TheoremProto_0001.LHSPrimaryKey_UInt64 == TheoremProto_0001.RHSPrimaryKey_UInt64]
                [TheoremProto_0001.TotalProofsFound_UInt64 >= TheoremProto_0001.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0001, Axiom);

                Auto
                [TheoremProto_0002.LHSPrimaryKey_UInt64 == TheoremProto_0002.RHSPrimaryKey_UInt64]
                [TheoremProto_0002.TotalProofsFound_UInt64 >= TheoremProto_0002.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0002, Axiom);

                Auto
                [TheoremProto_0002.LHSPrimaryKey_UInt64 == TheoremProto_0002.RHSPrimaryKey_UInt64]
                [TheoremProto_0002.TotalProofsFound_UInt64 >= TheoremProto_0002.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0002, Axiom);


                Auto
                [TheoremProto_0003.LHSPrimaryKey_UInt64 == TheoremProto_0003.RHSPrimaryKey_UInt64]
                [TheoremProto_0003.TotalProofsFound_UInt64 >= TheoremProto_0003.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0003, Axiom);

                Auto
                [TheoremProto_0003.LHSPrimaryKey_UInt64 == TheoremProto_0003.RHSPrimaryKey_UInt64]
                [TheoremProto_0003.TotalProofsFound_UInt64 >= TheoremProto_0003.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0003, Axiom);

                Auto
                [TheoremProto_0004.LHSPrimaryKey_UInt64 == TheoremProto_0004.RHSPrimaryKey_UInt64]
                [TheoremProto_0004.TotalProofsFound_UInt64 >= TheoremProto_0004.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0004, Axiom);

                Auto
                [TheoremProto_0004.LHSPrimaryKey_UInt64 == TheoremProto_0004.RHSPrimaryKey_UInt64]
                [TheoremProto_0004.TotalProofsFound_UInt64 >= TheoremProto_0004.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0004, Axiom);

                Auto
                [TheoremProto_0005.LHSPrimaryKey_UInt64 == TheoremProto_0005.RHSPrimaryKey_UInt64]
                [TheoremProto_0005.TotalProofsFound_UInt64 >= TheoremProto_0005.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0005, Axiom);

                Auto
                [TheoremProto_0005.LHSPrimaryKey_UInt64 == TheoremProto_0005.RHSPrimaryKey_UInt64]
                [TheoremProto_0005.TotalProofsFound_UInt64 >= TheoremProto_0005.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0005, Axiom);

                limiter.release();
            }

        });

};

Auto
[false]
[true]
[RouteSource_EnumClass::_rhs]
[Indirection_EnumClass::_expand] =
[](Theorem_Struct InTheorem, const Axiom_Struct& InAxiom) -> void
{
    InTheorem.ProofStack_VecUInt64.push_back(InAxiom);

    if (InTheorem.LHSPrimaryKey_UInt64 == InTheorem.RHSPrimaryKey_UInt64)
    {
        InTheorem.ProofFound_Flag = true;
        ++InTheorem.TotalProofsFound_UInt64;
    }

    if (InTheorem.TotalProofsFound_UInt64 >= InTheorem.MaxAllowedProofs_UInt64)
        return;

    Theorem_Struct TheoremProto_0000 = InTheorem;
    Theorem_Struct TheoremProto_0001 = InTheorem;
    Theorem_Struct TheoremProto_0002 = InTheorem;
    Theorem_Struct TheoremProto_0003 = InTheorem;
    Theorem_Struct TheoremProto_0004 = InTheorem;
    Theorem_Struct TheoremProto_0005 = InTheorem;

    if (TheoremProto_0000.SubnetFound_LHS(InAxiom.LHSPrimaryKey_UInt64))
        TheoremProto_0000.UpdatePrimaryKey_LHS(InAxiom.LHSPrimaryKey_UInt64);

    TheoremProto_0001.UpdatePrimaryKey_RHS(InAxiom.LHSPrimaryKey_UInt64);
    TheoremProto_0002.UpdatePrimaryKey_LHS(InAxiom.LHSPrimaryKey_UInt64);
    TheoremProto_0002.UpdatePrimaryKey_RHS(InAxiom.RHSPrimaryKey_UInt64);

    TheoremProto_0003.UpdatePrimaryKey_LHS(InAxiom.RHSPrimaryKey_UInt64);
    TheoremProto_0004.UpdatePrimaryKey_RHS(InAxiom.RHSPrimaryKey_UInt64);
    TheoremProto_0005.UpdatePrimaryKey_LHS(InAxiom.RHSPrimaryKey_UInt64);
    TheoremProto_0005.UpdatePrimaryKey_RHS(InAxiom.LHSPrimaryKey_UInt64);

    std::for_each(std::execution::par_unseq,
        Axioms_Vec.begin(),
        Axioms_Vec.end(),
        [&](const Axiom_Struct& Axiom)
        {
            RecursionLimiter::Invoke limiter(6);
            if (limiter.acquired())
            {
                Auto
                [TheoremProto_0000.LHSPrimaryKey_UInt64 == TheoremProto_0000.RHSPrimaryKey_UInt64]
                [TheoremProto_0000.TotalProofsFound_UInt64 >= TheoremProto_0000.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0000, Axiom);

                Auto
                [TheoremProto_0000.LHSPrimaryKey_UInt64 == TheoremProto_0000.RHSPrimaryKey_UInt64]
                [TheoremProto_0000.TotalProofsFound_UInt64 >= TheoremProto_0000.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0000, Axiom);

                Auto
                [TheoremProto_0001.LHSPrimaryKey_UInt64 == TheoremProto_0001.RHSPrimaryKey_UInt64]
                [TheoremProto_0001.TotalProofsFound_UInt64 >= TheoremProto_0001.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0001, Axiom);

                Auto
                [TheoremProto_0001.LHSPrimaryKey_UInt64 == TheoremProto_0001.RHSPrimaryKey_UInt64]
                [TheoremProto_0001.TotalProofsFound_UInt64 >= TheoremProto_0001.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0001, Axiom);

                Auto
                [TheoremProto_0002.LHSPrimaryKey_UInt64 == TheoremProto_0002.RHSPrimaryKey_UInt64]
                [TheoremProto_0002.TotalProofsFound_UInt64 >= TheoremProto_0002.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0002, Axiom);

                Auto
                [TheoremProto_0002.LHSPrimaryKey_UInt64 == TheoremProto_0002.RHSPrimaryKey_UInt64]
                [TheoremProto_0002.TotalProofsFound_UInt64 >= TheoremProto_0002.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0002, Axiom);

                limiter.release();
            }

        });

    std::for_each(std::execution::par_unseq,
        Axioms_Vec.begin(),
        Axioms_Vec.end(),
        [&](const Axiom_Struct& Axiom)
        {
            RecursionLimiter::Invoke limiter(6);
            if (limiter.acquired())
            {
                Auto
                [TheoremProto_0003.LHSPrimaryKey_UInt64 == TheoremProto_0003.RHSPrimaryKey_UInt64]
                [TheoremProto_0003.TotalProofsFound_UInt64 >= TheoremProto_0003.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0003, Axiom);

                Auto
                [TheoremProto_0003.LHSPrimaryKey_UInt64 == TheoremProto_0003.RHSPrimaryKey_UInt64]
                [TheoremProto_0003.TotalProofsFound_UInt64 >= TheoremProto_0003.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0003, Axiom);

                Auto
                [TheoremProto_0004.LHSPrimaryKey_UInt64 == TheoremProto_0004.RHSPrimaryKey_UInt64]
                [TheoremProto_0004.TotalProofsFound_UInt64 >= TheoremProto_0004.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0004, Axiom);

                Auto
                [TheoremProto_0004.LHSPrimaryKey_UInt64 == TheoremProto_0004.RHSPrimaryKey_UInt64]
                [TheoremProto_0004.TotalProofsFound_UInt64 >= TheoremProto_0004.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0004, Axiom);

                Auto
                [TheoremProto_0005.LHSPrimaryKey_UInt64 == TheoremProto_0005.RHSPrimaryKey_UInt64]
                [TheoremProto_0005.TotalProofsFound_UInt64 >= TheoremProto_0005.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0005, Axiom);

                Auto
                [TheoremProto_0005.LHSPrimaryKey_UInt64 == TheoremProto_0005.RHSPrimaryKey_UInt64]
                [TheoremProto_0005.TotalProofsFound_UInt64 >= TheoremProto_0005.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0005, Axiom);

                limiter.release();
            }

        });

    std::for_each(std::execution::par_unseq,
        Axioms_Vec.begin(),
        Axioms_Vec.end(),
        [&](const Axiom_Struct& Axiom)
        {
            RecursionLimiter::Invoke limiter(12);
            if (limiter.acquired())
            {
                Auto
                [TheoremProto_0000.LHSPrimaryKey_UInt64 == TheoremProto_0000.RHSPrimaryKey_UInt64]
                [TheoremProto_0000.TotalProofsFound_UInt64 >= TheoremProto_0000.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0000, Axiom);

                Auto
                [TheoremProto_0000.LHSPrimaryKey_UInt64 == TheoremProto_0000.RHSPrimaryKey_UInt64]
                [TheoremProto_0000.TotalProofsFound_UInt64 >= TheoremProto_0000.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0000, Axiom);

                Auto
                [TheoremProto_0001.LHSPrimaryKey_UInt64 == TheoremProto_0001.RHSPrimaryKey_UInt64]
                [TheoremProto_0001.TotalProofsFound_UInt64 >= TheoremProto_0001.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0001, Axiom);

                Auto
                [TheoremProto_0001.LHSPrimaryKey_UInt64 == TheoremProto_0001.RHSPrimaryKey_UInt64]
                [TheoremProto_0001.TotalProofsFound_UInt64 >= TheoremProto_0001.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0001, Axiom);

                Auto
                [TheoremProto_0002.LHSPrimaryKey_UInt64 == TheoremProto_0002.RHSPrimaryKey_UInt64]
                [TheoremProto_0002.TotalProofsFound_UInt64 >= TheoremProto_0002.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0002, Axiom);

                Auto
                [TheoremProto_0002.LHSPrimaryKey_UInt64 == TheoremProto_0002.RHSPrimaryKey_UInt64]
                [TheoremProto_0002.TotalProofsFound_UInt64 >= TheoremProto_0002.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0002, Axiom);


                Auto
                [TheoremProto_0003.LHSPrimaryKey_UInt64 == TheoremProto_0003.RHSPrimaryKey_UInt64]
                [TheoremProto_0003.TotalProofsFound_UInt64 >= TheoremProto_0003.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0003, Axiom);

                Auto
                [TheoremProto_0003.LHSPrimaryKey_UInt64 == TheoremProto_0003.RHSPrimaryKey_UInt64]
                [TheoremProto_0003.TotalProofsFound_UInt64 >= TheoremProto_0003.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0003, Axiom);

                Auto
                [TheoremProto_0004.LHSPrimaryKey_UInt64 == TheoremProto_0004.RHSPrimaryKey_UInt64]
                [TheoremProto_0004.TotalProofsFound_UInt64 >= TheoremProto_0004.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0004, Axiom);

                Auto
                [TheoremProto_0004.LHSPrimaryKey_UInt64 == TheoremProto_0004.RHSPrimaryKey_UInt64]
                [TheoremProto_0004.TotalProofsFound_UInt64 >= TheoremProto_0004.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0004, Axiom);

                Auto
                [TheoremProto_0005.LHSPrimaryKey_UInt64 == TheoremProto_0005.RHSPrimaryKey_UInt64]
                [TheoremProto_0005.TotalProofsFound_UInt64 >= TheoremProto_0005.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0005, Axiom);

                Auto
                [TheoremProto_0005.LHSPrimaryKey_UInt64 == TheoremProto_0005.RHSPrimaryKey_UInt64]
                [TheoremProto_0005.TotalProofsFound_UInt64 >= TheoremProto_0005.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0005, Axiom);

                limiter.release();
            }

        });

};

Auto
[true]
[false]
[RouteSource_EnumClass::_root]
[Indirection_EnumClass::_auto] =
[](Theorem_Struct InTheorem, const Axiom_Struct& InAxiom) -> void
{
    InTheorem.ProofStack_VecUInt64.push_back(InAxiom);

    if (InTheorem.LHSPrimaryKey_UInt64 == InTheorem.RHSPrimaryKey_UInt64)
    {
        InTheorem.ProofFound_Flag = true;
        ++InTheorem.TotalProofsFound_UInt64;
    }

    if (InTheorem.TotalProofsFound_UInt64 >= InTheorem.MaxAllowedProofs_UInt64)
        return;

    Theorem_Struct TheoremProto_0000 = InTheorem;
    Theorem_Struct TheoremProto_0001 = InTheorem;
    Theorem_Struct TheoremProto_0002 = InTheorem;
    Theorem_Struct TheoremProto_0003 = InTheorem;
    Theorem_Struct TheoremProto_0004 = InTheorem;
    Theorem_Struct TheoremProto_0005 = InTheorem;

    if (TheoremProto_0000.SubnetFound_LHS(InAxiom.LHSPrimaryKey_UInt64))
        TheoremProto_0000.UpdatePrimaryKey_LHS(InAxiom.LHSPrimaryKey_UInt64);

    TheoremProto_0001.UpdatePrimaryKey_RHS(InAxiom.LHSPrimaryKey_UInt64);
    TheoremProto_0002.UpdatePrimaryKey_LHS(InAxiom.LHSPrimaryKey_UInt64);
    TheoremProto_0002.UpdatePrimaryKey_RHS(InAxiom.RHSPrimaryKey_UInt64);

    TheoremProto_0003.UpdatePrimaryKey_LHS(InAxiom.RHSPrimaryKey_UInt64);
    TheoremProto_0004.UpdatePrimaryKey_RHS(InAxiom.RHSPrimaryKey_UInt64);
    TheoremProto_0005.UpdatePrimaryKey_LHS(InAxiom.RHSPrimaryKey_UInt64);
    TheoremProto_0005.UpdatePrimaryKey_RHS(InAxiom.LHSPrimaryKey_UInt64);

    std::for_each(std::execution::par_unseq,
        Axioms_Vec.begin(),
        Axioms_Vec.end(),
        [&](const Axiom_Struct& Axiom)
        {
            RecursionLimiter::Invoke limiter(6);
            if (limiter.acquired())
            {
                Auto
                [TheoremProto_0000.LHSPrimaryKey_UInt64 == TheoremProto_0000.RHSPrimaryKey_UInt64]
                [TheoremProto_0000.TotalProofsFound_UInt64 >= TheoremProto_0000.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0000, Axiom);

                Auto
                [TheoremProto_0000.LHSPrimaryKey_UInt64 == TheoremProto_0000.RHSPrimaryKey_UInt64]
                [TheoremProto_0000.TotalProofsFound_UInt64 >= TheoremProto_0000.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0000, Axiom);

                Auto
                [TheoremProto_0001.LHSPrimaryKey_UInt64 == TheoremProto_0001.RHSPrimaryKey_UInt64]
                [TheoremProto_0001.TotalProofsFound_UInt64 >= TheoremProto_0001.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0001, Axiom);

                Auto
                [TheoremProto_0001.LHSPrimaryKey_UInt64 == TheoremProto_0001.RHSPrimaryKey_UInt64]
                [TheoremProto_0001.TotalProofsFound_UInt64 >= TheoremProto_0001.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0001, Axiom);

                Auto
                [TheoremProto_0002.LHSPrimaryKey_UInt64 == TheoremProto_0002.RHSPrimaryKey_UInt64]
                [TheoremProto_0002.TotalProofsFound_UInt64 >= TheoremProto_0002.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0002, Axiom);

                Auto
                [TheoremProto_0002.LHSPrimaryKey_UInt64 == TheoremProto_0002.RHSPrimaryKey_UInt64]
                [TheoremProto_0002.TotalProofsFound_UInt64 >= TheoremProto_0002.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0002, Axiom);

                limiter.release();
            }

        });

    std::for_each(std::execution::par_unseq,
        Axioms_Vec.begin(),
        Axioms_Vec.end(),
        [&](const Axiom_Struct& Axiom)
        {
            RecursionLimiter::Invoke limiter(6);
            if (limiter.acquired())
            {
                Auto
                [TheoremProto_0003.LHSPrimaryKey_UInt64 == TheoremProto_0003.RHSPrimaryKey_UInt64]
                [TheoremProto_0003.TotalProofsFound_UInt64 >= TheoremProto_0003.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0003, Axiom);

                Auto
                [TheoremProto_0003.LHSPrimaryKey_UInt64 == TheoremProto_0003.RHSPrimaryKey_UInt64]
                [TheoremProto_0003.TotalProofsFound_UInt64 >= TheoremProto_0003.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0003, Axiom);

                Auto
                [TheoremProto_0004.LHSPrimaryKey_UInt64 == TheoremProto_0004.RHSPrimaryKey_UInt64]
                [TheoremProto_0004.TotalProofsFound_UInt64 >= TheoremProto_0004.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0004, Axiom);

                Auto
                [TheoremProto_0004.LHSPrimaryKey_UInt64 == TheoremProto_0004.RHSPrimaryKey_UInt64]
                [TheoremProto_0004.TotalProofsFound_UInt64 >= TheoremProto_0004.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0004, Axiom);

                Auto
                [TheoremProto_0005.LHSPrimaryKey_UInt64 == TheoremProto_0005.RHSPrimaryKey_UInt64]
                [TheoremProto_0005.TotalProofsFound_UInt64 >= TheoremProto_0005.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0005, Axiom);

                Auto
                [TheoremProto_0005.LHSPrimaryKey_UInt64 == TheoremProto_0005.RHSPrimaryKey_UInt64]
                [TheoremProto_0005.TotalProofsFound_UInt64 >= TheoremProto_0005.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0005, Axiom);

                limiter.release();
            }

        });

    std::for_each(std::execution::par_unseq,
        Axioms_Vec.begin(),
        Axioms_Vec.end(),
        [&](const Axiom_Struct& Axiom)
        {
            RecursionLimiter::Invoke limiter(12);
            if (limiter.acquired())
            {
                Auto
                [TheoremProto_0000.LHSPrimaryKey_UInt64 == TheoremProto_0000.RHSPrimaryKey_UInt64]
                [TheoremProto_0000.TotalProofsFound_UInt64 >= TheoremProto_0000.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0000, Axiom);

                Auto
                [TheoremProto_0000.LHSPrimaryKey_UInt64 == TheoremProto_0000.RHSPrimaryKey_UInt64]
                [TheoremProto_0000.TotalProofsFound_UInt64 >= TheoremProto_0000.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0000, Axiom);

                Auto
                [TheoremProto_0001.LHSPrimaryKey_UInt64 == TheoremProto_0001.RHSPrimaryKey_UInt64]
                [TheoremProto_0001.TotalProofsFound_UInt64 >= TheoremProto_0001.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0001, Axiom);

                Auto
                [TheoremProto_0001.LHSPrimaryKey_UInt64 == TheoremProto_0001.RHSPrimaryKey_UInt64]
                [TheoremProto_0001.TotalProofsFound_UInt64 >= TheoremProto_0001.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0001, Axiom);

                Auto
                [TheoremProto_0002.LHSPrimaryKey_UInt64 == TheoremProto_0002.RHSPrimaryKey_UInt64]
                [TheoremProto_0002.TotalProofsFound_UInt64 >= TheoremProto_0002.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0002, Axiom);

                Auto
                [TheoremProto_0002.LHSPrimaryKey_UInt64 == TheoremProto_0002.RHSPrimaryKey_UInt64]
                [TheoremProto_0002.TotalProofsFound_UInt64 >= TheoremProto_0002.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0002, Axiom);


                Auto
                [TheoremProto_0003.LHSPrimaryKey_UInt64 == TheoremProto_0003.RHSPrimaryKey_UInt64]
                [TheoremProto_0003.TotalProofsFound_UInt64 >= TheoremProto_0003.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0003, Axiom);

                Auto
                [TheoremProto_0003.LHSPrimaryKey_UInt64 == TheoremProto_0003.RHSPrimaryKey_UInt64]
                [TheoremProto_0003.TotalProofsFound_UInt64 >= TheoremProto_0003.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0003, Axiom);

                Auto
                [TheoremProto_0004.LHSPrimaryKey_UInt64 == TheoremProto_0004.RHSPrimaryKey_UInt64]
                [TheoremProto_0004.TotalProofsFound_UInt64 >= TheoremProto_0004.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0004, Axiom);

                Auto
                [TheoremProto_0004.LHSPrimaryKey_UInt64 == TheoremProto_0004.RHSPrimaryKey_UInt64]
                [TheoremProto_0004.TotalProofsFound_UInt64 >= TheoremProto_0004.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0004, Axiom);

                Auto
                [TheoremProto_0005.LHSPrimaryKey_UInt64 == TheoremProto_0005.RHSPrimaryKey_UInt64]
                [TheoremProto_0005.TotalProofsFound_UInt64 >= TheoremProto_0005.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0005, Axiom);

                Auto
                [TheoremProto_0005.LHSPrimaryKey_UInt64 == TheoremProto_0005.RHSPrimaryKey_UInt64]
                [TheoremProto_0005.TotalProofsFound_UInt64 >= TheoremProto_0005.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0005, Axiom);

                limiter.release();
            }

        });

};

Auto
[true]
[false]
[RouteSource_EnumClass::_root]
[Indirection_EnumClass::_reduce] =
[](Theorem_Struct InTheorem, const Axiom_Struct& InAxiom) -> void
{
    InTheorem.ProofStack_VecUInt64.push_back(InAxiom);

    if (InTheorem.LHSPrimaryKey_UInt64 == InTheorem.RHSPrimaryKey_UInt64)
    {
        InTheorem.ProofFound_Flag = true;
        ++InTheorem.TotalProofsFound_UInt64;
    }

    if (InTheorem.TotalProofsFound_UInt64 >= InTheorem.MaxAllowedProofs_UInt64)
        return;

    Theorem_Struct TheoremProto_0000 = InTheorem;
    Theorem_Struct TheoremProto_0001 = InTheorem;
    Theorem_Struct TheoremProto_0002 = InTheorem;
    Theorem_Struct TheoremProto_0003 = InTheorem;
    Theorem_Struct TheoremProto_0004 = InTheorem;
    Theorem_Struct TheoremProto_0005 = InTheorem;

    if (TheoremProto_0000.SubnetFound_LHS(InAxiom.LHSPrimaryKey_UInt64))
        TheoremProto_0000.UpdatePrimaryKey_LHS(InAxiom.LHSPrimaryKey_UInt64);

    TheoremProto_0001.UpdatePrimaryKey_RHS(InAxiom.LHSPrimaryKey_UInt64);
    TheoremProto_0002.UpdatePrimaryKey_LHS(InAxiom.LHSPrimaryKey_UInt64);
    TheoremProto_0002.UpdatePrimaryKey_RHS(InAxiom.RHSPrimaryKey_UInt64);

    TheoremProto_0003.UpdatePrimaryKey_LHS(InAxiom.RHSPrimaryKey_UInt64);
    TheoremProto_0004.UpdatePrimaryKey_RHS(InAxiom.RHSPrimaryKey_UInt64);
    TheoremProto_0005.UpdatePrimaryKey_LHS(InAxiom.RHSPrimaryKey_UInt64);
    TheoremProto_0005.UpdatePrimaryKey_RHS(InAxiom.LHSPrimaryKey_UInt64);

    std::for_each(std::execution::par_unseq,
        Axioms_Vec.begin(),
        Axioms_Vec.end(),
        [&](const Axiom_Struct& Axiom)
        {
            RecursionLimiter::Invoke limiter(6);
            if (limiter.acquired())
            {
                Auto
                [TheoremProto_0000.LHSPrimaryKey_UInt64 == TheoremProto_0000.RHSPrimaryKey_UInt64]
                [TheoremProto_0000.TotalProofsFound_UInt64 >= TheoremProto_0000.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0000, Axiom);

                Auto
                [TheoremProto_0000.LHSPrimaryKey_UInt64 == TheoremProto_0000.RHSPrimaryKey_UInt64]
                [TheoremProto_0000.TotalProofsFound_UInt64 >= TheoremProto_0000.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0000, Axiom);

                Auto
                [TheoremProto_0001.LHSPrimaryKey_UInt64 == TheoremProto_0001.RHSPrimaryKey_UInt64]
                [TheoremProto_0001.TotalProofsFound_UInt64 >= TheoremProto_0001.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0001, Axiom);

                Auto
                [TheoremProto_0001.LHSPrimaryKey_UInt64 == TheoremProto_0001.RHSPrimaryKey_UInt64]
                [TheoremProto_0001.TotalProofsFound_UInt64 >= TheoremProto_0001.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0001, Axiom);

                Auto
                [TheoremProto_0002.LHSPrimaryKey_UInt64 == TheoremProto_0002.RHSPrimaryKey_UInt64]
                [TheoremProto_0002.TotalProofsFound_UInt64 >= TheoremProto_0002.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0002, Axiom);

                Auto
                [TheoremProto_0002.LHSPrimaryKey_UInt64 == TheoremProto_0002.RHSPrimaryKey_UInt64]
                [TheoremProto_0002.TotalProofsFound_UInt64 >= TheoremProto_0002.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0002, Axiom);

                limiter.release();
            }

        });

    std::for_each(std::execution::par_unseq,
        Axioms_Vec.begin(),
        Axioms_Vec.end(),
        [&](const Axiom_Struct& Axiom)
        {
            RecursionLimiter::Invoke limiter(6);
            if (limiter.acquired())
            {
                Auto
                [TheoremProto_0003.LHSPrimaryKey_UInt64 == TheoremProto_0003.RHSPrimaryKey_UInt64]
                [TheoremProto_0003.TotalProofsFound_UInt64 >= TheoremProto_0003.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0003, Axiom);

                Auto
                [TheoremProto_0003.LHSPrimaryKey_UInt64 == TheoremProto_0003.RHSPrimaryKey_UInt64]
                [TheoremProto_0003.TotalProofsFound_UInt64 >= TheoremProto_0003.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0003, Axiom);

                Auto
                [TheoremProto_0004.LHSPrimaryKey_UInt64 == TheoremProto_0004.RHSPrimaryKey_UInt64]
                [TheoremProto_0004.TotalProofsFound_UInt64 >= TheoremProto_0004.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0004, Axiom);

                Auto
                [TheoremProto_0004.LHSPrimaryKey_UInt64 == TheoremProto_0004.RHSPrimaryKey_UInt64]
                [TheoremProto_0004.TotalProofsFound_UInt64 >= TheoremProto_0004.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0004, Axiom);

                Auto
                [TheoremProto_0005.LHSPrimaryKey_UInt64 == TheoremProto_0005.RHSPrimaryKey_UInt64]
                [TheoremProto_0005.TotalProofsFound_UInt64 >= TheoremProto_0005.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0005, Axiom);

                Auto
                [TheoremProto_0005.LHSPrimaryKey_UInt64 == TheoremProto_0005.RHSPrimaryKey_UInt64]
                [TheoremProto_0005.TotalProofsFound_UInt64 >= TheoremProto_0005.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0005, Axiom);

                limiter.release();
            }

        });

    std::for_each(std::execution::par_unseq,
        Axioms_Vec.begin(),
        Axioms_Vec.end(),
        [&](const Axiom_Struct& Axiom)
        {
            RecursionLimiter::Invoke limiter(12);
            if (limiter.acquired())
            {
                Auto
                [TheoremProto_0000.LHSPrimaryKey_UInt64 == TheoremProto_0000.RHSPrimaryKey_UInt64]
                [TheoremProto_0000.TotalProofsFound_UInt64 >= TheoremProto_0000.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0000, Axiom);

                Auto
                [TheoremProto_0000.LHSPrimaryKey_UInt64 == TheoremProto_0000.RHSPrimaryKey_UInt64]
                [TheoremProto_0000.TotalProofsFound_UInt64 >= TheoremProto_0000.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0000, Axiom);

                Auto
                [TheoremProto_0001.LHSPrimaryKey_UInt64 == TheoremProto_0001.RHSPrimaryKey_UInt64]
                [TheoremProto_0001.TotalProofsFound_UInt64 >= TheoremProto_0001.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0001, Axiom);

                Auto
                [TheoremProto_0001.LHSPrimaryKey_UInt64 == TheoremProto_0001.RHSPrimaryKey_UInt64]
                [TheoremProto_0001.TotalProofsFound_UInt64 >= TheoremProto_0001.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0001, Axiom);

                Auto
                [TheoremProto_0002.LHSPrimaryKey_UInt64 == TheoremProto_0002.RHSPrimaryKey_UInt64]
                [TheoremProto_0002.TotalProofsFound_UInt64 >= TheoremProto_0002.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0002, Axiom);

                Auto
                [TheoremProto_0002.LHSPrimaryKey_UInt64 == TheoremProto_0002.RHSPrimaryKey_UInt64]
                [TheoremProto_0002.TotalProofsFound_UInt64 >= TheoremProto_0002.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0002, Axiom);


                Auto
                [TheoremProto_0003.LHSPrimaryKey_UInt64 == TheoremProto_0003.RHSPrimaryKey_UInt64]
                [TheoremProto_0003.TotalProofsFound_UInt64 >= TheoremProto_0003.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0003, Axiom);

                Auto
                [TheoremProto_0003.LHSPrimaryKey_UInt64 == TheoremProto_0003.RHSPrimaryKey_UInt64]
                [TheoremProto_0003.TotalProofsFound_UInt64 >= TheoremProto_0003.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0003, Axiom);

                Auto
                [TheoremProto_0004.LHSPrimaryKey_UInt64 == TheoremProto_0004.RHSPrimaryKey_UInt64]
                [TheoremProto_0004.TotalProofsFound_UInt64 >= TheoremProto_0004.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0004, Axiom);

                Auto
                [TheoremProto_0004.LHSPrimaryKey_UInt64 == TheoremProto_0004.RHSPrimaryKey_UInt64]
                [TheoremProto_0004.TotalProofsFound_UInt64 >= TheoremProto_0004.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0004, Axiom);

                Auto
                [TheoremProto_0005.LHSPrimaryKey_UInt64 == TheoremProto_0005.RHSPrimaryKey_UInt64]
                [TheoremProto_0005.TotalProofsFound_UInt64 >= TheoremProto_0005.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0005, Axiom);

                Auto
                [TheoremProto_0005.LHSPrimaryKey_UInt64 == TheoremProto_0005.RHSPrimaryKey_UInt64]
                [TheoremProto_0005.TotalProofsFound_UInt64 >= TheoremProto_0005.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0005, Axiom);

                limiter.release();
            }

        });

};

Auto
[true]
[false]
[RouteSource_EnumClass::_root]
[Indirection_EnumClass::_expand] =
[](Theorem_Struct InTheorem, const Axiom_Struct& InAxiom) -> void
{
    InTheorem.ProofStack_VecUInt64.push_back(InAxiom);

    if (InTheorem.LHSPrimaryKey_UInt64 == InTheorem.RHSPrimaryKey_UInt64)
    {
        InTheorem.ProofFound_Flag = true;
        ++InTheorem.TotalProofsFound_UInt64;
    }

    if (InTheorem.TotalProofsFound_UInt64 >= InTheorem.MaxAllowedProofs_UInt64)
        return;

    Theorem_Struct TheoremProto_0000 = InTheorem;
    Theorem_Struct TheoremProto_0001 = InTheorem;
    Theorem_Struct TheoremProto_0002 = InTheorem;
    Theorem_Struct TheoremProto_0003 = InTheorem;
    Theorem_Struct TheoremProto_0004 = InTheorem;
    Theorem_Struct TheoremProto_0005 = InTheorem;

    if (TheoremProto_0000.SubnetFound_LHS(InAxiom.LHSPrimaryKey_UInt64))
        TheoremProto_0000.UpdatePrimaryKey_LHS(InAxiom.LHSPrimaryKey_UInt64);

    TheoremProto_0001.UpdatePrimaryKey_RHS(InAxiom.LHSPrimaryKey_UInt64);
    TheoremProto_0002.UpdatePrimaryKey_LHS(InAxiom.LHSPrimaryKey_UInt64);
    TheoremProto_0002.UpdatePrimaryKey_RHS(InAxiom.RHSPrimaryKey_UInt64);

    TheoremProto_0003.UpdatePrimaryKey_LHS(InAxiom.RHSPrimaryKey_UInt64);
    TheoremProto_0004.UpdatePrimaryKey_RHS(InAxiom.RHSPrimaryKey_UInt64);
    TheoremProto_0005.UpdatePrimaryKey_LHS(InAxiom.RHSPrimaryKey_UInt64);
    TheoremProto_0005.UpdatePrimaryKey_RHS(InAxiom.LHSPrimaryKey_UInt64);

    std::for_each(std::execution::par_unseq,
        Axioms_Vec.begin(),
        Axioms_Vec.end(),
        [&](const Axiom_Struct& Axiom)
        {
            RecursionLimiter::Invoke limiter(6);
            if (limiter.acquired())
            {
                Auto
                [TheoremProto_0000.LHSPrimaryKey_UInt64 == TheoremProto_0000.RHSPrimaryKey_UInt64]
                [TheoremProto_0000.TotalProofsFound_UInt64 >= TheoremProto_0000.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0000, Axiom);

                Auto
                [TheoremProto_0000.LHSPrimaryKey_UInt64 == TheoremProto_0000.RHSPrimaryKey_UInt64]
                [TheoremProto_0000.TotalProofsFound_UInt64 >= TheoremProto_0000.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0000, Axiom);

                Auto
                [TheoremProto_0001.LHSPrimaryKey_UInt64 == TheoremProto_0001.RHSPrimaryKey_UInt64]
                [TheoremProto_0001.TotalProofsFound_UInt64 >= TheoremProto_0001.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0001, Axiom);

                Auto
                [TheoremProto_0001.LHSPrimaryKey_UInt64 == TheoremProto_0001.RHSPrimaryKey_UInt64]
                [TheoremProto_0001.TotalProofsFound_UInt64 >= TheoremProto_0001.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0001, Axiom);

                Auto
                [TheoremProto_0002.LHSPrimaryKey_UInt64 == TheoremProto_0002.RHSPrimaryKey_UInt64]
                [TheoremProto_0002.TotalProofsFound_UInt64 >= TheoremProto_0002.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0002, Axiom);

                Auto
                [TheoremProto_0002.LHSPrimaryKey_UInt64 == TheoremProto_0002.RHSPrimaryKey_UInt64]
                [TheoremProto_0002.TotalProofsFound_UInt64 >= TheoremProto_0002.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0002, Axiom);

                limiter.release();
            }

        });

    std::for_each(std::execution::par_unseq,
        Axioms_Vec.begin(),
        Axioms_Vec.end(),
        [&](const Axiom_Struct& Axiom)
        {
            RecursionLimiter::Invoke limiter(6);
            if (limiter.acquired())
            {
                Auto
                [TheoremProto_0003.LHSPrimaryKey_UInt64 == TheoremProto_0003.RHSPrimaryKey_UInt64]
                [TheoremProto_0003.TotalProofsFound_UInt64 >= TheoremProto_0003.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0003, Axiom);

                Auto
                [TheoremProto_0003.LHSPrimaryKey_UInt64 == TheoremProto_0003.RHSPrimaryKey_UInt64]
                [TheoremProto_0003.TotalProofsFound_UInt64 >= TheoremProto_0003.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0003, Axiom);

                Auto
                [TheoremProto_0004.LHSPrimaryKey_UInt64 == TheoremProto_0004.RHSPrimaryKey_UInt64]
                [TheoremProto_0004.TotalProofsFound_UInt64 >= TheoremProto_0004.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0004, Axiom);

                Auto
                [TheoremProto_0004.LHSPrimaryKey_UInt64 == TheoremProto_0004.RHSPrimaryKey_UInt64]
                [TheoremProto_0004.TotalProofsFound_UInt64 >= TheoremProto_0004.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0004, Axiom);

                Auto
                [TheoremProto_0005.LHSPrimaryKey_UInt64 == TheoremProto_0005.RHSPrimaryKey_UInt64]
                [TheoremProto_0005.TotalProofsFound_UInt64 >= TheoremProto_0005.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0005, Axiom);

                Auto
                [TheoremProto_0005.LHSPrimaryKey_UInt64 == TheoremProto_0005.RHSPrimaryKey_UInt64]
                [TheoremProto_0005.TotalProofsFound_UInt64 >= TheoremProto_0005.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0005, Axiom);

                limiter.release();
            }

        });

    std::for_each(std::execution::par_unseq,
        Axioms_Vec.begin(),
        Axioms_Vec.end(),
        [&](const Axiom_Struct& Axiom)
        {
            RecursionLimiter::Invoke limiter(12);
            if (limiter.acquired())
            {
                Auto
                [TheoremProto_0000.LHSPrimaryKey_UInt64 == TheoremProto_0000.RHSPrimaryKey_UInt64]
                [TheoremProto_0000.TotalProofsFound_UInt64 >= TheoremProto_0000.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0000, Axiom);

                Auto
                [TheoremProto_0000.LHSPrimaryKey_UInt64 == TheoremProto_0000.RHSPrimaryKey_UInt64]
                [TheoremProto_0000.TotalProofsFound_UInt64 >= TheoremProto_0000.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0000, Axiom);

                Auto
                [TheoremProto_0001.LHSPrimaryKey_UInt64 == TheoremProto_0001.RHSPrimaryKey_UInt64]
                [TheoremProto_0001.TotalProofsFound_UInt64 >= TheoremProto_0001.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0001, Axiom);

                Auto
                [TheoremProto_0001.LHSPrimaryKey_UInt64 == TheoremProto_0001.RHSPrimaryKey_UInt64]
                [TheoremProto_0001.TotalProofsFound_UInt64 >= TheoremProto_0001.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0001, Axiom);

                Auto
                [TheoremProto_0002.LHSPrimaryKey_UInt64 == TheoremProto_0002.RHSPrimaryKey_UInt64]
                [TheoremProto_0002.TotalProofsFound_UInt64 >= TheoremProto_0002.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0002, Axiom);

                Auto
                [TheoremProto_0002.LHSPrimaryKey_UInt64 == TheoremProto_0002.RHSPrimaryKey_UInt64]
                [TheoremProto_0002.TotalProofsFound_UInt64 >= TheoremProto_0002.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0002, Axiom);


                Auto
                [TheoremProto_0003.LHSPrimaryKey_UInt64 == TheoremProto_0003.RHSPrimaryKey_UInt64]
                [TheoremProto_0003.TotalProofsFound_UInt64 >= TheoremProto_0003.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0003, Axiom);

                Auto
                [TheoremProto_0003.LHSPrimaryKey_UInt64 == TheoremProto_0003.RHSPrimaryKey_UInt64]
                [TheoremProto_0003.TotalProofsFound_UInt64 >= TheoremProto_0003.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0003, Axiom);

                Auto
                [TheoremProto_0004.LHSPrimaryKey_UInt64 == TheoremProto_0004.RHSPrimaryKey_UInt64]
                [TheoremProto_0004.TotalProofsFound_UInt64 >= TheoremProto_0004.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0004, Axiom);

                Auto
                [TheoremProto_0004.LHSPrimaryKey_UInt64 == TheoremProto_0004.RHSPrimaryKey_UInt64]
                [TheoremProto_0004.TotalProofsFound_UInt64 >= TheoremProto_0004.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0004, Axiom);

                Auto
                [TheoremProto_0005.LHSPrimaryKey_UInt64 == TheoremProto_0005.RHSPrimaryKey_UInt64]
                [TheoremProto_0005.TotalProofsFound_UInt64 >= TheoremProto_0005.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0005, Axiom);

                Auto
                [TheoremProto_0005.LHSPrimaryKey_UInt64 == TheoremProto_0005.RHSPrimaryKey_UInt64]
                [TheoremProto_0005.TotalProofsFound_UInt64 >= TheoremProto_0005.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0005, Axiom);

                limiter.release();
            }

        });

};

Auto
[true]
[false]
[RouteSource_EnumClass::_lhs]
[Indirection_EnumClass::_auto] =
[](Theorem_Struct InTheorem, const Axiom_Struct& InAxiom) -> void
{
    InTheorem.ProofStack_VecUInt64.push_back(InAxiom);

    if (InTheorem.LHSPrimaryKey_UInt64 == InTheorem.RHSPrimaryKey_UInt64)
    {
        InTheorem.ProofFound_Flag = true;
        ++InTheorem.TotalProofsFound_UInt64;
    }

    if (InTheorem.TotalProofsFound_UInt64 >= InTheorem.MaxAllowedProofs_UInt64)
        return;

    Theorem_Struct TheoremProto_0000 = InTheorem;
    Theorem_Struct TheoremProto_0001 = InTheorem;
    Theorem_Struct TheoremProto_0002 = InTheorem;
    Theorem_Struct TheoremProto_0003 = InTheorem;
    Theorem_Struct TheoremProto_0004 = InTheorem;
    Theorem_Struct TheoremProto_0005 = InTheorem;

    if (TheoremProto_0000.SubnetFound_LHS(InAxiom.LHSPrimaryKey_UInt64))
        TheoremProto_0000.UpdatePrimaryKey_LHS(InAxiom.LHSPrimaryKey_UInt64);

    TheoremProto_0001.UpdatePrimaryKey_RHS(InAxiom.LHSPrimaryKey_UInt64);
    TheoremProto_0002.UpdatePrimaryKey_LHS(InAxiom.LHSPrimaryKey_UInt64);
    TheoremProto_0002.UpdatePrimaryKey_RHS(InAxiom.RHSPrimaryKey_UInt64);

    TheoremProto_0003.UpdatePrimaryKey_LHS(InAxiom.RHSPrimaryKey_UInt64);
    TheoremProto_0004.UpdatePrimaryKey_RHS(InAxiom.RHSPrimaryKey_UInt64);
    TheoremProto_0005.UpdatePrimaryKey_LHS(InAxiom.RHSPrimaryKey_UInt64);
    TheoremProto_0005.UpdatePrimaryKey_RHS(InAxiom.LHSPrimaryKey_UInt64);

    std::for_each(std::execution::par_unseq,
        Axioms_Vec.begin(),
        Axioms_Vec.end(),
        [&](const Axiom_Struct& Axiom)
        {
            RecursionLimiter::Invoke limiter(6);
            if (limiter.acquired())
            {
                Auto
                [TheoremProto_0000.LHSPrimaryKey_UInt64 == TheoremProto_0000.RHSPrimaryKey_UInt64]
                [TheoremProto_0000.TotalProofsFound_UInt64 >= TheoremProto_0000.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0000, Axiom);

                Auto
                [TheoremProto_0000.LHSPrimaryKey_UInt64 == TheoremProto_0000.RHSPrimaryKey_UInt64]
                [TheoremProto_0000.TotalProofsFound_UInt64 >= TheoremProto_0000.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0000, Axiom);

                Auto
                [TheoremProto_0001.LHSPrimaryKey_UInt64 == TheoremProto_0001.RHSPrimaryKey_UInt64]
                [TheoremProto_0001.TotalProofsFound_UInt64 >= TheoremProto_0001.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0001, Axiom);

                Auto
                [TheoremProto_0001.LHSPrimaryKey_UInt64 == TheoremProto_0001.RHSPrimaryKey_UInt64]
                [TheoremProto_0001.TotalProofsFound_UInt64 >= TheoremProto_0001.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0001, Axiom);

                Auto
                [TheoremProto_0002.LHSPrimaryKey_UInt64 == TheoremProto_0002.RHSPrimaryKey_UInt64]
                [TheoremProto_0002.TotalProofsFound_UInt64 >= TheoremProto_0002.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0002, Axiom);

                Auto
                [TheoremProto_0002.LHSPrimaryKey_UInt64 == TheoremProto_0002.RHSPrimaryKey_UInt64]
                [TheoremProto_0002.TotalProofsFound_UInt64 >= TheoremProto_0002.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0002, Axiom);

                limiter.release();
            }

        });

    std::for_each(std::execution::par_unseq,
        Axioms_Vec.begin(),
        Axioms_Vec.end(),
        [&](const Axiom_Struct& Axiom)
        {
            RecursionLimiter::Invoke limiter(6);
            if (limiter.acquired())
            {
                Auto
                [TheoremProto_0003.LHSPrimaryKey_UInt64 == TheoremProto_0003.RHSPrimaryKey_UInt64]
                [TheoremProto_0003.TotalProofsFound_UInt64 >= TheoremProto_0003.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0003, Axiom);

                Auto
                [TheoremProto_0003.LHSPrimaryKey_UInt64 == TheoremProto_0003.RHSPrimaryKey_UInt64]
                [TheoremProto_0003.TotalProofsFound_UInt64 >= TheoremProto_0003.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0003, Axiom);

                Auto
                [TheoremProto_0004.LHSPrimaryKey_UInt64 == TheoremProto_0004.RHSPrimaryKey_UInt64]
                [TheoremProto_0004.TotalProofsFound_UInt64 >= TheoremProto_0004.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0004, Axiom);

                Auto
                [TheoremProto_0004.LHSPrimaryKey_UInt64 == TheoremProto_0004.RHSPrimaryKey_UInt64]
                [TheoremProto_0004.TotalProofsFound_UInt64 >= TheoremProto_0004.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0004, Axiom);

                Auto
                [TheoremProto_0005.LHSPrimaryKey_UInt64 == TheoremProto_0005.RHSPrimaryKey_UInt64]
                [TheoremProto_0005.TotalProofsFound_UInt64 >= TheoremProto_0005.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0005, Axiom);

                Auto
                [TheoremProto_0005.LHSPrimaryKey_UInt64 == TheoremProto_0005.RHSPrimaryKey_UInt64]
                [TheoremProto_0005.TotalProofsFound_UInt64 >= TheoremProto_0005.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0005, Axiom);

                limiter.release();
            }

        });

    std::for_each(std::execution::par_unseq,
        Axioms_Vec.begin(),
        Axioms_Vec.end(),
        [&](const Axiom_Struct& Axiom)
        {
            RecursionLimiter::Invoke limiter(12);
            if (limiter.acquired())
            {
                Auto
                [TheoremProto_0000.LHSPrimaryKey_UInt64 == TheoremProto_0000.RHSPrimaryKey_UInt64]
                [TheoremProto_0000.TotalProofsFound_UInt64 >= TheoremProto_0000.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0000, Axiom);

                Auto
                [TheoremProto_0000.LHSPrimaryKey_UInt64 == TheoremProto_0000.RHSPrimaryKey_UInt64]
                [TheoremProto_0000.TotalProofsFound_UInt64 >= TheoremProto_0000.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0000, Axiom);

                Auto
                [TheoremProto_0001.LHSPrimaryKey_UInt64 == TheoremProto_0001.RHSPrimaryKey_UInt64]
                [TheoremProto_0001.TotalProofsFound_UInt64 >= TheoremProto_0001.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0001, Axiom);

                Auto
                [TheoremProto_0001.LHSPrimaryKey_UInt64 == TheoremProto_0001.RHSPrimaryKey_UInt64]
                [TheoremProto_0001.TotalProofsFound_UInt64 >= TheoremProto_0001.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0001, Axiom);

                Auto
                [TheoremProto_0002.LHSPrimaryKey_UInt64 == TheoremProto_0002.RHSPrimaryKey_UInt64]
                [TheoremProto_0002.TotalProofsFound_UInt64 >= TheoremProto_0002.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0002, Axiom);

                Auto
                [TheoremProto_0002.LHSPrimaryKey_UInt64 == TheoremProto_0002.RHSPrimaryKey_UInt64]
                [TheoremProto_0002.TotalProofsFound_UInt64 >= TheoremProto_0002.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0002, Axiom);


                Auto
                [TheoremProto_0003.LHSPrimaryKey_UInt64 == TheoremProto_0003.RHSPrimaryKey_UInt64]
                [TheoremProto_0003.TotalProofsFound_UInt64 >= TheoremProto_0003.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0003, Axiom);

                Auto
                [TheoremProto_0003.LHSPrimaryKey_UInt64 == TheoremProto_0003.RHSPrimaryKey_UInt64]
                [TheoremProto_0003.TotalProofsFound_UInt64 >= TheoremProto_0003.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0003, Axiom);

                Auto
                [TheoremProto_0004.LHSPrimaryKey_UInt64 == TheoremProto_0004.RHSPrimaryKey_UInt64]
                [TheoremProto_0004.TotalProofsFound_UInt64 >= TheoremProto_0004.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0004, Axiom);

                Auto
                [TheoremProto_0004.LHSPrimaryKey_UInt64 == TheoremProto_0004.RHSPrimaryKey_UInt64]
                [TheoremProto_0004.TotalProofsFound_UInt64 >= TheoremProto_0004.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0004, Axiom);

                Auto
                [TheoremProto_0005.LHSPrimaryKey_UInt64 == TheoremProto_0005.RHSPrimaryKey_UInt64]
                [TheoremProto_0005.TotalProofsFound_UInt64 >= TheoremProto_0005.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0005, Axiom);

                Auto
                [TheoremProto_0005.LHSPrimaryKey_UInt64 == TheoremProto_0005.RHSPrimaryKey_UInt64]
                [TheoremProto_0005.TotalProofsFound_UInt64 >= TheoremProto_0005.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0005, Axiom);

                limiter.release();
            }

        });

};

Auto
[true]
[false]
[RouteSource_EnumClass::_lhs]
[Indirection_EnumClass::_reduce] =
[](Theorem_Struct InTheorem, const Axiom_Struct& InAxiom) -> void
{
    InTheorem.ProofStack_VecUInt64.push_back(InAxiom);

    if (InTheorem.LHSPrimaryKey_UInt64 == InTheorem.RHSPrimaryKey_UInt64)
    {
        InTheorem.ProofFound_Flag = true;
        ++InTheorem.TotalProofsFound_UInt64;
    }

    if (InTheorem.TotalProofsFound_UInt64 >= InTheorem.MaxAllowedProofs_UInt64)
        return;

    Theorem_Struct TheoremProto_0000 = InTheorem;
    Theorem_Struct TheoremProto_0001 = InTheorem;
    Theorem_Struct TheoremProto_0002 = InTheorem;
    Theorem_Struct TheoremProto_0003 = InTheorem;
    Theorem_Struct TheoremProto_0004 = InTheorem;
    Theorem_Struct TheoremProto_0005 = InTheorem;

    if (TheoremProto_0000.SubnetFound_LHS(InAxiom.LHSPrimaryKey_UInt64))
        TheoremProto_0000.UpdatePrimaryKey_LHS(InAxiom.LHSPrimaryKey_UInt64);

    TheoremProto_0001.UpdatePrimaryKey_RHS(InAxiom.LHSPrimaryKey_UInt64);
    TheoremProto_0002.UpdatePrimaryKey_LHS(InAxiom.LHSPrimaryKey_UInt64);
    TheoremProto_0002.UpdatePrimaryKey_RHS(InAxiom.RHSPrimaryKey_UInt64);

    TheoremProto_0003.UpdatePrimaryKey_LHS(InAxiom.RHSPrimaryKey_UInt64);
    TheoremProto_0004.UpdatePrimaryKey_RHS(InAxiom.RHSPrimaryKey_UInt64);
    TheoremProto_0005.UpdatePrimaryKey_LHS(InAxiom.RHSPrimaryKey_UInt64);
    TheoremProto_0005.UpdatePrimaryKey_RHS(InAxiom.LHSPrimaryKey_UInt64);

    std::for_each(std::execution::par_unseq,
        Axioms_Vec.begin(),
        Axioms_Vec.end(),
        [&](const Axiom_Struct& Axiom)
        {
            RecursionLimiter::Invoke limiter(6);
            if (limiter.acquired())
            {
                Auto
                [TheoremProto_0000.LHSPrimaryKey_UInt64 == TheoremProto_0000.RHSPrimaryKey_UInt64]
                [TheoremProto_0000.TotalProofsFound_UInt64 >= TheoremProto_0000.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0000, Axiom);

                Auto
                [TheoremProto_0000.LHSPrimaryKey_UInt64 == TheoremProto_0000.RHSPrimaryKey_UInt64]
                [TheoremProto_0000.TotalProofsFound_UInt64 >= TheoremProto_0000.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0000, Axiom);

                Auto
                [TheoremProto_0001.LHSPrimaryKey_UInt64 == TheoremProto_0001.RHSPrimaryKey_UInt64]
                [TheoremProto_0001.TotalProofsFound_UInt64 >= TheoremProto_0001.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0001, Axiom);

                Auto
                [TheoremProto_0001.LHSPrimaryKey_UInt64 == TheoremProto_0001.RHSPrimaryKey_UInt64]
                [TheoremProto_0001.TotalProofsFound_UInt64 >= TheoremProto_0001.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0001, Axiom);

                Auto
                [TheoremProto_0002.LHSPrimaryKey_UInt64 == TheoremProto_0002.RHSPrimaryKey_UInt64]
                [TheoremProto_0002.TotalProofsFound_UInt64 >= TheoremProto_0002.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0002, Axiom);

                Auto
                [TheoremProto_0002.LHSPrimaryKey_UInt64 == TheoremProto_0002.RHSPrimaryKey_UInt64]
                [TheoremProto_0002.TotalProofsFound_UInt64 >= TheoremProto_0002.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0002, Axiom);

                limiter.release();
            }

        });

    std::for_each(std::execution::par_unseq,
        Axioms_Vec.begin(),
        Axioms_Vec.end(),
        [&](const Axiom_Struct& Axiom)
        {
            RecursionLimiter::Invoke limiter(6);
            if (limiter.acquired())
            {
                Auto
                [TheoremProto_0003.LHSPrimaryKey_UInt64 == TheoremProto_0003.RHSPrimaryKey_UInt64]
                [TheoremProto_0003.TotalProofsFound_UInt64 >= TheoremProto_0003.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0003, Axiom);

                Auto
                [TheoremProto_0003.LHSPrimaryKey_UInt64 == TheoremProto_0003.RHSPrimaryKey_UInt64]
                [TheoremProto_0003.TotalProofsFound_UInt64 >= TheoremProto_0003.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0003, Axiom);

                Auto
                [TheoremProto_0004.LHSPrimaryKey_UInt64 == TheoremProto_0004.RHSPrimaryKey_UInt64]
                [TheoremProto_0004.TotalProofsFound_UInt64 >= TheoremProto_0004.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0004, Axiom);

                Auto
                [TheoremProto_0004.LHSPrimaryKey_UInt64 == TheoremProto_0004.RHSPrimaryKey_UInt64]
                [TheoremProto_0004.TotalProofsFound_UInt64 >= TheoremProto_0004.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0004, Axiom);

                Auto
                [TheoremProto_0005.LHSPrimaryKey_UInt64 == TheoremProto_0005.RHSPrimaryKey_UInt64]
                [TheoremProto_0005.TotalProofsFound_UInt64 >= TheoremProto_0005.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0005, Axiom);

                Auto
                [TheoremProto_0005.LHSPrimaryKey_UInt64 == TheoremProto_0005.RHSPrimaryKey_UInt64]
                [TheoremProto_0005.TotalProofsFound_UInt64 >= TheoremProto_0005.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0005, Axiom);

                limiter.release();
            }

        });

    std::for_each(std::execution::par_unseq,
        Axioms_Vec.begin(),
        Axioms_Vec.end(),
        [&](const Axiom_Struct& Axiom)
        {
            RecursionLimiter::Invoke limiter(12);
            if (limiter.acquired())
            {
                Auto
                [TheoremProto_0000.LHSPrimaryKey_UInt64 == TheoremProto_0000.RHSPrimaryKey_UInt64]
                [TheoremProto_0000.TotalProofsFound_UInt64 >= TheoremProto_0000.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0000, Axiom);

                Auto
                [TheoremProto_0000.LHSPrimaryKey_UInt64 == TheoremProto_0000.RHSPrimaryKey_UInt64]
                [TheoremProto_0000.TotalProofsFound_UInt64 >= TheoremProto_0000.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0000, Axiom);

                Auto
                [TheoremProto_0001.LHSPrimaryKey_UInt64 == TheoremProto_0001.RHSPrimaryKey_UInt64]
                [TheoremProto_0001.TotalProofsFound_UInt64 >= TheoremProto_0001.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0001, Axiom);

                Auto
                [TheoremProto_0001.LHSPrimaryKey_UInt64 == TheoremProto_0001.RHSPrimaryKey_UInt64]
                [TheoremProto_0001.TotalProofsFound_UInt64 >= TheoremProto_0001.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0001, Axiom);

                Auto
                [TheoremProto_0002.LHSPrimaryKey_UInt64 == TheoremProto_0002.RHSPrimaryKey_UInt64]
                [TheoremProto_0002.TotalProofsFound_UInt64 >= TheoremProto_0002.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0002, Axiom);

                Auto
                [TheoremProto_0002.LHSPrimaryKey_UInt64 == TheoremProto_0002.RHSPrimaryKey_UInt64]
                [TheoremProto_0002.TotalProofsFound_UInt64 >= TheoremProto_0002.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0002, Axiom);


                Auto
                [TheoremProto_0003.LHSPrimaryKey_UInt64 == TheoremProto_0003.RHSPrimaryKey_UInt64]
                [TheoremProto_0003.TotalProofsFound_UInt64 >= TheoremProto_0003.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0003, Axiom);

                Auto
                [TheoremProto_0003.LHSPrimaryKey_UInt64 == TheoremProto_0003.RHSPrimaryKey_UInt64]
                [TheoremProto_0003.TotalProofsFound_UInt64 >= TheoremProto_0003.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0003, Axiom);

                Auto
                [TheoremProto_0004.LHSPrimaryKey_UInt64 == TheoremProto_0004.RHSPrimaryKey_UInt64]
                [TheoremProto_0004.TotalProofsFound_UInt64 >= TheoremProto_0004.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0004, Axiom);

                Auto
                [TheoremProto_0004.LHSPrimaryKey_UInt64 == TheoremProto_0004.RHSPrimaryKey_UInt64]
                [TheoremProto_0004.TotalProofsFound_UInt64 >= TheoremProto_0004.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0004, Axiom);

                Auto
                [TheoremProto_0005.LHSPrimaryKey_UInt64 == TheoremProto_0005.RHSPrimaryKey_UInt64]
                [TheoremProto_0005.TotalProofsFound_UInt64 >= TheoremProto_0005.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0005, Axiom);

                Auto
                [TheoremProto_0005.LHSPrimaryKey_UInt64 == TheoremProto_0005.RHSPrimaryKey_UInt64]
                [TheoremProto_0005.TotalProofsFound_UInt64 >= TheoremProto_0005.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0005, Axiom);

                limiter.release();
            }

        });

};

Auto
[true]
[false]
[RouteSource_EnumClass::_lhs]
[Indirection_EnumClass::_expand] =
[](Theorem_Struct InTheorem, const Axiom_Struct& InAxiom) -> void
{
    InTheorem.ProofStack_VecUInt64.push_back(InAxiom);

    if (InTheorem.LHSPrimaryKey_UInt64 == InTheorem.RHSPrimaryKey_UInt64)
    {
        InTheorem.ProofFound_Flag = true;
        ++InTheorem.TotalProofsFound_UInt64;
    }

    if (InTheorem.TotalProofsFound_UInt64 >= InTheorem.MaxAllowedProofs_UInt64)
        return;

    Theorem_Struct TheoremProto_0000 = InTheorem;
    Theorem_Struct TheoremProto_0001 = InTheorem;
    Theorem_Struct TheoremProto_0002 = InTheorem;
    Theorem_Struct TheoremProto_0003 = InTheorem;
    Theorem_Struct TheoremProto_0004 = InTheorem;
    Theorem_Struct TheoremProto_0005 = InTheorem;

    if (TheoremProto_0000.SubnetFound_LHS(InAxiom.LHSPrimaryKey_UInt64))
        TheoremProto_0000.UpdatePrimaryKey_LHS(InAxiom.LHSPrimaryKey_UInt64);

    TheoremProto_0001.UpdatePrimaryKey_RHS(InAxiom.LHSPrimaryKey_UInt64);
    TheoremProto_0002.UpdatePrimaryKey_LHS(InAxiom.LHSPrimaryKey_UInt64);
    TheoremProto_0002.UpdatePrimaryKey_RHS(InAxiom.RHSPrimaryKey_UInt64);

    TheoremProto_0003.UpdatePrimaryKey_LHS(InAxiom.RHSPrimaryKey_UInt64);
    TheoremProto_0004.UpdatePrimaryKey_RHS(InAxiom.RHSPrimaryKey_UInt64);
    TheoremProto_0005.UpdatePrimaryKey_LHS(InAxiom.RHSPrimaryKey_UInt64);
    TheoremProto_0005.UpdatePrimaryKey_RHS(InAxiom.LHSPrimaryKey_UInt64);

    std::for_each(std::execution::par_unseq,
        Axioms_Vec.begin(),
        Axioms_Vec.end(),
        [&](const Axiom_Struct& Axiom)
        {
            RecursionLimiter::Invoke limiter(6);
            if (limiter.acquired())
            {
                Auto
                [TheoremProto_0000.LHSPrimaryKey_UInt64 == TheoremProto_0000.RHSPrimaryKey_UInt64]
                [TheoremProto_0000.TotalProofsFound_UInt64 >= TheoremProto_0000.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0000, Axiom);

                Auto
                [TheoremProto_0000.LHSPrimaryKey_UInt64 == TheoremProto_0000.RHSPrimaryKey_UInt64]
                [TheoremProto_0000.TotalProofsFound_UInt64 >= TheoremProto_0000.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0000, Axiom);

                Auto
                [TheoremProto_0001.LHSPrimaryKey_UInt64 == TheoremProto_0001.RHSPrimaryKey_UInt64]
                [TheoremProto_0001.TotalProofsFound_UInt64 >= TheoremProto_0001.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0001, Axiom);

                Auto
                [TheoremProto_0001.LHSPrimaryKey_UInt64 == TheoremProto_0001.RHSPrimaryKey_UInt64]
                [TheoremProto_0001.TotalProofsFound_UInt64 >= TheoremProto_0001.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0001, Axiom);

                Auto
                [TheoremProto_0002.LHSPrimaryKey_UInt64 == TheoremProto_0002.RHSPrimaryKey_UInt64]
                [TheoremProto_0002.TotalProofsFound_UInt64 >= TheoremProto_0002.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0002, Axiom);

                Auto
                [TheoremProto_0002.LHSPrimaryKey_UInt64 == TheoremProto_0002.RHSPrimaryKey_UInt64]
                [TheoremProto_0002.TotalProofsFound_UInt64 >= TheoremProto_0002.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0002, Axiom);

                limiter.release();
            }

        });

    std::for_each(std::execution::par_unseq,
        Axioms_Vec.begin(),
        Axioms_Vec.end(),
        [&](const Axiom_Struct& Axiom)
        {
            RecursionLimiter::Invoke limiter(6);
            if (limiter.acquired())
            {
                Auto
                [TheoremProto_0003.LHSPrimaryKey_UInt64 == TheoremProto_0003.RHSPrimaryKey_UInt64]
                [TheoremProto_0003.TotalProofsFound_UInt64 >= TheoremProto_0003.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0003, Axiom);

                Auto
                [TheoremProto_0003.LHSPrimaryKey_UInt64 == TheoremProto_0003.RHSPrimaryKey_UInt64]
                [TheoremProto_0003.TotalProofsFound_UInt64 >= TheoremProto_0003.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0003, Axiom);

                Auto
                [TheoremProto_0004.LHSPrimaryKey_UInt64 == TheoremProto_0004.RHSPrimaryKey_UInt64]
                [TheoremProto_0004.TotalProofsFound_UInt64 >= TheoremProto_0004.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0004, Axiom);

                Auto
                [TheoremProto_0004.LHSPrimaryKey_UInt64 == TheoremProto_0004.RHSPrimaryKey_UInt64]
                [TheoremProto_0004.TotalProofsFound_UInt64 >= TheoremProto_0004.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0004, Axiom);

                Auto
                [TheoremProto_0005.LHSPrimaryKey_UInt64 == TheoremProto_0005.RHSPrimaryKey_UInt64]
                [TheoremProto_0005.TotalProofsFound_UInt64 >= TheoremProto_0005.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0005, Axiom);

                Auto
                [TheoremProto_0005.LHSPrimaryKey_UInt64 == TheoremProto_0005.RHSPrimaryKey_UInt64]
                [TheoremProto_0005.TotalProofsFound_UInt64 >= TheoremProto_0005.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0005, Axiom);

                limiter.release();
            }

        });

    std::for_each(std::execution::par_unseq,
        Axioms_Vec.begin(),
        Axioms_Vec.end(),
        [&](const Axiom_Struct& Axiom)
        {
            RecursionLimiter::Invoke limiter(12);
            if (limiter.acquired())
            {
                Auto
                [TheoremProto_0000.LHSPrimaryKey_UInt64 == TheoremProto_0000.RHSPrimaryKey_UInt64]
                [TheoremProto_0000.TotalProofsFound_UInt64 >= TheoremProto_0000.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0000, Axiom);

                Auto
                [TheoremProto_0000.LHSPrimaryKey_UInt64 == TheoremProto_0000.RHSPrimaryKey_UInt64]
                [TheoremProto_0000.TotalProofsFound_UInt64 >= TheoremProto_0000.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0000, Axiom);

                Auto
                [TheoremProto_0001.LHSPrimaryKey_UInt64 == TheoremProto_0001.RHSPrimaryKey_UInt64]
                [TheoremProto_0001.TotalProofsFound_UInt64 >= TheoremProto_0001.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0001, Axiom);

                Auto
                [TheoremProto_0001.LHSPrimaryKey_UInt64 == TheoremProto_0001.RHSPrimaryKey_UInt64]
                [TheoremProto_0001.TotalProofsFound_UInt64 >= TheoremProto_0001.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0001, Axiom);

                Auto
                [TheoremProto_0002.LHSPrimaryKey_UInt64 == TheoremProto_0002.RHSPrimaryKey_UInt64]
                [TheoremProto_0002.TotalProofsFound_UInt64 >= TheoremProto_0002.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0002, Axiom);

                Auto
                [TheoremProto_0002.LHSPrimaryKey_UInt64 == TheoremProto_0002.RHSPrimaryKey_UInt64]
                [TheoremProto_0002.TotalProofsFound_UInt64 >= TheoremProto_0002.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0002, Axiom);


                Auto
                [TheoremProto_0003.LHSPrimaryKey_UInt64 == TheoremProto_0003.RHSPrimaryKey_UInt64]
                [TheoremProto_0003.TotalProofsFound_UInt64 >= TheoremProto_0003.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0003, Axiom);

                Auto
                [TheoremProto_0003.LHSPrimaryKey_UInt64 == TheoremProto_0003.RHSPrimaryKey_UInt64]
                [TheoremProto_0003.TotalProofsFound_UInt64 >= TheoremProto_0003.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0003, Axiom);

                Auto
                [TheoremProto_0004.LHSPrimaryKey_UInt64 == TheoremProto_0004.RHSPrimaryKey_UInt64]
                [TheoremProto_0004.TotalProofsFound_UInt64 >= TheoremProto_0004.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0004, Axiom);

                Auto
                [TheoremProto_0004.LHSPrimaryKey_UInt64 == TheoremProto_0004.RHSPrimaryKey_UInt64]
                [TheoremProto_0004.TotalProofsFound_UInt64 >= TheoremProto_0004.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0004, Axiom);

                Auto
                [TheoremProto_0005.LHSPrimaryKey_UInt64 == TheoremProto_0005.RHSPrimaryKey_UInt64]
                [TheoremProto_0005.TotalProofsFound_UInt64 >= TheoremProto_0005.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0005, Axiom);

                Auto
                [TheoremProto_0005.LHSPrimaryKey_UInt64 == TheoremProto_0005.RHSPrimaryKey_UInt64]
                [TheoremProto_0005.TotalProofsFound_UInt64 >= TheoremProto_0005.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0005, Axiom);

                limiter.release();
            }

        });

};

Auto
[true]
[false]
[RouteSource_EnumClass::_rhs]
[Indirection_EnumClass::_auto] =
[](Theorem_Struct InTheorem, const Axiom_Struct& InAxiom) -> void
{
    InTheorem.ProofStack_VecUInt64.push_back(InAxiom);

    if (InTheorem.LHSPrimaryKey_UInt64 == InTheorem.RHSPrimaryKey_UInt64)
    {
        InTheorem.ProofFound_Flag = true;
        ++InTheorem.TotalProofsFound_UInt64;
    }

    if (InTheorem.TotalProofsFound_UInt64 >= InTheorem.MaxAllowedProofs_UInt64)
        return;

    Theorem_Struct TheoremProto_0000 = InTheorem;
    Theorem_Struct TheoremProto_0001 = InTheorem;
    Theorem_Struct TheoremProto_0002 = InTheorem;
    Theorem_Struct TheoremProto_0003 = InTheorem;
    Theorem_Struct TheoremProto_0004 = InTheorem;
    Theorem_Struct TheoremProto_0005 = InTheorem;

    if (TheoremProto_0000.SubnetFound_LHS(InAxiom.LHSPrimaryKey_UInt64))
        TheoremProto_0000.UpdatePrimaryKey_LHS(InAxiom.LHSPrimaryKey_UInt64);

    TheoremProto_0001.UpdatePrimaryKey_RHS(InAxiom.LHSPrimaryKey_UInt64);
    TheoremProto_0002.UpdatePrimaryKey_LHS(InAxiom.LHSPrimaryKey_UInt64);
    TheoremProto_0002.UpdatePrimaryKey_RHS(InAxiom.RHSPrimaryKey_UInt64);

    TheoremProto_0003.UpdatePrimaryKey_LHS(InAxiom.RHSPrimaryKey_UInt64);
    TheoremProto_0004.UpdatePrimaryKey_RHS(InAxiom.RHSPrimaryKey_UInt64);
    TheoremProto_0005.UpdatePrimaryKey_LHS(InAxiom.RHSPrimaryKey_UInt64);
    TheoremProto_0005.UpdatePrimaryKey_RHS(InAxiom.LHSPrimaryKey_UInt64);

    std::for_each(std::execution::par_unseq,
        Axioms_Vec.begin(),
        Axioms_Vec.end(),
        [&](const Axiom_Struct& Axiom)
        {
            RecursionLimiter::Invoke limiter(6);
            if (limiter.acquired())
            {
                Auto
                [TheoremProto_0000.LHSPrimaryKey_UInt64 == TheoremProto_0000.RHSPrimaryKey_UInt64]
                [TheoremProto_0000.TotalProofsFound_UInt64 >= TheoremProto_0000.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0000, Axiom);

                Auto
                [TheoremProto_0000.LHSPrimaryKey_UInt64 == TheoremProto_0000.RHSPrimaryKey_UInt64]
                [TheoremProto_0000.TotalProofsFound_UInt64 >= TheoremProto_0000.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0000, Axiom);

                Auto
                [TheoremProto_0001.LHSPrimaryKey_UInt64 == TheoremProto_0001.RHSPrimaryKey_UInt64]
                [TheoremProto_0001.TotalProofsFound_UInt64 >= TheoremProto_0001.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0001, Axiom);

                Auto
                [TheoremProto_0001.LHSPrimaryKey_UInt64 == TheoremProto_0001.RHSPrimaryKey_UInt64]
                [TheoremProto_0001.TotalProofsFound_UInt64 >= TheoremProto_0001.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0001, Axiom);

                Auto
                [TheoremProto_0002.LHSPrimaryKey_UInt64 == TheoremProto_0002.RHSPrimaryKey_UInt64]
                [TheoremProto_0002.TotalProofsFound_UInt64 >= TheoremProto_0002.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0002, Axiom);

                Auto
                [TheoremProto_0002.LHSPrimaryKey_UInt64 == TheoremProto_0002.RHSPrimaryKey_UInt64]
                [TheoremProto_0002.TotalProofsFound_UInt64 >= TheoremProto_0002.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0002, Axiom);

                limiter.release();
            }

        });

    std::for_each(std::execution::par_unseq,
        Axioms_Vec.begin(),
        Axioms_Vec.end(),
        [&](const Axiom_Struct& Axiom)
        {
            RecursionLimiter::Invoke limiter(6);
            if (limiter.acquired())
            {
                Auto
                [TheoremProto_0003.LHSPrimaryKey_UInt64 == TheoremProto_0003.RHSPrimaryKey_UInt64]
                [TheoremProto_0003.TotalProofsFound_UInt64 >= TheoremProto_0003.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0003, Axiom);

                Auto
                [TheoremProto_0003.LHSPrimaryKey_UInt64 == TheoremProto_0003.RHSPrimaryKey_UInt64]
                [TheoremProto_0003.TotalProofsFound_UInt64 >= TheoremProto_0003.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0003, Axiom);

                Auto
                [TheoremProto_0004.LHSPrimaryKey_UInt64 == TheoremProto_0004.RHSPrimaryKey_UInt64]
                [TheoremProto_0004.TotalProofsFound_UInt64 >= TheoremProto_0004.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0004, Axiom);

                Auto
                [TheoremProto_0004.LHSPrimaryKey_UInt64 == TheoremProto_0004.RHSPrimaryKey_UInt64]
                [TheoremProto_0004.TotalProofsFound_UInt64 >= TheoremProto_0004.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0004, Axiom);

                Auto
                [TheoremProto_0005.LHSPrimaryKey_UInt64 == TheoremProto_0005.RHSPrimaryKey_UInt64]
                [TheoremProto_0005.TotalProofsFound_UInt64 >= TheoremProto_0005.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0005, Axiom);

                Auto
                [TheoremProto_0005.LHSPrimaryKey_UInt64 == TheoremProto_0005.RHSPrimaryKey_UInt64]
                [TheoremProto_0005.TotalProofsFound_UInt64 >= TheoremProto_0005.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0005, Axiom);

                limiter.release();
            }

        });

    std::for_each(std::execution::par_unseq,
        Axioms_Vec.begin(),
        Axioms_Vec.end(),
        [&](const Axiom_Struct& Axiom)
        {
            RecursionLimiter::Invoke limiter(12);
            if (limiter.acquired())
            {
                Auto
                [TheoremProto_0000.LHSPrimaryKey_UInt64 == TheoremProto_0000.RHSPrimaryKey_UInt64]
                [TheoremProto_0000.TotalProofsFound_UInt64 >= TheoremProto_0000.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0000, Axiom);

                Auto
                [TheoremProto_0000.LHSPrimaryKey_UInt64 == TheoremProto_0000.RHSPrimaryKey_UInt64]
                [TheoremProto_0000.TotalProofsFound_UInt64 >= TheoremProto_0000.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0000, Axiom);

                Auto
                [TheoremProto_0001.LHSPrimaryKey_UInt64 == TheoremProto_0001.RHSPrimaryKey_UInt64]
                [TheoremProto_0001.TotalProofsFound_UInt64 >= TheoremProto_0001.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0001, Axiom);

                Auto
                [TheoremProto_0001.LHSPrimaryKey_UInt64 == TheoremProto_0001.RHSPrimaryKey_UInt64]
                [TheoremProto_0001.TotalProofsFound_UInt64 >= TheoremProto_0001.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0001, Axiom);

                Auto
                [TheoremProto_0002.LHSPrimaryKey_UInt64 == TheoremProto_0002.RHSPrimaryKey_UInt64]
                [TheoremProto_0002.TotalProofsFound_UInt64 >= TheoremProto_0002.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0002, Axiom);

                Auto
                [TheoremProto_0002.LHSPrimaryKey_UInt64 == TheoremProto_0002.RHSPrimaryKey_UInt64]
                [TheoremProto_0002.TotalProofsFound_UInt64 >= TheoremProto_0002.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0002, Axiom);


                Auto
                [TheoremProto_0003.LHSPrimaryKey_UInt64 == TheoremProto_0003.RHSPrimaryKey_UInt64]
                [TheoremProto_0003.TotalProofsFound_UInt64 >= TheoremProto_0003.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0003, Axiom);

                Auto
                [TheoremProto_0003.LHSPrimaryKey_UInt64 == TheoremProto_0003.RHSPrimaryKey_UInt64]
                [TheoremProto_0003.TotalProofsFound_UInt64 >= TheoremProto_0003.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0003, Axiom);

                Auto
                [TheoremProto_0004.LHSPrimaryKey_UInt64 == TheoremProto_0004.RHSPrimaryKey_UInt64]
                [TheoremProto_0004.TotalProofsFound_UInt64 >= TheoremProto_0004.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0004, Axiom);

                Auto
                [TheoremProto_0004.LHSPrimaryKey_UInt64 == TheoremProto_0004.RHSPrimaryKey_UInt64]
                [TheoremProto_0004.TotalProofsFound_UInt64 >= TheoremProto_0004.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0004, Axiom);

                Auto
                [TheoremProto_0005.LHSPrimaryKey_UInt64 == TheoremProto_0005.RHSPrimaryKey_UInt64]
                [TheoremProto_0005.TotalProofsFound_UInt64 >= TheoremProto_0005.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0005, Axiom);

                Auto
                [TheoremProto_0005.LHSPrimaryKey_UInt64 == TheoremProto_0005.RHSPrimaryKey_UInt64]
                [TheoremProto_0005.TotalProofsFound_UInt64 >= TheoremProto_0005.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0005, Axiom);

                limiter.release();
            }

        });

};

Auto
[true]
[false]
[RouteSource_EnumClass::_rhs]
[Indirection_EnumClass::_reduce] =
[](Theorem_Struct InTheorem, const Axiom_Struct& InAxiom) -> void
{
    InTheorem.ProofStack_VecUInt64.push_back(InAxiom);

    if (InTheorem.LHSPrimaryKey_UInt64 == InTheorem.RHSPrimaryKey_UInt64)
    {
        InTheorem.ProofFound_Flag = true;
        ++InTheorem.TotalProofsFound_UInt64;
    }

    if (InTheorem.TotalProofsFound_UInt64 >= InTheorem.MaxAllowedProofs_UInt64)
        return;

    Theorem_Struct TheoremProto_0000 = InTheorem;
    Theorem_Struct TheoremProto_0001 = InTheorem;
    Theorem_Struct TheoremProto_0002 = InTheorem;
    Theorem_Struct TheoremProto_0003 = InTheorem;
    Theorem_Struct TheoremProto_0004 = InTheorem;
    Theorem_Struct TheoremProto_0005 = InTheorem;

    if (TheoremProto_0000.SubnetFound_LHS(InAxiom.LHSPrimaryKey_UInt64))
        TheoremProto_0000.UpdatePrimaryKey_LHS(InAxiom.LHSPrimaryKey_UInt64);

    TheoremProto_0001.UpdatePrimaryKey_RHS(InAxiom.LHSPrimaryKey_UInt64);
    TheoremProto_0002.UpdatePrimaryKey_LHS(InAxiom.LHSPrimaryKey_UInt64);
    TheoremProto_0002.UpdatePrimaryKey_RHS(InAxiom.RHSPrimaryKey_UInt64);

    TheoremProto_0003.UpdatePrimaryKey_LHS(InAxiom.RHSPrimaryKey_UInt64);
    TheoremProto_0004.UpdatePrimaryKey_RHS(InAxiom.RHSPrimaryKey_UInt64);
    TheoremProto_0005.UpdatePrimaryKey_LHS(InAxiom.RHSPrimaryKey_UInt64);
    TheoremProto_0005.UpdatePrimaryKey_RHS(InAxiom.LHSPrimaryKey_UInt64);

    std::for_each(std::execution::par_unseq,
        Axioms_Vec.begin(),
        Axioms_Vec.end(),
        [&](const Axiom_Struct& Axiom)
        {
            RecursionLimiter::Invoke limiter(6);
            if (limiter.acquired())
            {
                Auto
                [TheoremProto_0000.LHSPrimaryKey_UInt64 == TheoremProto_0000.RHSPrimaryKey_UInt64]
                [TheoremProto_0000.TotalProofsFound_UInt64 >= TheoremProto_0000.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0000, Axiom);

                Auto
                [TheoremProto_0000.LHSPrimaryKey_UInt64 == TheoremProto_0000.RHSPrimaryKey_UInt64]
                [TheoremProto_0000.TotalProofsFound_UInt64 >= TheoremProto_0000.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0000, Axiom);

                Auto
                [TheoremProto_0001.LHSPrimaryKey_UInt64 == TheoremProto_0001.RHSPrimaryKey_UInt64]
                [TheoremProto_0001.TotalProofsFound_UInt64 >= TheoremProto_0001.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0001, Axiom);

                Auto
                [TheoremProto_0001.LHSPrimaryKey_UInt64 == TheoremProto_0001.RHSPrimaryKey_UInt64]
                [TheoremProto_0001.TotalProofsFound_UInt64 >= TheoremProto_0001.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0001, Axiom);

                Auto
                [TheoremProto_0002.LHSPrimaryKey_UInt64 == TheoremProto_0002.RHSPrimaryKey_UInt64]
                [TheoremProto_0002.TotalProofsFound_UInt64 >= TheoremProto_0002.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0002, Axiom);

                Auto
                [TheoremProto_0002.LHSPrimaryKey_UInt64 == TheoremProto_0002.RHSPrimaryKey_UInt64]
                [TheoremProto_0002.TotalProofsFound_UInt64 >= TheoremProto_0002.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0002, Axiom);

                limiter.release();
            }

        });

    std::for_each(std::execution::par_unseq,
        Axioms_Vec.begin(),
        Axioms_Vec.end(),
        [&](const Axiom_Struct& Axiom)
        {
            RecursionLimiter::Invoke limiter(6);
            if (limiter.acquired())
            {
                Auto
                [TheoremProto_0003.LHSPrimaryKey_UInt64 == TheoremProto_0003.RHSPrimaryKey_UInt64]
                [TheoremProto_0003.TotalProofsFound_UInt64 >= TheoremProto_0003.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0003, Axiom);

                Auto
                [TheoremProto_0003.LHSPrimaryKey_UInt64 == TheoremProto_0003.RHSPrimaryKey_UInt64]
                [TheoremProto_0003.TotalProofsFound_UInt64 >= TheoremProto_0003.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0003, Axiom);

                Auto
                [TheoremProto_0004.LHSPrimaryKey_UInt64 == TheoremProto_0004.RHSPrimaryKey_UInt64]
                [TheoremProto_0004.TotalProofsFound_UInt64 >= TheoremProto_0004.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0004, Axiom);

                Auto
                [TheoremProto_0004.LHSPrimaryKey_UInt64 == TheoremProto_0004.RHSPrimaryKey_UInt64]
                [TheoremProto_0004.TotalProofsFound_UInt64 >= TheoremProto_0004.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0004, Axiom);

                Auto
                [TheoremProto_0005.LHSPrimaryKey_UInt64 == TheoremProto_0005.RHSPrimaryKey_UInt64]
                [TheoremProto_0005.TotalProofsFound_UInt64 >= TheoremProto_0005.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0005, Axiom);

                Auto
                [TheoremProto_0005.LHSPrimaryKey_UInt64 == TheoremProto_0005.RHSPrimaryKey_UInt64]
                [TheoremProto_0005.TotalProofsFound_UInt64 >= TheoremProto_0005.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0005, Axiom);

                limiter.release();
            }

        });

    std::for_each(std::execution::par_unseq,
        Axioms_Vec.begin(),
        Axioms_Vec.end(),
        [&](const Axiom_Struct& Axiom)
        {
            RecursionLimiter::Invoke limiter(12);
            if (limiter.acquired())
            {
                Auto
                [TheoremProto_0000.LHSPrimaryKey_UInt64 == TheoremProto_0000.RHSPrimaryKey_UInt64]
                [TheoremProto_0000.TotalProofsFound_UInt64 >= TheoremProto_0000.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0000, Axiom);

                Auto
                [TheoremProto_0000.LHSPrimaryKey_UInt64 == TheoremProto_0000.RHSPrimaryKey_UInt64]
                [TheoremProto_0000.TotalProofsFound_UInt64 >= TheoremProto_0000.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0000, Axiom);

                Auto
                [TheoremProto_0001.LHSPrimaryKey_UInt64 == TheoremProto_0001.RHSPrimaryKey_UInt64]
                [TheoremProto_0001.TotalProofsFound_UInt64 >= TheoremProto_0001.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0001, Axiom);

                Auto
                [TheoremProto_0001.LHSPrimaryKey_UInt64 == TheoremProto_0001.RHSPrimaryKey_UInt64]
                [TheoremProto_0001.TotalProofsFound_UInt64 >= TheoremProto_0001.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0001, Axiom);

                Auto
                [TheoremProto_0002.LHSPrimaryKey_UInt64 == TheoremProto_0002.RHSPrimaryKey_UInt64]
                [TheoremProto_0002.TotalProofsFound_UInt64 >= TheoremProto_0002.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0002, Axiom);

                Auto
                [TheoremProto_0002.LHSPrimaryKey_UInt64 == TheoremProto_0002.RHSPrimaryKey_UInt64]
                [TheoremProto_0002.TotalProofsFound_UInt64 >= TheoremProto_0002.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0002, Axiom);


                Auto
                [TheoremProto_0003.LHSPrimaryKey_UInt64 == TheoremProto_0003.RHSPrimaryKey_UInt64]
                [TheoremProto_0003.TotalProofsFound_UInt64 >= TheoremProto_0003.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0003, Axiom);

                Auto
                [TheoremProto_0003.LHSPrimaryKey_UInt64 == TheoremProto_0003.RHSPrimaryKey_UInt64]
                [TheoremProto_0003.TotalProofsFound_UInt64 >= TheoremProto_0003.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0003, Axiom);

                Auto
                [TheoremProto_0004.LHSPrimaryKey_UInt64 == TheoremProto_0004.RHSPrimaryKey_UInt64]
                [TheoremProto_0004.TotalProofsFound_UInt64 >= TheoremProto_0004.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0004, Axiom);

                Auto
                [TheoremProto_0004.LHSPrimaryKey_UInt64 == TheoremProto_0004.RHSPrimaryKey_UInt64]
                [TheoremProto_0004.TotalProofsFound_UInt64 >= TheoremProto_0004.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0004, Axiom);

                Auto
                [TheoremProto_0005.LHSPrimaryKey_UInt64 == TheoremProto_0005.RHSPrimaryKey_UInt64]
                [TheoremProto_0005.TotalProofsFound_UInt64 >= TheoremProto_0005.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0005, Axiom);

                Auto
                [TheoremProto_0005.LHSPrimaryKey_UInt64 == TheoremProto_0005.RHSPrimaryKey_UInt64]
                [TheoremProto_0005.TotalProofsFound_UInt64 >= TheoremProto_0005.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0005, Axiom);

                limiter.release();
            }

        });

};

Auto
[true]
[false]
[RouteSource_EnumClass::_rhs]
[Indirection_EnumClass::_expand] =
[](Theorem_Struct InTheorem, const Axiom_Struct& InAxiom) -> void
{
    InTheorem.ProofStack_VecUInt64.push_back(InAxiom);

    if (InTheorem.LHSPrimaryKey_UInt64 == InTheorem.RHSPrimaryKey_UInt64)
    {
        InTheorem.ProofFound_Flag = true;
        ++InTheorem.TotalProofsFound_UInt64;
    }

    if (InTheorem.TotalProofsFound_UInt64 >= InTheorem.MaxAllowedProofs_UInt64)
        return;

    Theorem_Struct TheoremProto_0000 = InTheorem;
    Theorem_Struct TheoremProto_0001 = InTheorem;
    Theorem_Struct TheoremProto_0002 = InTheorem;
    Theorem_Struct TheoremProto_0003 = InTheorem;
    Theorem_Struct TheoremProto_0004 = InTheorem;
    Theorem_Struct TheoremProto_0005 = InTheorem;

    if (TheoremProto_0000.SubnetFound_LHS(InAxiom.LHSPrimaryKey_UInt64))
        TheoremProto_0000.UpdatePrimaryKey_LHS(InAxiom.LHSPrimaryKey_UInt64);

    TheoremProto_0001.UpdatePrimaryKey_RHS(InAxiom.LHSPrimaryKey_UInt64);
    TheoremProto_0002.UpdatePrimaryKey_LHS(InAxiom.LHSPrimaryKey_UInt64);
    TheoremProto_0002.UpdatePrimaryKey_RHS(InAxiom.RHSPrimaryKey_UInt64);

    TheoremProto_0003.UpdatePrimaryKey_LHS(InAxiom.RHSPrimaryKey_UInt64);
    TheoremProto_0004.UpdatePrimaryKey_RHS(InAxiom.RHSPrimaryKey_UInt64);
    TheoremProto_0005.UpdatePrimaryKey_LHS(InAxiom.RHSPrimaryKey_UInt64);
    TheoremProto_0005.UpdatePrimaryKey_RHS(InAxiom.LHSPrimaryKey_UInt64);

    std::for_each(std::execution::par_unseq,
        Axioms_Vec.begin(),
        Axioms_Vec.end(),
        [&](const Axiom_Struct& Axiom)
        {
            RecursionLimiter::Invoke limiter(6);
            if (limiter.acquired())
            {
                Auto
                [TheoremProto_0000.LHSPrimaryKey_UInt64 == TheoremProto_0000.RHSPrimaryKey_UInt64]
                [TheoremProto_0000.TotalProofsFound_UInt64 >= TheoremProto_0000.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0000, Axiom);

                Auto
                [TheoremProto_0000.LHSPrimaryKey_UInt64 == TheoremProto_0000.RHSPrimaryKey_UInt64]
                [TheoremProto_0000.TotalProofsFound_UInt64 >= TheoremProto_0000.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0000, Axiom);

                Auto
                [TheoremProto_0001.LHSPrimaryKey_UInt64 == TheoremProto_0001.RHSPrimaryKey_UInt64]
                [TheoremProto_0001.TotalProofsFound_UInt64 >= TheoremProto_0001.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0001, Axiom);

                Auto
                [TheoremProto_0001.LHSPrimaryKey_UInt64 == TheoremProto_0001.RHSPrimaryKey_UInt64]
                [TheoremProto_0001.TotalProofsFound_UInt64 >= TheoremProto_0001.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0001, Axiom);

                Auto
                [TheoremProto_0002.LHSPrimaryKey_UInt64 == TheoremProto_0002.RHSPrimaryKey_UInt64]
                [TheoremProto_0002.TotalProofsFound_UInt64 >= TheoremProto_0002.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0002, Axiom);

                Auto
                [TheoremProto_0002.LHSPrimaryKey_UInt64 == TheoremProto_0002.RHSPrimaryKey_UInt64]
                [TheoremProto_0002.TotalProofsFound_UInt64 >= TheoremProto_0002.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0002, Axiom);

                limiter.release();
            }

        });

    std::for_each(std::execution::par_unseq,
        Axioms_Vec.begin(),
        Axioms_Vec.end(),
        [&](const Axiom_Struct& Axiom)
        {
            RecursionLimiter::Invoke limiter(6);
            if (limiter.acquired())
            {
                Auto
                [TheoremProto_0003.LHSPrimaryKey_UInt64 == TheoremProto_0003.RHSPrimaryKey_UInt64]
                [TheoremProto_0003.TotalProofsFound_UInt64 >= TheoremProto_0003.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0003, Axiom);

                Auto
                [TheoremProto_0003.LHSPrimaryKey_UInt64 == TheoremProto_0003.RHSPrimaryKey_UInt64]
                [TheoremProto_0003.TotalProofsFound_UInt64 >= TheoremProto_0003.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0003, Axiom);

                Auto
                [TheoremProto_0004.LHSPrimaryKey_UInt64 == TheoremProto_0004.RHSPrimaryKey_UInt64]
                [TheoremProto_0004.TotalProofsFound_UInt64 >= TheoremProto_0004.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0004, Axiom);

                Auto
                [TheoremProto_0004.LHSPrimaryKey_UInt64 == TheoremProto_0004.RHSPrimaryKey_UInt64]
                [TheoremProto_0004.TotalProofsFound_UInt64 >= TheoremProto_0004.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0004, Axiom);

                Auto
                [TheoremProto_0005.LHSPrimaryKey_UInt64 == TheoremProto_0005.RHSPrimaryKey_UInt64]
                [TheoremProto_0005.TotalProofsFound_UInt64 >= TheoremProto_0005.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0005, Axiom);

                Auto
                [TheoremProto_0005.LHSPrimaryKey_UInt64 == TheoremProto_0005.RHSPrimaryKey_UInt64]
                [TheoremProto_0005.TotalProofsFound_UInt64 >= TheoremProto_0005.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0005, Axiom);

                limiter.release();
            }

        });

    std::for_each(std::execution::par_unseq,
        Axioms_Vec.begin(),
        Axioms_Vec.end(),
        [&](const Axiom_Struct& Axiom)
        {
            RecursionLimiter::Invoke limiter(12);
            if (limiter.acquired())
            {
                Auto
                [TheoremProto_0000.LHSPrimaryKey_UInt64 == TheoremProto_0000.RHSPrimaryKey_UInt64]
                [TheoremProto_0000.TotalProofsFound_UInt64 >= TheoremProto_0000.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0000, Axiom);

                Auto
                [TheoremProto_0000.LHSPrimaryKey_UInt64 == TheoremProto_0000.RHSPrimaryKey_UInt64]
                [TheoremProto_0000.TotalProofsFound_UInt64 >= TheoremProto_0000.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0000, Axiom);

                Auto
                [TheoremProto_0001.LHSPrimaryKey_UInt64 == TheoremProto_0001.RHSPrimaryKey_UInt64]
                [TheoremProto_0001.TotalProofsFound_UInt64 >= TheoremProto_0001.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0001, Axiom);

                Auto
                [TheoremProto_0001.LHSPrimaryKey_UInt64 == TheoremProto_0001.RHSPrimaryKey_UInt64]
                [TheoremProto_0001.TotalProofsFound_UInt64 >= TheoremProto_0001.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0001, Axiom);

                Auto
                [TheoremProto_0002.LHSPrimaryKey_UInt64 == TheoremProto_0002.RHSPrimaryKey_UInt64]
                [TheoremProto_0002.TotalProofsFound_UInt64 >= TheoremProto_0002.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0002, Axiom);

                Auto
                [TheoremProto_0002.LHSPrimaryKey_UInt64 == TheoremProto_0002.RHSPrimaryKey_UInt64]
                [TheoremProto_0002.TotalProofsFound_UInt64 >= TheoremProto_0002.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0002, Axiom);


                Auto
                [TheoremProto_0003.LHSPrimaryKey_UInt64 == TheoremProto_0003.RHSPrimaryKey_UInt64]
                [TheoremProto_0003.TotalProofsFound_UInt64 >= TheoremProto_0003.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0003, Axiom);

                Auto
                [TheoremProto_0003.LHSPrimaryKey_UInt64 == TheoremProto_0003.RHSPrimaryKey_UInt64]
                [TheoremProto_0003.TotalProofsFound_UInt64 >= TheoremProto_0003.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0003, Axiom);

                Auto
                [TheoremProto_0004.LHSPrimaryKey_UInt64 == TheoremProto_0004.RHSPrimaryKey_UInt64]
                [TheoremProto_0004.TotalProofsFound_UInt64 >= TheoremProto_0004.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0004, Axiom);

                Auto
                [TheoremProto_0004.LHSPrimaryKey_UInt64 == TheoremProto_0004.RHSPrimaryKey_UInt64]
                [TheoremProto_0004.TotalProofsFound_UInt64 >= TheoremProto_0004.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0004, Axiom);

                Auto
                [TheoremProto_0005.LHSPrimaryKey_UInt64 == TheoremProto_0005.RHSPrimaryKey_UInt64]
                [TheoremProto_0005.TotalProofsFound_UInt64 >= TheoremProto_0005.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0005, Axiom);

                Auto
                [TheoremProto_0005.LHSPrimaryKey_UInt64 == TheoremProto_0005.RHSPrimaryKey_UInt64]
                [TheoremProto_0005.TotalProofsFound_UInt64 >= TheoremProto_0005.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0005, Axiom);

                limiter.release();
            }

        });

};

Auto
[true]
[true]
[RouteSource_EnumClass::_root]
[Indirection_EnumClass::_auto] =
[](Theorem_Struct InTheorem, const Axiom_Struct& InAxiom) -> void
{
    InTheorem.ProofStack_VecUInt64.push_back(InAxiom);

    if (InTheorem.LHSPrimaryKey_UInt64 == InTheorem.RHSPrimaryKey_UInt64)
    {
        InTheorem.ProofFound_Flag = true;
        ++InTheorem.TotalProofsFound_UInt64;
    }

    if (InTheorem.TotalProofsFound_UInt64 >= InTheorem.MaxAllowedProofs_UInt64)
        return;

    Theorem_Struct TheoremProto_0000 = InTheorem;
    Theorem_Struct TheoremProto_0001 = InTheorem;
    Theorem_Struct TheoremProto_0002 = InTheorem;
    Theorem_Struct TheoremProto_0003 = InTheorem;
    Theorem_Struct TheoremProto_0004 = InTheorem;
    Theorem_Struct TheoremProto_0005 = InTheorem;

    if (TheoremProto_0000.SubnetFound_LHS(InAxiom.LHSPrimaryKey_UInt64))
        TheoremProto_0000.UpdatePrimaryKey_LHS(InAxiom.LHSPrimaryKey_UInt64);

    TheoremProto_0001.UpdatePrimaryKey_RHS(InAxiom.LHSPrimaryKey_UInt64);
    TheoremProto_0002.UpdatePrimaryKey_LHS(InAxiom.LHSPrimaryKey_UInt64);
    TheoremProto_0002.UpdatePrimaryKey_RHS(InAxiom.RHSPrimaryKey_UInt64);

    TheoremProto_0003.UpdatePrimaryKey_LHS(InAxiom.RHSPrimaryKey_UInt64);
    TheoremProto_0004.UpdatePrimaryKey_RHS(InAxiom.RHSPrimaryKey_UInt64);
    TheoremProto_0005.UpdatePrimaryKey_LHS(InAxiom.RHSPrimaryKey_UInt64);
    TheoremProto_0005.UpdatePrimaryKey_RHS(InAxiom.LHSPrimaryKey_UInt64);

    std::for_each(std::execution::par_unseq,
        Axioms_Vec.begin(),
        Axioms_Vec.end(),
        [&](const Axiom_Struct& Axiom)
        {
            RecursionLimiter::Invoke limiter(6);
            if (limiter.acquired())
            {
                Auto
                [TheoremProto_0000.LHSPrimaryKey_UInt64 == TheoremProto_0000.RHSPrimaryKey_UInt64]
                [TheoremProto_0000.TotalProofsFound_UInt64 >= TheoremProto_0000.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0000, Axiom);

                Auto
                [TheoremProto_0000.LHSPrimaryKey_UInt64 == TheoremProto_0000.RHSPrimaryKey_UInt64]
                [TheoremProto_0000.TotalProofsFound_UInt64 >= TheoremProto_0000.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0000, Axiom);

                Auto
                [TheoremProto_0001.LHSPrimaryKey_UInt64 == TheoremProto_0001.RHSPrimaryKey_UInt64]
                [TheoremProto_0001.TotalProofsFound_UInt64 >= TheoremProto_0001.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0001, Axiom);

                Auto
                [TheoremProto_0001.LHSPrimaryKey_UInt64 == TheoremProto_0001.RHSPrimaryKey_UInt64]
                [TheoremProto_0001.TotalProofsFound_UInt64 >= TheoremProto_0001.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0001, Axiom);

                Auto
                [TheoremProto_0002.LHSPrimaryKey_UInt64 == TheoremProto_0002.RHSPrimaryKey_UInt64]
                [TheoremProto_0002.TotalProofsFound_UInt64 >= TheoremProto_0002.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0002, Axiom);

                Auto
                [TheoremProto_0002.LHSPrimaryKey_UInt64 == TheoremProto_0002.RHSPrimaryKey_UInt64]
                [TheoremProto_0002.TotalProofsFound_UInt64 >= TheoremProto_0002.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0002, Axiom);

                limiter.release();
            }

        });

    std::for_each(std::execution::par_unseq,
        Axioms_Vec.begin(),
        Axioms_Vec.end(),
        [&](const Axiom_Struct& Axiom)
        {
            RecursionLimiter::Invoke limiter(6);
            if (limiter.acquired())
            {
                Auto
                [TheoremProto_0003.LHSPrimaryKey_UInt64 == TheoremProto_0003.RHSPrimaryKey_UInt64]
                [TheoremProto_0003.TotalProofsFound_UInt64 >= TheoremProto_0003.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0003, Axiom);

                Auto
                [TheoremProto_0003.LHSPrimaryKey_UInt64 == TheoremProto_0003.RHSPrimaryKey_UInt64]
                [TheoremProto_0003.TotalProofsFound_UInt64 >= TheoremProto_0003.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0003, Axiom);

                Auto
                [TheoremProto_0004.LHSPrimaryKey_UInt64 == TheoremProto_0004.RHSPrimaryKey_UInt64]
                [TheoremProto_0004.TotalProofsFound_UInt64 >= TheoremProto_0004.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0004, Axiom);

                Auto
                [TheoremProto_0004.LHSPrimaryKey_UInt64 == TheoremProto_0004.RHSPrimaryKey_UInt64]
                [TheoremProto_0004.TotalProofsFound_UInt64 >= TheoremProto_0004.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0004, Axiom);

                Auto
                [TheoremProto_0005.LHSPrimaryKey_UInt64 == TheoremProto_0005.RHSPrimaryKey_UInt64]
                [TheoremProto_0005.TotalProofsFound_UInt64 >= TheoremProto_0005.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0005, Axiom);

                Auto
                [TheoremProto_0005.LHSPrimaryKey_UInt64 == TheoremProto_0005.RHSPrimaryKey_UInt64]
                [TheoremProto_0005.TotalProofsFound_UInt64 >= TheoremProto_0005.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0005, Axiom);

                limiter.release();
            }

        });

    std::for_each(std::execution::par_unseq,
        Axioms_Vec.begin(),
        Axioms_Vec.end(),
        [&](const Axiom_Struct& Axiom)
        {
            RecursionLimiter::Invoke limiter(12);
            if (limiter.acquired())
            {
                Auto
                [TheoremProto_0000.LHSPrimaryKey_UInt64 == TheoremProto_0000.RHSPrimaryKey_UInt64]
                [TheoremProto_0000.TotalProofsFound_UInt64 >= TheoremProto_0000.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0000, Axiom);

                Auto
                [TheoremProto_0000.LHSPrimaryKey_UInt64 == TheoremProto_0000.RHSPrimaryKey_UInt64]
                [TheoremProto_0000.TotalProofsFound_UInt64 >= TheoremProto_0000.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0000, Axiom);

                Auto
                [TheoremProto_0001.LHSPrimaryKey_UInt64 == TheoremProto_0001.RHSPrimaryKey_UInt64]
                [TheoremProto_0001.TotalProofsFound_UInt64 >= TheoremProto_0001.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0001, Axiom);

                Auto
                [TheoremProto_0001.LHSPrimaryKey_UInt64 == TheoremProto_0001.RHSPrimaryKey_UInt64]
                [TheoremProto_0001.TotalProofsFound_UInt64 >= TheoremProto_0001.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0001, Axiom);

                Auto
                [TheoremProto_0002.LHSPrimaryKey_UInt64 == TheoremProto_0002.RHSPrimaryKey_UInt64]
                [TheoremProto_0002.TotalProofsFound_UInt64 >= TheoremProto_0002.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0002, Axiom);

                Auto
                [TheoremProto_0002.LHSPrimaryKey_UInt64 == TheoremProto_0002.RHSPrimaryKey_UInt64]
                [TheoremProto_0002.TotalProofsFound_UInt64 >= TheoremProto_0002.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0002, Axiom);


                Auto
                [TheoremProto_0003.LHSPrimaryKey_UInt64 == TheoremProto_0003.RHSPrimaryKey_UInt64]
                [TheoremProto_0003.TotalProofsFound_UInt64 >= TheoremProto_0003.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0003, Axiom);

                Auto
                [TheoremProto_0003.LHSPrimaryKey_UInt64 == TheoremProto_0003.RHSPrimaryKey_UInt64]
                [TheoremProto_0003.TotalProofsFound_UInt64 >= TheoremProto_0003.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0003, Axiom);

                Auto
                [TheoremProto_0004.LHSPrimaryKey_UInt64 == TheoremProto_0004.RHSPrimaryKey_UInt64]
                [TheoremProto_0004.TotalProofsFound_UInt64 >= TheoremProto_0004.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0004, Axiom);

                Auto
                [TheoremProto_0004.LHSPrimaryKey_UInt64 == TheoremProto_0004.RHSPrimaryKey_UInt64]
                [TheoremProto_0004.TotalProofsFound_UInt64 >= TheoremProto_0004.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0004, Axiom);

                Auto
                [TheoremProto_0005.LHSPrimaryKey_UInt64 == TheoremProto_0005.RHSPrimaryKey_UInt64]
                [TheoremProto_0005.TotalProofsFound_UInt64 >= TheoremProto_0005.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0005, Axiom);

                Auto
                [TheoremProto_0005.LHSPrimaryKey_UInt64 == TheoremProto_0005.RHSPrimaryKey_UInt64]
                [TheoremProto_0005.TotalProofsFound_UInt64 >= TheoremProto_0005.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0005, Axiom);

                limiter.release();
            }

        });

};

Auto
[true]
[true]
[RouteSource_EnumClass::_root]
[Indirection_EnumClass::_reduce] =
[](Theorem_Struct InTheorem, const Axiom_Struct& InAxiom) -> void
{
    InTheorem.ProofStack_VecUInt64.push_back(InAxiom);

    if (InTheorem.LHSPrimaryKey_UInt64 == InTheorem.RHSPrimaryKey_UInt64)
    {
        InTheorem.ProofFound_Flag = true;
        ++InTheorem.TotalProofsFound_UInt64;
    }

    if (InTheorem.TotalProofsFound_UInt64 >= InTheorem.MaxAllowedProofs_UInt64)
        return;

    Theorem_Struct TheoremProto_0000 = InTheorem;
    Theorem_Struct TheoremProto_0001 = InTheorem;
    Theorem_Struct TheoremProto_0002 = InTheorem;
    Theorem_Struct TheoremProto_0003 = InTheorem;
    Theorem_Struct TheoremProto_0004 = InTheorem;
    Theorem_Struct TheoremProto_0005 = InTheorem;

    if (TheoremProto_0000.SubnetFound_LHS(InAxiom.LHSPrimaryKey_UInt64))
        TheoremProto_0000.UpdatePrimaryKey_LHS(InAxiom.LHSPrimaryKey_UInt64);

    TheoremProto_0001.UpdatePrimaryKey_RHS(InAxiom.LHSPrimaryKey_UInt64);
    TheoremProto_0002.UpdatePrimaryKey_LHS(InAxiom.LHSPrimaryKey_UInt64);
    TheoremProto_0002.UpdatePrimaryKey_RHS(InAxiom.RHSPrimaryKey_UInt64);

    TheoremProto_0003.UpdatePrimaryKey_LHS(InAxiom.RHSPrimaryKey_UInt64);
    TheoremProto_0004.UpdatePrimaryKey_RHS(InAxiom.RHSPrimaryKey_UInt64);
    TheoremProto_0005.UpdatePrimaryKey_LHS(InAxiom.RHSPrimaryKey_UInt64);
    TheoremProto_0005.UpdatePrimaryKey_RHS(InAxiom.LHSPrimaryKey_UInt64);

    std::for_each(std::execution::par_unseq,
        Axioms_Vec.begin(),
        Axioms_Vec.end(),
        [&](const Axiom_Struct& Axiom)
        {
            RecursionLimiter::Invoke limiter(6);
            if (limiter.acquired())
            {
                Auto
                [TheoremProto_0000.LHSPrimaryKey_UInt64 == TheoremProto_0000.RHSPrimaryKey_UInt64]
                [TheoremProto_0000.TotalProofsFound_UInt64 >= TheoremProto_0000.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0000, Axiom);

                Auto
                [TheoremProto_0000.LHSPrimaryKey_UInt64 == TheoremProto_0000.RHSPrimaryKey_UInt64]
                [TheoremProto_0000.TotalProofsFound_UInt64 >= TheoremProto_0000.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0000, Axiom);

                Auto
                [TheoremProto_0001.LHSPrimaryKey_UInt64 == TheoremProto_0001.RHSPrimaryKey_UInt64]
                [TheoremProto_0001.TotalProofsFound_UInt64 >= TheoremProto_0001.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0001, Axiom);

                Auto
                [TheoremProto_0001.LHSPrimaryKey_UInt64 == TheoremProto_0001.RHSPrimaryKey_UInt64]
                [TheoremProto_0001.TotalProofsFound_UInt64 >= TheoremProto_0001.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0001, Axiom);

                Auto
                [TheoremProto_0002.LHSPrimaryKey_UInt64 == TheoremProto_0002.RHSPrimaryKey_UInt64]
                [TheoremProto_0002.TotalProofsFound_UInt64 >= TheoremProto_0002.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0002, Axiom);

                Auto
                [TheoremProto_0002.LHSPrimaryKey_UInt64 == TheoremProto_0002.RHSPrimaryKey_UInt64]
                [TheoremProto_0002.TotalProofsFound_UInt64 >= TheoremProto_0002.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0002, Axiom);

                limiter.release();
            }

        });

    std::for_each(std::execution::par_unseq,
        Axioms_Vec.begin(),
        Axioms_Vec.end(),
        [&](const Axiom_Struct& Axiom)
        {
            RecursionLimiter::Invoke limiter(6);
            if (limiter.acquired())
            {
                Auto
                [TheoremProto_0003.LHSPrimaryKey_UInt64 == TheoremProto_0003.RHSPrimaryKey_UInt64]
                [TheoremProto_0003.TotalProofsFound_UInt64 >= TheoremProto_0003.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0003, Axiom);

                Auto
                [TheoremProto_0003.LHSPrimaryKey_UInt64 == TheoremProto_0003.RHSPrimaryKey_UInt64]
                [TheoremProto_0003.TotalProofsFound_UInt64 >= TheoremProto_0003.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0003, Axiom);

                Auto
                [TheoremProto_0004.LHSPrimaryKey_UInt64 == TheoremProto_0004.RHSPrimaryKey_UInt64]
                [TheoremProto_0004.TotalProofsFound_UInt64 >= TheoremProto_0004.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0004, Axiom);

                Auto
                [TheoremProto_0004.LHSPrimaryKey_UInt64 == TheoremProto_0004.RHSPrimaryKey_UInt64]
                [TheoremProto_0004.TotalProofsFound_UInt64 >= TheoremProto_0004.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0004, Axiom);

                Auto
                [TheoremProto_0005.LHSPrimaryKey_UInt64 == TheoremProto_0005.RHSPrimaryKey_UInt64]
                [TheoremProto_0005.TotalProofsFound_UInt64 >= TheoremProto_0005.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0005, Axiom);

                Auto
                [TheoremProto_0005.LHSPrimaryKey_UInt64 == TheoremProto_0005.RHSPrimaryKey_UInt64]
                [TheoremProto_0005.TotalProofsFound_UInt64 >= TheoremProto_0005.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0005, Axiom);

                limiter.release();
            }

        });

    std::for_each(std::execution::par_unseq,
        Axioms_Vec.begin(),
        Axioms_Vec.end(),
        [&](const Axiom_Struct& Axiom)
        {
            RecursionLimiter::Invoke limiter(12);
            if (limiter.acquired())
            {
                Auto
                [TheoremProto_0000.LHSPrimaryKey_UInt64 == TheoremProto_0000.RHSPrimaryKey_UInt64]
                [TheoremProto_0000.TotalProofsFound_UInt64 >= TheoremProto_0000.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0000, Axiom);

                Auto
                [TheoremProto_0000.LHSPrimaryKey_UInt64 == TheoremProto_0000.RHSPrimaryKey_UInt64]
                [TheoremProto_0000.TotalProofsFound_UInt64 >= TheoremProto_0000.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0000, Axiom);

                Auto
                [TheoremProto_0001.LHSPrimaryKey_UInt64 == TheoremProto_0001.RHSPrimaryKey_UInt64]
                [TheoremProto_0001.TotalProofsFound_UInt64 >= TheoremProto_0001.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0001, Axiom);

                Auto
                [TheoremProto_0001.LHSPrimaryKey_UInt64 == TheoremProto_0001.RHSPrimaryKey_UInt64]
                [TheoremProto_0001.TotalProofsFound_UInt64 >= TheoremProto_0001.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0001, Axiom);

                Auto
                [TheoremProto_0002.LHSPrimaryKey_UInt64 == TheoremProto_0002.RHSPrimaryKey_UInt64]
                [TheoremProto_0002.TotalProofsFound_UInt64 >= TheoremProto_0002.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0002, Axiom);

                Auto
                [TheoremProto_0002.LHSPrimaryKey_UInt64 == TheoremProto_0002.RHSPrimaryKey_UInt64]
                [TheoremProto_0002.TotalProofsFound_UInt64 >= TheoremProto_0002.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0002, Axiom);


                Auto
                [TheoremProto_0003.LHSPrimaryKey_UInt64 == TheoremProto_0003.RHSPrimaryKey_UInt64]
                [TheoremProto_0003.TotalProofsFound_UInt64 >= TheoremProto_0003.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0003, Axiom);

                Auto
                [TheoremProto_0003.LHSPrimaryKey_UInt64 == TheoremProto_0003.RHSPrimaryKey_UInt64]
                [TheoremProto_0003.TotalProofsFound_UInt64 >= TheoremProto_0003.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0003, Axiom);

                Auto
                [TheoremProto_0004.LHSPrimaryKey_UInt64 == TheoremProto_0004.RHSPrimaryKey_UInt64]
                [TheoremProto_0004.TotalProofsFound_UInt64 >= TheoremProto_0004.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0004, Axiom);

                Auto
                [TheoremProto_0004.LHSPrimaryKey_UInt64 == TheoremProto_0004.RHSPrimaryKey_UInt64]
                [TheoremProto_0004.TotalProofsFound_UInt64 >= TheoremProto_0004.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0004, Axiom);

                Auto
                [TheoremProto_0005.LHSPrimaryKey_UInt64 == TheoremProto_0005.RHSPrimaryKey_UInt64]
                [TheoremProto_0005.TotalProofsFound_UInt64 >= TheoremProto_0005.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0005, Axiom);

                Auto
                [TheoremProto_0005.LHSPrimaryKey_UInt64 == TheoremProto_0005.RHSPrimaryKey_UInt64]
                [TheoremProto_0005.TotalProofsFound_UInt64 >= TheoremProto_0005.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0005, Axiom);

                limiter.release();
            }

        });

};

Auto
[true]
[true]
[RouteSource_EnumClass::_root]
[Indirection_EnumClass::_expand] =
[](Theorem_Struct InTheorem, const Axiom_Struct& InAxiom) -> void
{
    InTheorem.ProofStack_VecUInt64.push_back(InAxiom);

    if (InTheorem.LHSPrimaryKey_UInt64 == InTheorem.RHSPrimaryKey_UInt64)
    {
        InTheorem.ProofFound_Flag = true;
        ++InTheorem.TotalProofsFound_UInt64;
    }

    if (InTheorem.TotalProofsFound_UInt64 >= InTheorem.MaxAllowedProofs_UInt64)
        return;

    Theorem_Struct TheoremProto_0000 = InTheorem;
    Theorem_Struct TheoremProto_0001 = InTheorem;
    Theorem_Struct TheoremProto_0002 = InTheorem;
    Theorem_Struct TheoremProto_0003 = InTheorem;
    Theorem_Struct TheoremProto_0004 = InTheorem;
    Theorem_Struct TheoremProto_0005 = InTheorem;

    if (TheoremProto_0000.SubnetFound_LHS(InAxiom.LHSPrimaryKey_UInt64))
        TheoremProto_0000.UpdatePrimaryKey_LHS(InAxiom.LHSPrimaryKey_UInt64);

    TheoremProto_0001.UpdatePrimaryKey_RHS(InAxiom.LHSPrimaryKey_UInt64);
    TheoremProto_0002.UpdatePrimaryKey_LHS(InAxiom.LHSPrimaryKey_UInt64);
    TheoremProto_0002.UpdatePrimaryKey_RHS(InAxiom.RHSPrimaryKey_UInt64);

    TheoremProto_0003.UpdatePrimaryKey_LHS(InAxiom.RHSPrimaryKey_UInt64);
    TheoremProto_0004.UpdatePrimaryKey_RHS(InAxiom.RHSPrimaryKey_UInt64);
    TheoremProto_0005.UpdatePrimaryKey_LHS(InAxiom.RHSPrimaryKey_UInt64);
    TheoremProto_0005.UpdatePrimaryKey_RHS(InAxiom.LHSPrimaryKey_UInt64);

    std::for_each(std::execution::par_unseq,
        Axioms_Vec.begin(),
        Axioms_Vec.end(),
        [&](const Axiom_Struct& Axiom)
        {
            RecursionLimiter::Invoke limiter(6);
            if (limiter.acquired())
            {
                Auto
                [TheoremProto_0000.LHSPrimaryKey_UInt64 == TheoremProto_0000.RHSPrimaryKey_UInt64]
                [TheoremProto_0000.TotalProofsFound_UInt64 >= TheoremProto_0000.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0000, Axiom);

                Auto
                [TheoremProto_0000.LHSPrimaryKey_UInt64 == TheoremProto_0000.RHSPrimaryKey_UInt64]
                [TheoremProto_0000.TotalProofsFound_UInt64 >= TheoremProto_0000.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0000, Axiom);

                Auto
                [TheoremProto_0001.LHSPrimaryKey_UInt64 == TheoremProto_0001.RHSPrimaryKey_UInt64]
                [TheoremProto_0001.TotalProofsFound_UInt64 >= TheoremProto_0001.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0001, Axiom);

                Auto
                [TheoremProto_0001.LHSPrimaryKey_UInt64 == TheoremProto_0001.RHSPrimaryKey_UInt64]
                [TheoremProto_0001.TotalProofsFound_UInt64 >= TheoremProto_0001.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0001, Axiom);

                Auto
                [TheoremProto_0002.LHSPrimaryKey_UInt64 == TheoremProto_0002.RHSPrimaryKey_UInt64]
                [TheoremProto_0002.TotalProofsFound_UInt64 >= TheoremProto_0002.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0002, Axiom);

                Auto
                [TheoremProto_0002.LHSPrimaryKey_UInt64 == TheoremProto_0002.RHSPrimaryKey_UInt64]
                [TheoremProto_0002.TotalProofsFound_UInt64 >= TheoremProto_0002.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0002, Axiom);

                limiter.release();
            }

        });

    std::for_each(std::execution::par_unseq,
        Axioms_Vec.begin(),
        Axioms_Vec.end(),
        [&](const Axiom_Struct& Axiom)
        {
            RecursionLimiter::Invoke limiter(6);
            if (limiter.acquired())
            {
                Auto
                [TheoremProto_0003.LHSPrimaryKey_UInt64 == TheoremProto_0003.RHSPrimaryKey_UInt64]
                [TheoremProto_0003.TotalProofsFound_UInt64 >= TheoremProto_0003.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0003, Axiom);

                Auto
                [TheoremProto_0003.LHSPrimaryKey_UInt64 == TheoremProto_0003.RHSPrimaryKey_UInt64]
                [TheoremProto_0003.TotalProofsFound_UInt64 >= TheoremProto_0003.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0003, Axiom);

                Auto
                [TheoremProto_0004.LHSPrimaryKey_UInt64 == TheoremProto_0004.RHSPrimaryKey_UInt64]
                [TheoremProto_0004.TotalProofsFound_UInt64 >= TheoremProto_0004.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0004, Axiom);

                Auto
                [TheoremProto_0004.LHSPrimaryKey_UInt64 == TheoremProto_0004.RHSPrimaryKey_UInt64]
                [TheoremProto_0004.TotalProofsFound_UInt64 >= TheoremProto_0004.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0004, Axiom);

                Auto
                [TheoremProto_0005.LHSPrimaryKey_UInt64 == TheoremProto_0005.RHSPrimaryKey_UInt64]
                [TheoremProto_0005.TotalProofsFound_UInt64 >= TheoremProto_0005.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0005, Axiom);

                Auto
                [TheoremProto_0005.LHSPrimaryKey_UInt64 == TheoremProto_0005.RHSPrimaryKey_UInt64]
                [TheoremProto_0005.TotalProofsFound_UInt64 >= TheoremProto_0005.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0005, Axiom);

                limiter.release();
            }

        });

    std::for_each(std::execution::par_unseq,
        Axioms_Vec.begin(),
        Axioms_Vec.end(),
        [&](const Axiom_Struct& Axiom)
        {
            RecursionLimiter::Invoke limiter(12);
            if (limiter.acquired())
            {
                Auto
                [TheoremProto_0000.LHSPrimaryKey_UInt64 == TheoremProto_0000.RHSPrimaryKey_UInt64]
                [TheoremProto_0000.TotalProofsFound_UInt64 >= TheoremProto_0000.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0000, Axiom);

                Auto
                [TheoremProto_0000.LHSPrimaryKey_UInt64 == TheoremProto_0000.RHSPrimaryKey_UInt64]
                [TheoremProto_0000.TotalProofsFound_UInt64 >= TheoremProto_0000.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0000, Axiom);

                Auto
                [TheoremProto_0001.LHSPrimaryKey_UInt64 == TheoremProto_0001.RHSPrimaryKey_UInt64]
                [TheoremProto_0001.TotalProofsFound_UInt64 >= TheoremProto_0001.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0001, Axiom);

                Auto
                [TheoremProto_0001.LHSPrimaryKey_UInt64 == TheoremProto_0001.RHSPrimaryKey_UInt64]
                [TheoremProto_0001.TotalProofsFound_UInt64 >= TheoremProto_0001.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0001, Axiom);

                Auto
                [TheoremProto_0002.LHSPrimaryKey_UInt64 == TheoremProto_0002.RHSPrimaryKey_UInt64]
                [TheoremProto_0002.TotalProofsFound_UInt64 >= TheoremProto_0002.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0002, Axiom);

                Auto
                [TheoremProto_0002.LHSPrimaryKey_UInt64 == TheoremProto_0002.RHSPrimaryKey_UInt64]
                [TheoremProto_0002.TotalProofsFound_UInt64 >= TheoremProto_0002.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0002, Axiom);


                Auto
                [TheoremProto_0003.LHSPrimaryKey_UInt64 == TheoremProto_0003.RHSPrimaryKey_UInt64]
                [TheoremProto_0003.TotalProofsFound_UInt64 >= TheoremProto_0003.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0003, Axiom);

                Auto
                [TheoremProto_0003.LHSPrimaryKey_UInt64 == TheoremProto_0003.RHSPrimaryKey_UInt64]
                [TheoremProto_0003.TotalProofsFound_UInt64 >= TheoremProto_0003.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0003, Axiom);

                Auto
                [TheoremProto_0004.LHSPrimaryKey_UInt64 == TheoremProto_0004.RHSPrimaryKey_UInt64]
                [TheoremProto_0004.TotalProofsFound_UInt64 >= TheoremProto_0004.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0004, Axiom);

                Auto
                [TheoremProto_0004.LHSPrimaryKey_UInt64 == TheoremProto_0004.RHSPrimaryKey_UInt64]
                [TheoremProto_0004.TotalProofsFound_UInt64 >= TheoremProto_0004.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0004, Axiom);

                Auto
                [TheoremProto_0005.LHSPrimaryKey_UInt64 == TheoremProto_0005.RHSPrimaryKey_UInt64]
                [TheoremProto_0005.TotalProofsFound_UInt64 >= TheoremProto_0005.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0005, Axiom);

                Auto
                [TheoremProto_0005.LHSPrimaryKey_UInt64 == TheoremProto_0005.RHSPrimaryKey_UInt64]
                [TheoremProto_0005.TotalProofsFound_UInt64 >= TheoremProto_0005.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0005, Axiom);

                limiter.release();
            }

        });

};

Auto
[true]
[true]
[RouteSource_EnumClass::_lhs]
[Indirection_EnumClass::_auto] =
[](Theorem_Struct InTheorem, const Axiom_Struct& InAxiom) -> void
{
    InTheorem.ProofStack_VecUInt64.push_back(InAxiom);

    if (InTheorem.LHSPrimaryKey_UInt64 == InTheorem.RHSPrimaryKey_UInt64)
    {
        InTheorem.ProofFound_Flag = true;
        ++InTheorem.TotalProofsFound_UInt64;
    }

    if (InTheorem.TotalProofsFound_UInt64 >= InTheorem.MaxAllowedProofs_UInt64)
        return;

    Theorem_Struct TheoremProto_0000 = InTheorem;
    Theorem_Struct TheoremProto_0001 = InTheorem;
    Theorem_Struct TheoremProto_0002 = InTheorem;
    Theorem_Struct TheoremProto_0003 = InTheorem;
    Theorem_Struct TheoremProto_0004 = InTheorem;
    Theorem_Struct TheoremProto_0005 = InTheorem;

    if (TheoremProto_0000.SubnetFound_LHS(InAxiom.LHSPrimaryKey_UInt64))
        TheoremProto_0000.UpdatePrimaryKey_LHS(InAxiom.LHSPrimaryKey_UInt64);

    TheoremProto_0001.UpdatePrimaryKey_RHS(InAxiom.LHSPrimaryKey_UInt64);
    TheoremProto_0002.UpdatePrimaryKey_LHS(InAxiom.LHSPrimaryKey_UInt64);
    TheoremProto_0002.UpdatePrimaryKey_RHS(InAxiom.RHSPrimaryKey_UInt64);

    TheoremProto_0003.UpdatePrimaryKey_LHS(InAxiom.RHSPrimaryKey_UInt64);
    TheoremProto_0004.UpdatePrimaryKey_RHS(InAxiom.RHSPrimaryKey_UInt64);
    TheoremProto_0005.UpdatePrimaryKey_LHS(InAxiom.RHSPrimaryKey_UInt64);
    TheoremProto_0005.UpdatePrimaryKey_RHS(InAxiom.LHSPrimaryKey_UInt64);

    std::for_each(std::execution::par_unseq,
        Axioms_Vec.begin(),
        Axioms_Vec.end(),
        [&](const Axiom_Struct& Axiom)
        {
            RecursionLimiter::Invoke limiter(6);
            if (limiter.acquired())
            {
                Auto
                [TheoremProto_0000.LHSPrimaryKey_UInt64 == TheoremProto_0000.RHSPrimaryKey_UInt64]
                [TheoremProto_0000.TotalProofsFound_UInt64 >= TheoremProto_0000.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0000, Axiom);

                Auto
                [TheoremProto_0000.LHSPrimaryKey_UInt64 == TheoremProto_0000.RHSPrimaryKey_UInt64]
                [TheoremProto_0000.TotalProofsFound_UInt64 >= TheoremProto_0000.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0000, Axiom);

                Auto
                [TheoremProto_0001.LHSPrimaryKey_UInt64 == TheoremProto_0001.RHSPrimaryKey_UInt64]
                [TheoremProto_0001.TotalProofsFound_UInt64 >= TheoremProto_0001.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0001, Axiom);

                Auto
                [TheoremProto_0001.LHSPrimaryKey_UInt64 == TheoremProto_0001.RHSPrimaryKey_UInt64]
                [TheoremProto_0001.TotalProofsFound_UInt64 >= TheoremProto_0001.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0001, Axiom);

                Auto
                [TheoremProto_0002.LHSPrimaryKey_UInt64 == TheoremProto_0002.RHSPrimaryKey_UInt64]
                [TheoremProto_0002.TotalProofsFound_UInt64 >= TheoremProto_0002.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0002, Axiom);

                Auto
                [TheoremProto_0002.LHSPrimaryKey_UInt64 == TheoremProto_0002.RHSPrimaryKey_UInt64]
                [TheoremProto_0002.TotalProofsFound_UInt64 >= TheoremProto_0002.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0002, Axiom);

                limiter.release();
            }

        });

    std::for_each(std::execution::par_unseq,
        Axioms_Vec.begin(),
        Axioms_Vec.end(),
        [&](const Axiom_Struct& Axiom)
        {
            RecursionLimiter::Invoke limiter(6);
            if (limiter.acquired())
            {
                Auto
                [TheoremProto_0003.LHSPrimaryKey_UInt64 == TheoremProto_0003.RHSPrimaryKey_UInt64]
                [TheoremProto_0003.TotalProofsFound_UInt64 >= TheoremProto_0003.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0003, Axiom);

                Auto
                [TheoremProto_0003.LHSPrimaryKey_UInt64 == TheoremProto_0003.RHSPrimaryKey_UInt64]
                [TheoremProto_0003.TotalProofsFound_UInt64 >= TheoremProto_0003.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0003, Axiom);

                Auto
                [TheoremProto_0004.LHSPrimaryKey_UInt64 == TheoremProto_0004.RHSPrimaryKey_UInt64]
                [TheoremProto_0004.TotalProofsFound_UInt64 >= TheoremProto_0004.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0004, Axiom);

                Auto
                [TheoremProto_0004.LHSPrimaryKey_UInt64 == TheoremProto_0004.RHSPrimaryKey_UInt64]
                [TheoremProto_0004.TotalProofsFound_UInt64 >= TheoremProto_0004.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0004, Axiom);

                Auto
                [TheoremProto_0005.LHSPrimaryKey_UInt64 == TheoremProto_0005.RHSPrimaryKey_UInt64]
                [TheoremProto_0005.TotalProofsFound_UInt64 >= TheoremProto_0005.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0005, Axiom);

                Auto
                [TheoremProto_0005.LHSPrimaryKey_UInt64 == TheoremProto_0005.RHSPrimaryKey_UInt64]
                [TheoremProto_0005.TotalProofsFound_UInt64 >= TheoremProto_0005.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0005, Axiom);

                limiter.release();
            }

        });

    std::for_each(std::execution::par_unseq,
        Axioms_Vec.begin(),
        Axioms_Vec.end(),
        [&](const Axiom_Struct& Axiom)
        {
            RecursionLimiter::Invoke limiter(12);
            if (limiter.acquired())
            {
                Auto
                [TheoremProto_0000.LHSPrimaryKey_UInt64 == TheoremProto_0000.RHSPrimaryKey_UInt64]
                [TheoremProto_0000.TotalProofsFound_UInt64 >= TheoremProto_0000.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0000, Axiom);

                Auto
                [TheoremProto_0000.LHSPrimaryKey_UInt64 == TheoremProto_0000.RHSPrimaryKey_UInt64]
                [TheoremProto_0000.TotalProofsFound_UInt64 >= TheoremProto_0000.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0000, Axiom);

                Auto
                [TheoremProto_0001.LHSPrimaryKey_UInt64 == TheoremProto_0001.RHSPrimaryKey_UInt64]
                [TheoremProto_0001.TotalProofsFound_UInt64 >= TheoremProto_0001.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0001, Axiom);

                Auto
                [TheoremProto_0001.LHSPrimaryKey_UInt64 == TheoremProto_0001.RHSPrimaryKey_UInt64]
                [TheoremProto_0001.TotalProofsFound_UInt64 >= TheoremProto_0001.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0001, Axiom);

                Auto
                [TheoremProto_0002.LHSPrimaryKey_UInt64 == TheoremProto_0002.RHSPrimaryKey_UInt64]
                [TheoremProto_0002.TotalProofsFound_UInt64 >= TheoremProto_0002.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0002, Axiom);

                Auto
                [TheoremProto_0002.LHSPrimaryKey_UInt64 == TheoremProto_0002.RHSPrimaryKey_UInt64]
                [TheoremProto_0002.TotalProofsFound_UInt64 >= TheoremProto_0002.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0002, Axiom);


                Auto
                [TheoremProto_0003.LHSPrimaryKey_UInt64 == TheoremProto_0003.RHSPrimaryKey_UInt64]
                [TheoremProto_0003.TotalProofsFound_UInt64 >= TheoremProto_0003.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0003, Axiom);

                Auto
                [TheoremProto_0003.LHSPrimaryKey_UInt64 == TheoremProto_0003.RHSPrimaryKey_UInt64]
                [TheoremProto_0003.TotalProofsFound_UInt64 >= TheoremProto_0003.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0003, Axiom);

                Auto
                [TheoremProto_0004.LHSPrimaryKey_UInt64 == TheoremProto_0004.RHSPrimaryKey_UInt64]
                [TheoremProto_0004.TotalProofsFound_UInt64 >= TheoremProto_0004.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0004, Axiom);

                Auto
                [TheoremProto_0004.LHSPrimaryKey_UInt64 == TheoremProto_0004.RHSPrimaryKey_UInt64]
                [TheoremProto_0004.TotalProofsFound_UInt64 >= TheoremProto_0004.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0004, Axiom);

                Auto
                [TheoremProto_0005.LHSPrimaryKey_UInt64 == TheoremProto_0005.RHSPrimaryKey_UInt64]
                [TheoremProto_0005.TotalProofsFound_UInt64 >= TheoremProto_0005.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0005, Axiom);

                Auto
                [TheoremProto_0005.LHSPrimaryKey_UInt64 == TheoremProto_0005.RHSPrimaryKey_UInt64]
                [TheoremProto_0005.TotalProofsFound_UInt64 >= TheoremProto_0005.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0005, Axiom);

                limiter.release();
            }

        });

};

Auto
[true]
[true]
[RouteSource_EnumClass::_lhs]
[Indirection_EnumClass::_reduce] =
[](Theorem_Struct InTheorem, const Axiom_Struct& InAxiom) -> void
{
    InTheorem.ProofStack_VecUInt64.push_back(InAxiom);

    if (InTheorem.LHSPrimaryKey_UInt64 == InTheorem.RHSPrimaryKey_UInt64)
    {
        InTheorem.ProofFound_Flag = true;
        ++InTheorem.TotalProofsFound_UInt64;
    }

    if (InTheorem.TotalProofsFound_UInt64 >= InTheorem.MaxAllowedProofs_UInt64)
        return;

    Theorem_Struct TheoremProto_0000 = InTheorem;
    Theorem_Struct TheoremProto_0001 = InTheorem;
    Theorem_Struct TheoremProto_0002 = InTheorem;
    Theorem_Struct TheoremProto_0003 = InTheorem;
    Theorem_Struct TheoremProto_0004 = InTheorem;
    Theorem_Struct TheoremProto_0005 = InTheorem;

    if (TheoremProto_0000.SubnetFound_LHS(InAxiom.LHSPrimaryKey_UInt64))
        TheoremProto_0000.UpdatePrimaryKey_LHS(InAxiom.LHSPrimaryKey_UInt64);

    TheoremProto_0001.UpdatePrimaryKey_RHS(InAxiom.LHSPrimaryKey_UInt64);
    TheoremProto_0002.UpdatePrimaryKey_LHS(InAxiom.LHSPrimaryKey_UInt64);
    TheoremProto_0002.UpdatePrimaryKey_RHS(InAxiom.RHSPrimaryKey_UInt64);

    TheoremProto_0003.UpdatePrimaryKey_LHS(InAxiom.RHSPrimaryKey_UInt64);
    TheoremProto_0004.UpdatePrimaryKey_RHS(InAxiom.RHSPrimaryKey_UInt64);
    TheoremProto_0005.UpdatePrimaryKey_LHS(InAxiom.RHSPrimaryKey_UInt64);
    TheoremProto_0005.UpdatePrimaryKey_RHS(InAxiom.LHSPrimaryKey_UInt64);

    std::for_each(std::execution::par_unseq,
        Axioms_Vec.begin(),
        Axioms_Vec.end(),
        [&](const Axiom_Struct& Axiom)
        {
            RecursionLimiter::Invoke limiter(6);
            if (limiter.acquired())
            {
                Auto
                [TheoremProto_0000.LHSPrimaryKey_UInt64 == TheoremProto_0000.RHSPrimaryKey_UInt64]
                [TheoremProto_0000.TotalProofsFound_UInt64 >= TheoremProto_0000.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0000, Axiom);

                Auto
                [TheoremProto_0000.LHSPrimaryKey_UInt64 == TheoremProto_0000.RHSPrimaryKey_UInt64]
                [TheoremProto_0000.TotalProofsFound_UInt64 >= TheoremProto_0000.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0000, Axiom);

                Auto
                [TheoremProto_0001.LHSPrimaryKey_UInt64 == TheoremProto_0001.RHSPrimaryKey_UInt64]
                [TheoremProto_0001.TotalProofsFound_UInt64 >= TheoremProto_0001.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0001, Axiom);

                Auto
                [TheoremProto_0001.LHSPrimaryKey_UInt64 == TheoremProto_0001.RHSPrimaryKey_UInt64]
                [TheoremProto_0001.TotalProofsFound_UInt64 >= TheoremProto_0001.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0001, Axiom);

                Auto
                [TheoremProto_0002.LHSPrimaryKey_UInt64 == TheoremProto_0002.RHSPrimaryKey_UInt64]
                [TheoremProto_0002.TotalProofsFound_UInt64 >= TheoremProto_0002.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0002, Axiom);

                Auto
                [TheoremProto_0002.LHSPrimaryKey_UInt64 == TheoremProto_0002.RHSPrimaryKey_UInt64]
                [TheoremProto_0002.TotalProofsFound_UInt64 >= TheoremProto_0002.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0002, Axiom);

                limiter.release();
            }

        });

    std::for_each(std::execution::par_unseq,
        Axioms_Vec.begin(),
        Axioms_Vec.end(),
        [&](const Axiom_Struct& Axiom)
        {
            RecursionLimiter::Invoke limiter(6);
            if (limiter.acquired())
            {
                Auto
                [TheoremProto_0003.LHSPrimaryKey_UInt64 == TheoremProto_0003.RHSPrimaryKey_UInt64]
                [TheoremProto_0003.TotalProofsFound_UInt64 >= TheoremProto_0003.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0003, Axiom);

                Auto
                [TheoremProto_0003.LHSPrimaryKey_UInt64 == TheoremProto_0003.RHSPrimaryKey_UInt64]
                [TheoremProto_0003.TotalProofsFound_UInt64 >= TheoremProto_0003.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0003, Axiom);

                Auto
                [TheoremProto_0004.LHSPrimaryKey_UInt64 == TheoremProto_0004.RHSPrimaryKey_UInt64]
                [TheoremProto_0004.TotalProofsFound_UInt64 >= TheoremProto_0004.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0004, Axiom);

                Auto
                [TheoremProto_0004.LHSPrimaryKey_UInt64 == TheoremProto_0004.RHSPrimaryKey_UInt64]
                [TheoremProto_0004.TotalProofsFound_UInt64 >= TheoremProto_0004.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0004, Axiom);

                Auto
                [TheoremProto_0005.LHSPrimaryKey_UInt64 == TheoremProto_0005.RHSPrimaryKey_UInt64]
                [TheoremProto_0005.TotalProofsFound_UInt64 >= TheoremProto_0005.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0005, Axiom);

                Auto
                [TheoremProto_0005.LHSPrimaryKey_UInt64 == TheoremProto_0005.RHSPrimaryKey_UInt64]
                [TheoremProto_0005.TotalProofsFound_UInt64 >= TheoremProto_0005.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0005, Axiom);

                limiter.release();
            }

        });

    std::for_each(std::execution::par_unseq,
        Axioms_Vec.begin(),
        Axioms_Vec.end(),
        [&](const Axiom_Struct& Axiom)
        {
            RecursionLimiter::Invoke limiter(12);
            if (limiter.acquired())
            {
                Auto
                [TheoremProto_0000.LHSPrimaryKey_UInt64 == TheoremProto_0000.RHSPrimaryKey_UInt64]
                [TheoremProto_0000.TotalProofsFound_UInt64 >= TheoremProto_0000.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0000, Axiom);

                Auto
                [TheoremProto_0000.LHSPrimaryKey_UInt64 == TheoremProto_0000.RHSPrimaryKey_UInt64]
                [TheoremProto_0000.TotalProofsFound_UInt64 >= TheoremProto_0000.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0000, Axiom);

                Auto
                [TheoremProto_0001.LHSPrimaryKey_UInt64 == TheoremProto_0001.RHSPrimaryKey_UInt64]
                [TheoremProto_0001.TotalProofsFound_UInt64 >= TheoremProto_0001.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0001, Axiom);

                Auto
                [TheoremProto_0001.LHSPrimaryKey_UInt64 == TheoremProto_0001.RHSPrimaryKey_UInt64]
                [TheoremProto_0001.TotalProofsFound_UInt64 >= TheoremProto_0001.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0001, Axiom);

                Auto
                [TheoremProto_0002.LHSPrimaryKey_UInt64 == TheoremProto_0002.RHSPrimaryKey_UInt64]
                [TheoremProto_0002.TotalProofsFound_UInt64 >= TheoremProto_0002.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0002, Axiom);

                Auto
                [TheoremProto_0002.LHSPrimaryKey_UInt64 == TheoremProto_0002.RHSPrimaryKey_UInt64]
                [TheoremProto_0002.TotalProofsFound_UInt64 >= TheoremProto_0002.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0002, Axiom);


                Auto
                [TheoremProto_0003.LHSPrimaryKey_UInt64 == TheoremProto_0003.RHSPrimaryKey_UInt64]
                [TheoremProto_0003.TotalProofsFound_UInt64 >= TheoremProto_0003.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0003, Axiom);

                Auto
                [TheoremProto_0003.LHSPrimaryKey_UInt64 == TheoremProto_0003.RHSPrimaryKey_UInt64]
                [TheoremProto_0003.TotalProofsFound_UInt64 >= TheoremProto_0003.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0003, Axiom);

                Auto
                [TheoremProto_0004.LHSPrimaryKey_UInt64 == TheoremProto_0004.RHSPrimaryKey_UInt64]
                [TheoremProto_0004.TotalProofsFound_UInt64 >= TheoremProto_0004.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0004, Axiom);

                Auto
                [TheoremProto_0004.LHSPrimaryKey_UInt64 == TheoremProto_0004.RHSPrimaryKey_UInt64]
                [TheoremProto_0004.TotalProofsFound_UInt64 >= TheoremProto_0004.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0004, Axiom);

                Auto
                [TheoremProto_0005.LHSPrimaryKey_UInt64 == TheoremProto_0005.RHSPrimaryKey_UInt64]
                [TheoremProto_0005.TotalProofsFound_UInt64 >= TheoremProto_0005.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0005, Axiom);

                Auto
                [TheoremProto_0005.LHSPrimaryKey_UInt64 == TheoremProto_0005.RHSPrimaryKey_UInt64]
                [TheoremProto_0005.TotalProofsFound_UInt64 >= TheoremProto_0005.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0005, Axiom);

                limiter.release();
            }

        });

};

Auto
[true]
[true]
[RouteSource_EnumClass::_lhs]
[Indirection_EnumClass::_expand] =
[](Theorem_Struct InTheorem, const Axiom_Struct& InAxiom) -> void
{
    InTheorem.ProofStack_VecUInt64.push_back(InAxiom);

    if (InTheorem.LHSPrimaryKey_UInt64 == InTheorem.RHSPrimaryKey_UInt64)
    {
        InTheorem.ProofFound_Flag = true;
        ++InTheorem.TotalProofsFound_UInt64;
    }

    if (InTheorem.TotalProofsFound_UInt64 >= InTheorem.MaxAllowedProofs_UInt64)
        return;

    Theorem_Struct TheoremProto_0000 = InTheorem;
    Theorem_Struct TheoremProto_0001 = InTheorem;
    Theorem_Struct TheoremProto_0002 = InTheorem;
    Theorem_Struct TheoremProto_0003 = InTheorem;
    Theorem_Struct TheoremProto_0004 = InTheorem;
    Theorem_Struct TheoremProto_0005 = InTheorem;

    if (TheoremProto_0000.SubnetFound_LHS(InAxiom.LHSPrimaryKey_UInt64))
        TheoremProto_0000.UpdatePrimaryKey_LHS(InAxiom.LHSPrimaryKey_UInt64);

    TheoremProto_0001.UpdatePrimaryKey_RHS(InAxiom.LHSPrimaryKey_UInt64);
    TheoremProto_0002.UpdatePrimaryKey_LHS(InAxiom.LHSPrimaryKey_UInt64);
    TheoremProto_0002.UpdatePrimaryKey_RHS(InAxiom.RHSPrimaryKey_UInt64);

    TheoremProto_0003.UpdatePrimaryKey_LHS(InAxiom.RHSPrimaryKey_UInt64);
    TheoremProto_0004.UpdatePrimaryKey_RHS(InAxiom.RHSPrimaryKey_UInt64);
    TheoremProto_0005.UpdatePrimaryKey_LHS(InAxiom.RHSPrimaryKey_UInt64);
    TheoremProto_0005.UpdatePrimaryKey_RHS(InAxiom.LHSPrimaryKey_UInt64);

    std::for_each(std::execution::par_unseq,
        Axioms_Vec.begin(),
        Axioms_Vec.end(),
        [&](const Axiom_Struct& Axiom)
        {
            RecursionLimiter::Invoke limiter(6);
            if (limiter.acquired())
            {
                Auto
                [TheoremProto_0000.LHSPrimaryKey_UInt64 == TheoremProto_0000.RHSPrimaryKey_UInt64]
                [TheoremProto_0000.TotalProofsFound_UInt64 >= TheoremProto_0000.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0000, Axiom);

                Auto
                [TheoremProto_0000.LHSPrimaryKey_UInt64 == TheoremProto_0000.RHSPrimaryKey_UInt64]
                [TheoremProto_0000.TotalProofsFound_UInt64 >= TheoremProto_0000.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0000, Axiom);

                Auto
                [TheoremProto_0001.LHSPrimaryKey_UInt64 == TheoremProto_0001.RHSPrimaryKey_UInt64]
                [TheoremProto_0001.TotalProofsFound_UInt64 >= TheoremProto_0001.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0001, Axiom);

                Auto
                [TheoremProto_0001.LHSPrimaryKey_UInt64 == TheoremProto_0001.RHSPrimaryKey_UInt64]
                [TheoremProto_0001.TotalProofsFound_UInt64 >= TheoremProto_0001.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0001, Axiom);

                Auto
                [TheoremProto_0002.LHSPrimaryKey_UInt64 == TheoremProto_0002.RHSPrimaryKey_UInt64]
                [TheoremProto_0002.TotalProofsFound_UInt64 >= TheoremProto_0002.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0002, Axiom);

                Auto
                [TheoremProto_0002.LHSPrimaryKey_UInt64 == TheoremProto_0002.RHSPrimaryKey_UInt64]
                [TheoremProto_0002.TotalProofsFound_UInt64 >= TheoremProto_0002.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0002, Axiom);

                limiter.release();
            }

        });

    std::for_each(std::execution::par_unseq,
        Axioms_Vec.begin(),
        Axioms_Vec.end(),
        [&](const Axiom_Struct& Axiom)
        {
            RecursionLimiter::Invoke limiter(6);
            if (limiter.acquired())
            {
                Auto
                [TheoremProto_0003.LHSPrimaryKey_UInt64 == TheoremProto_0003.RHSPrimaryKey_UInt64]
                [TheoremProto_0003.TotalProofsFound_UInt64 >= TheoremProto_0003.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0003, Axiom);

                Auto
                [TheoremProto_0003.LHSPrimaryKey_UInt64 == TheoremProto_0003.RHSPrimaryKey_UInt64]
                [TheoremProto_0003.TotalProofsFound_UInt64 >= TheoremProto_0003.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0003, Axiom);

                Auto
                [TheoremProto_0004.LHSPrimaryKey_UInt64 == TheoremProto_0004.RHSPrimaryKey_UInt64]
                [TheoremProto_0004.TotalProofsFound_UInt64 >= TheoremProto_0004.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0004, Axiom);

                Auto
                [TheoremProto_0004.LHSPrimaryKey_UInt64 == TheoremProto_0004.RHSPrimaryKey_UInt64]
                [TheoremProto_0004.TotalProofsFound_UInt64 >= TheoremProto_0004.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0004, Axiom);

                Auto
                [TheoremProto_0005.LHSPrimaryKey_UInt64 == TheoremProto_0005.RHSPrimaryKey_UInt64]
                [TheoremProto_0005.TotalProofsFound_UInt64 >= TheoremProto_0005.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0005, Axiom);

                Auto
                [TheoremProto_0005.LHSPrimaryKey_UInt64 == TheoremProto_0005.RHSPrimaryKey_UInt64]
                [TheoremProto_0005.TotalProofsFound_UInt64 >= TheoremProto_0005.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0005, Axiom);

                limiter.release();
            }

        });

    std::for_each(std::execution::par_unseq,
        Axioms_Vec.begin(),
        Axioms_Vec.end(),
        [&](const Axiom_Struct& Axiom)
        {
            RecursionLimiter::Invoke limiter(12);
            if (limiter.acquired())
            {
                Auto
                [TheoremProto_0000.LHSPrimaryKey_UInt64 == TheoremProto_0000.RHSPrimaryKey_UInt64]
                [TheoremProto_0000.TotalProofsFound_UInt64 >= TheoremProto_0000.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0000, Axiom);

                Auto
                [TheoremProto_0000.LHSPrimaryKey_UInt64 == TheoremProto_0000.RHSPrimaryKey_UInt64]
                [TheoremProto_0000.TotalProofsFound_UInt64 >= TheoremProto_0000.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0000, Axiom);

                Auto
                [TheoremProto_0001.LHSPrimaryKey_UInt64 == TheoremProto_0001.RHSPrimaryKey_UInt64]
                [TheoremProto_0001.TotalProofsFound_UInt64 >= TheoremProto_0001.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0001, Axiom);

                Auto
                [TheoremProto_0001.LHSPrimaryKey_UInt64 == TheoremProto_0001.RHSPrimaryKey_UInt64]
                [TheoremProto_0001.TotalProofsFound_UInt64 >= TheoremProto_0001.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0001, Axiom);

                Auto
                [TheoremProto_0002.LHSPrimaryKey_UInt64 == TheoremProto_0002.RHSPrimaryKey_UInt64]
                [TheoremProto_0002.TotalProofsFound_UInt64 >= TheoremProto_0002.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0002, Axiom);

                Auto
                [TheoremProto_0002.LHSPrimaryKey_UInt64 == TheoremProto_0002.RHSPrimaryKey_UInt64]
                [TheoremProto_0002.TotalProofsFound_UInt64 >= TheoremProto_0002.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0002, Axiom);


                Auto
                [TheoremProto_0003.LHSPrimaryKey_UInt64 == TheoremProto_0003.RHSPrimaryKey_UInt64]
                [TheoremProto_0003.TotalProofsFound_UInt64 >= TheoremProto_0003.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0003, Axiom);

                Auto
                [TheoremProto_0003.LHSPrimaryKey_UInt64 == TheoremProto_0003.RHSPrimaryKey_UInt64]
                [TheoremProto_0003.TotalProofsFound_UInt64 >= TheoremProto_0003.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0003, Axiom);

                Auto
                [TheoremProto_0004.LHSPrimaryKey_UInt64 == TheoremProto_0004.RHSPrimaryKey_UInt64]
                [TheoremProto_0004.TotalProofsFound_UInt64 >= TheoremProto_0004.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0004, Axiom);

                Auto
                [TheoremProto_0004.LHSPrimaryKey_UInt64 == TheoremProto_0004.RHSPrimaryKey_UInt64]
                [TheoremProto_0004.TotalProofsFound_UInt64 >= TheoremProto_0004.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0004, Axiom);

                Auto
                [TheoremProto_0005.LHSPrimaryKey_UInt64 == TheoremProto_0005.RHSPrimaryKey_UInt64]
                [TheoremProto_0005.TotalProofsFound_UInt64 >= TheoremProto_0005.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0005, Axiom);

                Auto
                [TheoremProto_0005.LHSPrimaryKey_UInt64 == TheoremProto_0005.RHSPrimaryKey_UInt64]
                [TheoremProto_0005.TotalProofsFound_UInt64 >= TheoremProto_0005.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0005, Axiom);

                limiter.release();
            }

        });

};

Auto
[true]
[true]
[RouteSource_EnumClass::_rhs]
[Indirection_EnumClass::_auto] =
[](Theorem_Struct InTheorem, const Axiom_Struct& InAxiom) -> void
{
    InTheorem.ProofStack_VecUInt64.push_back(InAxiom);

    if (InTheorem.LHSPrimaryKey_UInt64 == InTheorem.RHSPrimaryKey_UInt64)
    {
        InTheorem.ProofFound_Flag = true;
        ++InTheorem.TotalProofsFound_UInt64;
    }

    if (InTheorem.TotalProofsFound_UInt64 >= InTheorem.MaxAllowedProofs_UInt64)
        return;

    Theorem_Struct TheoremProto_0000 = InTheorem;
    Theorem_Struct TheoremProto_0001 = InTheorem;
    Theorem_Struct TheoremProto_0002 = InTheorem;
    Theorem_Struct TheoremProto_0003 = InTheorem;
    Theorem_Struct TheoremProto_0004 = InTheorem;
    Theorem_Struct TheoremProto_0005 = InTheorem;

    if (TheoremProto_0000.SubnetFound_LHS(InAxiom.LHSPrimaryKey_UInt64))
        TheoremProto_0000.UpdatePrimaryKey_LHS(InAxiom.LHSPrimaryKey_UInt64);

    TheoremProto_0001.UpdatePrimaryKey_RHS(InAxiom.LHSPrimaryKey_UInt64);
    TheoremProto_0002.UpdatePrimaryKey_LHS(InAxiom.LHSPrimaryKey_UInt64);
    TheoremProto_0002.UpdatePrimaryKey_RHS(InAxiom.RHSPrimaryKey_UInt64);

    TheoremProto_0003.UpdatePrimaryKey_LHS(InAxiom.RHSPrimaryKey_UInt64);
    TheoremProto_0004.UpdatePrimaryKey_RHS(InAxiom.RHSPrimaryKey_UInt64);
    TheoremProto_0005.UpdatePrimaryKey_LHS(InAxiom.RHSPrimaryKey_UInt64);
    TheoremProto_0005.UpdatePrimaryKey_RHS(InAxiom.LHSPrimaryKey_UInt64);

    std::for_each(std::execution::par_unseq,
        Axioms_Vec.begin(),
        Axioms_Vec.end(),
        [&](const Axiom_Struct& Axiom)
        {
            RecursionLimiter::Invoke limiter(6);
            if (limiter.acquired())
            {
                Auto
                [TheoremProto_0000.LHSPrimaryKey_UInt64 == TheoremProto_0000.RHSPrimaryKey_UInt64]
                [TheoremProto_0000.TotalProofsFound_UInt64 >= TheoremProto_0000.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0000, Axiom);

                Auto
                [TheoremProto_0000.LHSPrimaryKey_UInt64 == TheoremProto_0000.RHSPrimaryKey_UInt64]
                [TheoremProto_0000.TotalProofsFound_UInt64 >= TheoremProto_0000.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0000, Axiom);

                Auto
                [TheoremProto_0001.LHSPrimaryKey_UInt64 == TheoremProto_0001.RHSPrimaryKey_UInt64]
                [TheoremProto_0001.TotalProofsFound_UInt64 >= TheoremProto_0001.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0001, Axiom);

                Auto
                [TheoremProto_0001.LHSPrimaryKey_UInt64 == TheoremProto_0001.RHSPrimaryKey_UInt64]
                [TheoremProto_0001.TotalProofsFound_UInt64 >= TheoremProto_0001.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0001, Axiom);

                Auto
                [TheoremProto_0002.LHSPrimaryKey_UInt64 == TheoremProto_0002.RHSPrimaryKey_UInt64]
                [TheoremProto_0002.TotalProofsFound_UInt64 >= TheoremProto_0002.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0002, Axiom);

                Auto
                [TheoremProto_0002.LHSPrimaryKey_UInt64 == TheoremProto_0002.RHSPrimaryKey_UInt64]
                [TheoremProto_0002.TotalProofsFound_UInt64 >= TheoremProto_0002.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0002, Axiom);

                limiter.release();
            }

        });

    std::for_each(std::execution::par_unseq,
        Axioms_Vec.begin(),
        Axioms_Vec.end(),
        [&](const Axiom_Struct& Axiom)
        {
            RecursionLimiter::Invoke limiter(6);
            if (limiter.acquired())
            {
                Auto
                [TheoremProto_0003.LHSPrimaryKey_UInt64 == TheoremProto_0003.RHSPrimaryKey_UInt64]
                [TheoremProto_0003.TotalProofsFound_UInt64 >= TheoremProto_0003.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0003, Axiom);

                Auto
                [TheoremProto_0003.LHSPrimaryKey_UInt64 == TheoremProto_0003.RHSPrimaryKey_UInt64]
                [TheoremProto_0003.TotalProofsFound_UInt64 >= TheoremProto_0003.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0003, Axiom);

                Auto
                [TheoremProto_0004.LHSPrimaryKey_UInt64 == TheoremProto_0004.RHSPrimaryKey_UInt64]
                [TheoremProto_0004.TotalProofsFound_UInt64 >= TheoremProto_0004.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0004, Axiom);

                Auto
                [TheoremProto_0004.LHSPrimaryKey_UInt64 == TheoremProto_0004.RHSPrimaryKey_UInt64]
                [TheoremProto_0004.TotalProofsFound_UInt64 >= TheoremProto_0004.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0004, Axiom);

                Auto
                [TheoremProto_0005.LHSPrimaryKey_UInt64 == TheoremProto_0005.RHSPrimaryKey_UInt64]
                [TheoremProto_0005.TotalProofsFound_UInt64 >= TheoremProto_0005.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0005, Axiom);

                Auto
                [TheoremProto_0005.LHSPrimaryKey_UInt64 == TheoremProto_0005.RHSPrimaryKey_UInt64]
                [TheoremProto_0005.TotalProofsFound_UInt64 >= TheoremProto_0005.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0005, Axiom);

                limiter.release();
            }

        });

    std::for_each(std::execution::par_unseq,
        Axioms_Vec.begin(),
        Axioms_Vec.end(),
        [&](const Axiom_Struct& Axiom)
        {
            RecursionLimiter::Invoke limiter(12);
            if (limiter.acquired())
            {
                Auto
                [TheoremProto_0000.LHSPrimaryKey_UInt64 == TheoremProto_0000.RHSPrimaryKey_UInt64]
                [TheoremProto_0000.TotalProofsFound_UInt64 >= TheoremProto_0000.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0000, Axiom);

                Auto
                [TheoremProto_0000.LHSPrimaryKey_UInt64 == TheoremProto_0000.RHSPrimaryKey_UInt64]
                [TheoremProto_0000.TotalProofsFound_UInt64 >= TheoremProto_0000.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0000, Axiom);

                Auto
                [TheoremProto_0001.LHSPrimaryKey_UInt64 == TheoremProto_0001.RHSPrimaryKey_UInt64]
                [TheoremProto_0001.TotalProofsFound_UInt64 >= TheoremProto_0001.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0001, Axiom);

                Auto
                [TheoremProto_0001.LHSPrimaryKey_UInt64 == TheoremProto_0001.RHSPrimaryKey_UInt64]
                [TheoremProto_0001.TotalProofsFound_UInt64 >= TheoremProto_0001.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0001, Axiom);

                Auto
                [TheoremProto_0002.LHSPrimaryKey_UInt64 == TheoremProto_0002.RHSPrimaryKey_UInt64]
                [TheoremProto_0002.TotalProofsFound_UInt64 >= TheoremProto_0002.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0002, Axiom);

                Auto
                [TheoremProto_0002.LHSPrimaryKey_UInt64 == TheoremProto_0002.RHSPrimaryKey_UInt64]
                [TheoremProto_0002.TotalProofsFound_UInt64 >= TheoremProto_0002.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0002, Axiom);


                Auto
                [TheoremProto_0003.LHSPrimaryKey_UInt64 == TheoremProto_0003.RHSPrimaryKey_UInt64]
                [TheoremProto_0003.TotalProofsFound_UInt64 >= TheoremProto_0003.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0003, Axiom);

                Auto
                [TheoremProto_0003.LHSPrimaryKey_UInt64 == TheoremProto_0003.RHSPrimaryKey_UInt64]
                [TheoremProto_0003.TotalProofsFound_UInt64 >= TheoremProto_0003.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0003, Axiom);

                Auto
                [TheoremProto_0004.LHSPrimaryKey_UInt64 == TheoremProto_0004.RHSPrimaryKey_UInt64]
                [TheoremProto_0004.TotalProofsFound_UInt64 >= TheoremProto_0004.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0004, Axiom);

                Auto
                [TheoremProto_0004.LHSPrimaryKey_UInt64 == TheoremProto_0004.RHSPrimaryKey_UInt64]
                [TheoremProto_0004.TotalProofsFound_UInt64 >= TheoremProto_0004.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0004, Axiom);

                Auto
                [TheoremProto_0005.LHSPrimaryKey_UInt64 == TheoremProto_0005.RHSPrimaryKey_UInt64]
                [TheoremProto_0005.TotalProofsFound_UInt64 >= TheoremProto_0005.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0005, Axiom);

                Auto
                [TheoremProto_0005.LHSPrimaryKey_UInt64 == TheoremProto_0005.RHSPrimaryKey_UInt64]
                [TheoremProto_0005.TotalProofsFound_UInt64 >= TheoremProto_0005.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0005, Axiom);

                limiter.release();
            }

        });

};

Auto
[true]
[true]
[RouteSource_EnumClass::_rhs]
[Indirection_EnumClass::_reduce] =
[](Theorem_Struct InTheorem, const Axiom_Struct& InAxiom) -> void
{
    InTheorem.ProofStack_VecUInt64.push_back(InAxiom);

    if (InTheorem.LHSPrimaryKey_UInt64 == InTheorem.RHSPrimaryKey_UInt64)
    {
        InTheorem.ProofFound_Flag = true;
        ++InTheorem.TotalProofsFound_UInt64;
    }

    if (InTheorem.TotalProofsFound_UInt64 >= InTheorem.MaxAllowedProofs_UInt64)
        return;

    Theorem_Struct TheoremProto_0000 = InTheorem;
    Theorem_Struct TheoremProto_0001 = InTheorem;
    Theorem_Struct TheoremProto_0002 = InTheorem;
    Theorem_Struct TheoremProto_0003 = InTheorem;
    Theorem_Struct TheoremProto_0004 = InTheorem;
    Theorem_Struct TheoremProto_0005 = InTheorem;

    if (TheoremProto_0000.SubnetFound_LHS(InAxiom.LHSPrimaryKey_UInt64))
        TheoremProto_0000.UpdatePrimaryKey_LHS(InAxiom.LHSPrimaryKey_UInt64);

    TheoremProto_0001.UpdatePrimaryKey_RHS(InAxiom.LHSPrimaryKey_UInt64);
    TheoremProto_0002.UpdatePrimaryKey_LHS(InAxiom.LHSPrimaryKey_UInt64);
    TheoremProto_0002.UpdatePrimaryKey_RHS(InAxiom.RHSPrimaryKey_UInt64);

    TheoremProto_0003.UpdatePrimaryKey_LHS(InAxiom.RHSPrimaryKey_UInt64);
    TheoremProto_0004.UpdatePrimaryKey_RHS(InAxiom.RHSPrimaryKey_UInt64);
    TheoremProto_0005.UpdatePrimaryKey_LHS(InAxiom.RHSPrimaryKey_UInt64);
    TheoremProto_0005.UpdatePrimaryKey_RHS(InAxiom.LHSPrimaryKey_UInt64);

    std::for_each(std::execution::par_unseq,
        Axioms_Vec.begin(),
        Axioms_Vec.end(),
        [&](const Axiom_Struct& Axiom)
        {
            RecursionLimiter::Invoke limiter(6);
            if (limiter.acquired())
            {
                Auto
                [TheoremProto_0000.LHSPrimaryKey_UInt64 == TheoremProto_0000.RHSPrimaryKey_UInt64]
                [TheoremProto_0000.TotalProofsFound_UInt64 >= TheoremProto_0000.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0000, Axiom);

                Auto
                [TheoremProto_0000.LHSPrimaryKey_UInt64 == TheoremProto_0000.RHSPrimaryKey_UInt64]
                [TheoremProto_0000.TotalProofsFound_UInt64 >= TheoremProto_0000.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0000, Axiom);

                Auto
                [TheoremProto_0001.LHSPrimaryKey_UInt64 == TheoremProto_0001.RHSPrimaryKey_UInt64]
                [TheoremProto_0001.TotalProofsFound_UInt64 >= TheoremProto_0001.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0001, Axiom);

                Auto
                [TheoremProto_0001.LHSPrimaryKey_UInt64 == TheoremProto_0001.RHSPrimaryKey_UInt64]
                [TheoremProto_0001.TotalProofsFound_UInt64 >= TheoremProto_0001.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0001, Axiom);

                Auto
                [TheoremProto_0002.LHSPrimaryKey_UInt64 == TheoremProto_0002.RHSPrimaryKey_UInt64]
                [TheoremProto_0002.TotalProofsFound_UInt64 >= TheoremProto_0002.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0002, Axiom);

                Auto
                [TheoremProto_0002.LHSPrimaryKey_UInt64 == TheoremProto_0002.RHSPrimaryKey_UInt64]
                [TheoremProto_0002.TotalProofsFound_UInt64 >= TheoremProto_0002.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0002, Axiom);

                limiter.release();
            }

        });

    std::for_each(std::execution::par_unseq,
        Axioms_Vec.begin(),
        Axioms_Vec.end(),
        [&](const Axiom_Struct& Axiom)
        {
            RecursionLimiter::Invoke limiter(6);
            if (limiter.acquired())
            {
                Auto
                [TheoremProto_0003.LHSPrimaryKey_UInt64 == TheoremProto_0003.RHSPrimaryKey_UInt64]
                [TheoremProto_0003.TotalProofsFound_UInt64 >= TheoremProto_0003.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0003, Axiom);

                Auto
                [TheoremProto_0003.LHSPrimaryKey_UInt64 == TheoremProto_0003.RHSPrimaryKey_UInt64]
                [TheoremProto_0003.TotalProofsFound_UInt64 >= TheoremProto_0003.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0003, Axiom);

                Auto
                [TheoremProto_0004.LHSPrimaryKey_UInt64 == TheoremProto_0004.RHSPrimaryKey_UInt64]
                [TheoremProto_0004.TotalProofsFound_UInt64 >= TheoremProto_0004.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0004, Axiom);

                Auto
                [TheoremProto_0004.LHSPrimaryKey_UInt64 == TheoremProto_0004.RHSPrimaryKey_UInt64]
                [TheoremProto_0004.TotalProofsFound_UInt64 >= TheoremProto_0004.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0004, Axiom);

                Auto
                [TheoremProto_0005.LHSPrimaryKey_UInt64 == TheoremProto_0005.RHSPrimaryKey_UInt64]
                [TheoremProto_0005.TotalProofsFound_UInt64 >= TheoremProto_0005.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0005, Axiom);

                Auto
                [TheoremProto_0005.LHSPrimaryKey_UInt64 == TheoremProto_0005.RHSPrimaryKey_UInt64]
                [TheoremProto_0005.TotalProofsFound_UInt64 >= TheoremProto_0005.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0005, Axiom);

                limiter.release();
            }

        });

    std::for_each(std::execution::par_unseq,
        Axioms_Vec.begin(),
        Axioms_Vec.end(),
        [&](const Axiom_Struct& Axiom)
        {
            RecursionLimiter::Invoke limiter(12);
            if (limiter.acquired())
            {
                Auto
                [TheoremProto_0000.LHSPrimaryKey_UInt64 == TheoremProto_0000.RHSPrimaryKey_UInt64]
                [TheoremProto_0000.TotalProofsFound_UInt64 >= TheoremProto_0000.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0000, Axiom);

                Auto
                [TheoremProto_0000.LHSPrimaryKey_UInt64 == TheoremProto_0000.RHSPrimaryKey_UInt64]
                [TheoremProto_0000.TotalProofsFound_UInt64 >= TheoremProto_0000.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0000, Axiom);

                Auto
                [TheoremProto_0001.LHSPrimaryKey_UInt64 == TheoremProto_0001.RHSPrimaryKey_UInt64]
                [TheoremProto_0001.TotalProofsFound_UInt64 >= TheoremProto_0001.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0001, Axiom);

                Auto
                [TheoremProto_0001.LHSPrimaryKey_UInt64 == TheoremProto_0001.RHSPrimaryKey_UInt64]
                [TheoremProto_0001.TotalProofsFound_UInt64 >= TheoremProto_0001.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0001, Axiom);

                Auto
                [TheoremProto_0002.LHSPrimaryKey_UInt64 == TheoremProto_0002.RHSPrimaryKey_UInt64]
                [TheoremProto_0002.TotalProofsFound_UInt64 >= TheoremProto_0002.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0002, Axiom);

                Auto
                [TheoremProto_0002.LHSPrimaryKey_UInt64 == TheoremProto_0002.RHSPrimaryKey_UInt64]
                [TheoremProto_0002.TotalProofsFound_UInt64 >= TheoremProto_0002.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0002, Axiom);


                Auto
                [TheoremProto_0003.LHSPrimaryKey_UInt64 == TheoremProto_0003.RHSPrimaryKey_UInt64]
                [TheoremProto_0003.TotalProofsFound_UInt64 >= TheoremProto_0003.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0003, Axiom);

                Auto
                [TheoremProto_0003.LHSPrimaryKey_UInt64 == TheoremProto_0003.RHSPrimaryKey_UInt64]
                [TheoremProto_0003.TotalProofsFound_UInt64 >= TheoremProto_0003.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0003, Axiom);

                Auto
                [TheoremProto_0004.LHSPrimaryKey_UInt64 == TheoremProto_0004.RHSPrimaryKey_UInt64]
                [TheoremProto_0004.TotalProofsFound_UInt64 >= TheoremProto_0004.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0004, Axiom);

                Auto
                [TheoremProto_0004.LHSPrimaryKey_UInt64 == TheoremProto_0004.RHSPrimaryKey_UInt64]
                [TheoremProto_0004.TotalProofsFound_UInt64 >= TheoremProto_0004.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0004, Axiom);

                Auto
                [TheoremProto_0005.LHSPrimaryKey_UInt64 == TheoremProto_0005.RHSPrimaryKey_UInt64]
                [TheoremProto_0005.TotalProofsFound_UInt64 >= TheoremProto_0005.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0005, Axiom);

                Auto
                [TheoremProto_0005.LHSPrimaryKey_UInt64 == TheoremProto_0005.RHSPrimaryKey_UInt64]
                [TheoremProto_0005.TotalProofsFound_UInt64 >= TheoremProto_0005.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0005, Axiom);

                limiter.release();
            }

        });

};

Auto
[true]
[true]
[RouteSource_EnumClass::_rhs]
[Indirection_EnumClass::_expand] =
[](Theorem_Struct InTheorem, const Axiom_Struct& InAxiom) -> void
{
    InTheorem.ProofStack_VecUInt64.push_back(InAxiom);

    if (InTheorem.LHSPrimaryKey_UInt64 == InTheorem.RHSPrimaryKey_UInt64)
    {
        InTheorem.ProofFound_Flag = true;
        ++InTheorem.TotalProofsFound_UInt64;
    }

    if (InTheorem.TotalProofsFound_UInt64 >= InTheorem.MaxAllowedProofs_UInt64)
        return;

    Theorem_Struct TheoremProto_0000 = InTheorem;
    Theorem_Struct TheoremProto_0001 = InTheorem;
    Theorem_Struct TheoremProto_0002 = InTheorem;
    Theorem_Struct TheoremProto_0003 = InTheorem;
    Theorem_Struct TheoremProto_0004 = InTheorem;
    Theorem_Struct TheoremProto_0005 = InTheorem;

    if (TheoremProto_0000.SubnetFound_LHS(InAxiom.LHSPrimaryKey_UInt64))
        TheoremProto_0000.UpdatePrimaryKey_LHS(InAxiom.LHSPrimaryKey_UInt64);

    TheoremProto_0001.UpdatePrimaryKey_RHS(InAxiom.LHSPrimaryKey_UInt64);
    TheoremProto_0002.UpdatePrimaryKey_LHS(InAxiom.LHSPrimaryKey_UInt64);
    TheoremProto_0002.UpdatePrimaryKey_RHS(InAxiom.RHSPrimaryKey_UInt64);

    TheoremProto_0003.UpdatePrimaryKey_LHS(InAxiom.RHSPrimaryKey_UInt64);
    TheoremProto_0004.UpdatePrimaryKey_RHS(InAxiom.RHSPrimaryKey_UInt64);
    TheoremProto_0005.UpdatePrimaryKey_LHS(InAxiom.RHSPrimaryKey_UInt64);
    TheoremProto_0005.UpdatePrimaryKey_RHS(InAxiom.LHSPrimaryKey_UInt64);

    std::for_each(std::execution::par_unseq,
        Axioms_Vec.begin(),
        Axioms_Vec.end(),
        [&](const Axiom_Struct& Axiom)
        {
            RecursionLimiter::Invoke limiter(6);
            if (limiter.acquired())
            {
                Auto
                [TheoremProto_0000.LHSPrimaryKey_UInt64 == TheoremProto_0000.RHSPrimaryKey_UInt64]
                [TheoremProto_0000.TotalProofsFound_UInt64 >= TheoremProto_0000.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0000, Axiom);

                Auto
                [TheoremProto_0000.LHSPrimaryKey_UInt64 == TheoremProto_0000.RHSPrimaryKey_UInt64]
                [TheoremProto_0000.TotalProofsFound_UInt64 >= TheoremProto_0000.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0000, Axiom);

                Auto
                [TheoremProto_0001.LHSPrimaryKey_UInt64 == TheoremProto_0001.RHSPrimaryKey_UInt64]
                [TheoremProto_0001.TotalProofsFound_UInt64 >= TheoremProto_0001.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0001, Axiom);

                Auto
                [TheoremProto_0001.LHSPrimaryKey_UInt64 == TheoremProto_0001.RHSPrimaryKey_UInt64]
                [TheoremProto_0001.TotalProofsFound_UInt64 >= TheoremProto_0001.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0001, Axiom);

                Auto
                [TheoremProto_0002.LHSPrimaryKey_UInt64 == TheoremProto_0002.RHSPrimaryKey_UInt64]
                [TheoremProto_0002.TotalProofsFound_UInt64 >= TheoremProto_0002.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0002, Axiom);

                Auto
                [TheoremProto_0002.LHSPrimaryKey_UInt64 == TheoremProto_0002.RHSPrimaryKey_UInt64]
                [TheoremProto_0002.TotalProofsFound_UInt64 >= TheoremProto_0002.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0002, Axiom);

                limiter.release();
            }

        });

    std::for_each(std::execution::par_unseq,
        Axioms_Vec.begin(),
        Axioms_Vec.end(),
        [&](const Axiom_Struct& Axiom)
        {
            RecursionLimiter::Invoke limiter(6);
            if (limiter.acquired())
            {
                Auto
                [TheoremProto_0003.LHSPrimaryKey_UInt64 == TheoremProto_0003.RHSPrimaryKey_UInt64]
                [TheoremProto_0003.TotalProofsFound_UInt64 >= TheoremProto_0003.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0003, Axiom);

                Auto
                [TheoremProto_0003.LHSPrimaryKey_UInt64 == TheoremProto_0003.RHSPrimaryKey_UInt64]
                [TheoremProto_0003.TotalProofsFound_UInt64 >= TheoremProto_0003.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0003, Axiom);

                Auto
                [TheoremProto_0004.LHSPrimaryKey_UInt64 == TheoremProto_0004.RHSPrimaryKey_UInt64]
                [TheoremProto_0004.TotalProofsFound_UInt64 >= TheoremProto_0004.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0004, Axiom);

                Auto
                [TheoremProto_0004.LHSPrimaryKey_UInt64 == TheoremProto_0004.RHSPrimaryKey_UInt64]
                [TheoremProto_0004.TotalProofsFound_UInt64 >= TheoremProto_0004.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0004, Axiom);

                Auto
                [TheoremProto_0005.LHSPrimaryKey_UInt64 == TheoremProto_0005.RHSPrimaryKey_UInt64]
                [TheoremProto_0005.TotalProofsFound_UInt64 >= TheoremProto_0005.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0005, Axiom);

                Auto
                [TheoremProto_0005.LHSPrimaryKey_UInt64 == TheoremProto_0005.RHSPrimaryKey_UInt64]
                [TheoremProto_0005.TotalProofsFound_UInt64 >= TheoremProto_0005.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0005, Axiom);

                limiter.release();
            }

        });

    std::for_each(std::execution::par_unseq,
        Axioms_Vec.begin(),
        Axioms_Vec.end(),
        [&](const Axiom_Struct& Axiom)
        {
            RecursionLimiter::Invoke limiter(12);
            if (limiter.acquired())
            {
                Auto
                [TheoremProto_0000.LHSPrimaryKey_UInt64 == TheoremProto_0000.RHSPrimaryKey_UInt64]
                [TheoremProto_0000.TotalProofsFound_UInt64 >= TheoremProto_0000.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0000, Axiom);

                Auto
                [TheoremProto_0000.LHSPrimaryKey_UInt64 == TheoremProto_0000.RHSPrimaryKey_UInt64]
                [TheoremProto_0000.TotalProofsFound_UInt64 >= TheoremProto_0000.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0000, Axiom);

                Auto
                [TheoremProto_0001.LHSPrimaryKey_UInt64 == TheoremProto_0001.RHSPrimaryKey_UInt64]
                [TheoremProto_0001.TotalProofsFound_UInt64 >= TheoremProto_0001.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0001, Axiom);

                Auto
                [TheoremProto_0001.LHSPrimaryKey_UInt64 == TheoremProto_0001.RHSPrimaryKey_UInt64]
                [TheoremProto_0001.TotalProofsFound_UInt64 >= TheoremProto_0001.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0001, Axiom);

                Auto
                [TheoremProto_0002.LHSPrimaryKey_UInt64 == TheoremProto_0002.RHSPrimaryKey_UInt64]
                [TheoremProto_0002.TotalProofsFound_UInt64 >= TheoremProto_0002.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0002, Axiom);

                Auto
                [TheoremProto_0002.LHSPrimaryKey_UInt64 == TheoremProto_0002.RHSPrimaryKey_UInt64]
                [TheoremProto_0002.TotalProofsFound_UInt64 >= TheoremProto_0002.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0002, Axiom);


                Auto
                [TheoremProto_0003.LHSPrimaryKey_UInt64 == TheoremProto_0003.RHSPrimaryKey_UInt64]
                [TheoremProto_0003.TotalProofsFound_UInt64 >= TheoremProto_0003.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0003, Axiom);

                Auto
                [TheoremProto_0003.LHSPrimaryKey_UInt64 == TheoremProto_0003.RHSPrimaryKey_UInt64]
                [TheoremProto_0003.TotalProofsFound_UInt64 >= TheoremProto_0003.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0003, Axiom);

                Auto
                [TheoremProto_0004.LHSPrimaryKey_UInt64 == TheoremProto_0004.RHSPrimaryKey_UInt64]
                [TheoremProto_0004.TotalProofsFound_UInt64 >= TheoremProto_0004.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0004, Axiom);

                Auto
                [TheoremProto_0004.LHSPrimaryKey_UInt64 == TheoremProto_0004.RHSPrimaryKey_UInt64]
                [TheoremProto_0004.TotalProofsFound_UInt64 >= TheoremProto_0004.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0004, Axiom);

                Auto
                [TheoremProto_0005.LHSPrimaryKey_UInt64 == TheoremProto_0005.RHSPrimaryKey_UInt64]
                [TheoremProto_0005.TotalProofsFound_UInt64 >= TheoremProto_0005.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_lhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0005, Axiom);

                Auto
                [TheoremProto_0005.LHSPrimaryKey_UInt64 == TheoremProto_0005.RHSPrimaryKey_UInt64]
                [TheoremProto_0005.TotalProofsFound_UInt64 >= TheoremProto_0005.MaxAllowedProofs_UInt64]
                [RouteSource_EnumClass::_rhs]
                [Indirection_EnumClass::_reduce]
                (TheoremProto_0005, Axiom);

                limiter.release();
            }

        });

};

std::ostream& operator<< (std::ostream& os, const RouteSource_EnumClass& route)
{
    switch (route)
    {
    case RouteSource_EnumClass::_lhs:
        os << "RouteSource_EnumClass::_lhs";
        break;
    case RouteSource_EnumClass::_rhs:
        os << "RouteSource_EnumClass::_rhs";
        break;
    default:
        os.setstate(std::ios_base::failbit);
        break;
    }
    return os;
};

int main()
{
    const auto start_time_chrono = std::chrono::high_resolution_clock::now();

    /*
    token: [ "1" "2" "4" "+" ]
    prime: [  2   3   5   7 ]
    */

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

    uint64_t GUID = 0;

    const uint64_t N = 2; // Update as needed;

    std::array < Axiom_Struct, N > Axioms_Vec;

    RecursionLimiter::set_recursion_limit(32'768); // 15-bits on x86i64;

    Theorem_Struct Theorem;

    // Compile
    auto processAxioms = [&GUID, &Axioms_UInt64Vec, &Theorem, &Axioms_Vec]() noexcept -> void
    {
        for (const std::array<uint64_t, 2>&Axiom_i : Axioms_UInt64Vec)
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
                Theorem.guid = GUID++;
                Theorem.LHSPrimaryKey_UInt64 = lhs;
                Theorem.RHSPrimaryKey_UInt64 = rhs;
                continue;
            }

            Axiom_Struct Axiom;
            Axiom.guid = GUID++;
            Axiom.LHSPrimaryKey_UInt64 = lhs;
            Axiom.RHSPrimaryKey_UInt64 = rhs;

            /*
            Authorize qualifying axiom subnets by adding
            their netlists to the outbound route map
            */

            if (Theorem.SubnetFound_LHS(lhs))
            {
                Axiom.RHSCallGraph_UInt64Map[RouteSource_EnumClass::_lhs][Theorem.guid] = true;
            }

            if (Theorem.SubnetFound_RHS(lhs))
            {
                Axiom.RHSCallGraph_UInt64Map[RouteSource_EnumClass::_rhs][Theorem.guid] = true;
            }

            if (Theorem.SubnetFound_LHS(rhs))
            {
                Axiom.LHSCallGraph_UInt64Map[RouteSource_EnumClass::_lhs][Theorem.guid] = true;
            }

            if (Theorem.SubnetFound_RHS(rhs))
            {
                Axiom.LHSCallGraph_UInt64Map[RouteSource_EnumClass::_rhs][Theorem.guid] = true;
            }

            Axioms_Vec[Axiom.guid - 1] = Axiom;
        }

        for (const Axiom_Struct& Axiom_i : Axioms_Vec)
        {
            for (Axiom_Struct& Axiom_j : Axioms_Vec)
            {
                /*
                Authorize qualifying axiom subnets by adding
                their netlists to the outbound route map
                */
                const bool ijAvoidsACallLoop_Flag = (Axiom_i.guid != Axiom_j.guid); // Avoid Call loops
                if (ijAvoidsACallLoop_Flag)
                {
                if (Axiom_i.SubnetFound_LHS(Axiom_j.LHSPrimaryKey_UInt64))
                {
                    Axiom_j.RHSCallGraph_UInt64Map[RouteSource_EnumClass::_lhs][Axiom_i.guid] = true;
                }

                if (Axiom_i.SubnetFound_LHS(Axiom_j.RHSPrimaryKey_UInt64))
                {
                    Axiom_j.LHSCallGraph_UInt64Map[RouteSource_EnumClass::_lhs][Axiom_i.guid] = true;
                }

                if (Axiom_i.SubnetFound_RHS(Axiom_j.LHSPrimaryKey_UInt64))
                {
                    Axiom_j.RHSCallGraph_UInt64Map[RouteSource_EnumClass::_rhs][Axiom_i.guid] = true;
                }

                if (Axiom_i.SubnetFound_RHS(Axiom_j.RHSPrimaryKey_UInt64))
                {
                    Axiom_j.LHSCallGraph_UInt64Map[RouteSource_EnumClass::_rhs][Axiom_i.guid] = true;
                }
                }
            }
        }
    };

    std::jthread th(processAxioms);
    th.join();

    const auto end_time_chrono = std::chrono::high_resolution_clock::now();
    const auto duration_chrono = std::chrono::duration_cast<std::chrono::nanoseconds>(end_time_chrono - start_time_chrono).count();
    std::cout << "Total Duration (nanoseconds): " << duration_chrono << std::endl;
    /*
    // Iterate and print the contents of the map
    for (const Axiom_Struct& Axiom : Axioms_Vec)
    {
        for (const auto& outer_pair : Axiom.LHSCallGraph_UInt64Map) {
            const RouteSource_EnumClass& outer_key = outer_pair.first;
            const std::unordered_map<uint64_t, bool>& inner_map = outer_pair.second;

            for (const auto& inner_pair : inner_map) {
                const uint64_t inner_key = inner_pair.first;
                const bool value = inner_pair.second;

                std::cout << "Axiom_" << Axiom.guid << ".LHSCallGraph_UInt64Map[" << outer_key << "][" << inner_key << "] = " << std::boolalpha << value << '\n';
            }
        }
    }
    */
    return 0;
}
