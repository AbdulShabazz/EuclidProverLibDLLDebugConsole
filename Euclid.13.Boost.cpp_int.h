#pragma once

#include <iostream>
#include <vector>
#include <string>

#include <queue>
#include <chrono>
#include <unordered_map>
#include <mutex>
#include <thread>
#include <boost/multiprecision/cpp_int.hpp>

namespace Euclid_Prover {

    using BigInt512_t = boost::multiprecision::cpp_int;

    //#define IOSTREAM_INCLUDED // Comment out to disable all std::cout messages. //

#ifdef IOSTREAM_INCLUDED
    std::vector<std::string> TraceCallStackStdStrVec{ "EuclidProver" };
#endif

    void __stdlog__(const std::initializer_list<std::string>& msg, const bool AddNewlineFlag = true)
    {
        // Check if the iostream library is included.
#ifdef IOSTREAM_INCLUDED
        auto it = msg.begin();
        auto IT = msg.end();
        std::cout << *it;
        ++it; // Advance the iterator by 1 position //
        for (it; it != IT; ++it)
        {
            std::cout << *it;
        }
        if (AddNewlineFlag)
            std::cout << std::endl;
#endif
    };

    void __stdtracein__(const std::string& msg)
    {
        // Check if the iostream library is included.
#ifdef IOSTREAM_INCLUDED
        TraceCallStackStdStrVec.emplace_back(msg);
        const BigInt512_t I = TraceCallStackStdStrVec.size();
        std::cout << TraceCallStackStdStrVec[0];
        for (BigInt512_t i = 1; i < I; ++i)
        {
            std::cout << " > " << TraceCallStackStdStrVec[std::size_t{ i }];
        }
        std::cout << std::endl;
#endif
    };

    void __stdtraceout__(const std::string& msg)
    {
        // Check if the iostream library is included.
#ifdef IOSTREAM_INCLUDED
        TraceCallStackStdStrVec.pop_back();
        const BigInt512_t I = TraceCallStackStdStrVec.size();
        std::string buff{ TraceCallStackStdStrVec[0] };
        for (BigInt512_t i = 1; i < I; ++i)
        {
            buff.append(" > " + TraceCallStackStdStrVec[std::size_t{ i }]);
        }
        std::cout << buff << " < " << msg << std::endl;
        std::cout << buff << std::endl;
#endif
    };

    /**
        AUTHOR:
            Seagat2011 (https://github.com/Seagat2011 )

        TITLE:
            EuclidProver.h

        DESCRIPTION:
            Term rewrite engine.

        TEST CASE 246:
            nanoseconds elapsed: +5 min

        REFERENCES
            OpenAI GPT-4-32k-0314 ( { max_tokens:32000, temperature:1.0, top_p:1.0, N:1,
                stream:false, logprobs:NULL, echo:false, stop:NULL, presence_penalty:0,
                frequency_penalty:0, best_of:1, logit_bias:NULL } )

        COMPATIBILITY
            Windows 11+ x86i64
    */

    using BigInt512_t = boost::multiprecision::cpp_int;

    bool SubnetFound
    (
        const std::vector<std::string>& Theorem_Src,
        const std::vector<std::string>& Axiom_Src,
        const std::vector<std::string>& Axiom_Dest,
        std::vector<std::string>& Theorem_Dest
    )
    {
        __stdtracein__("SubnetFound");
        const BigInt512_t& th_size = Theorem_Src.size();
        const BigInt512_t& ax_size = Axiom_Src.size();

        bool SubnetFoundFlag{};

        if (ax_size <= th_size)
        {
            BigInt512_t i_ax{};

            for (const std::string& th_tok : Theorem_Src)
            {
                if (Axiom_Src[std::size_t{ i_ax }] == th_tok && !SubnetFoundFlag) {
                    ++i_ax;
                    const bool LocalSubnetFoundFlag = ( i_ax == ax_size );
                    if (LocalSubnetFoundFlag)
                    {
                        for (const std::string ax_tok : Axiom_Dest) {
                            Theorem_Dest.emplace_back(ax_tok);
                        }
                        SubnetFoundFlag = true;
                        i_ax = 0;
                        continue;
                    }
                } else {
                    i_ax = 0;
                    Theorem_Dest.emplace_back(th_tok);
                }
            }
        }
        __stdtraceout__("SubnetFound");
        return SubnetFoundFlag;
    };

    auto Prove = [] () -> void
    {
        __stdtracein__("Prove");
        bool QED{};

        constexpr int LHS = 0;
        constexpr int RHS = 1;
        constexpr int opcode_field = 2;
        constexpr int opcode = 0;
        constexpr int axiom_label = 1;
        constexpr int guid_UInt64 = 2;

        const std::string axiom_name = "Axiom_";
        const std::string theorem_name = "Theorem_";

        class OPCODESTRUCT {
        public:
            const std::string lhs_reduce = "lhs_reduce ";
            const std::string lhs_expand = "lhs_expand ";
            const std::string rhs_reduce = "rhs_reduce ";
            const std::string rhs_expand = "rhs_expand ";
        };

        OPCODESTRUCT OpcodeStruct;

        using PROOF_STEP = std::vector<std::vector<std::vector<std::string>>>;

        // input //

        std::vector<std::vector<std::vector<std::string>>> InProofLibrary3DStdStrVec =

        {
            /*
            // {{lhs},{rhs}} //
            {{"1","+","1","+","1","+","1"},{"4"}}, // Theorem_0 //	
            {{"1","+","1"},{"2"}},	// Axiom_1 //	
            {{"2","+","2"},{"4"}},	// Axiom_2 //
            */
            {
     {
         "1", "+", "1", "+", "1", "+", "1", "+", "1", "+", "1", "+", "1", "+", "1", "+", "1", "+",
         "1", "+", "1", "+", "1", "+", "1", "+", "1", "+", "1", "+", "1", "+", "1", "+", "1", "+",
         "1", "+", "1", "+", "1", "+", "1", "+", "1", "+", "1", "+", "1", "+", "1", "+", "1", "+",
         "1", "+", "1", "+", "1", "+", "1", "+", "1", "+", "1", "+", "1", "+", "1", "+", "1", "+",
         "1", "+", "1", "+", "1", "+", "1", "+", "1", "+", "1", "+", "1", "+", "1", "+", "1", "+",
         "1", "+", "1", "+", "1", "+", "1", "+", "1", "+", "1", "+", "1", "+", "1", "+", "1", "+",
         "1", "+", "1", "+", "1", "+", "1", "+", "1", "+", "1", "+", "1", "+", "1", "+", "1", "+",
         "1", "+", "1", "+", "1", "+", "1", "+", "1", "+", "1", "+", "1", "+", "1", "+", "1", "+",
         "1", "+", "1", "+", "1", "+", "1", "+", "1", "+", "1", "+", "1", "+", "1", "+", "1", "+",
         "1", "+", "1", "+", "1", "+", "1", "+", "1", "+", "1", "+", "1", "+", "1", "+", "1", "+",
         "1", "+", "1", "+", "1", "+", "1", "+", "1", "+", "1", "+", "1", "+", "1", "+", "1", "+",
         "1", "+", "1", "+", "1", "+", "1", "+", "1", "+", "1", "+", "1", "+", "1", "+", "1", "+",
         "1", "+", "1", "+", "1", "+", "1", "+", "1", "+", "1", "+", "1", "+", "1", "+", "1", "+",
         "1", "+", "1", "+", "1", "+", "1", "+", "1", "+", "1", "+", "1", "+", "1", "+", "1", "+",
         "1", "+", "1", "+", "1", "+", "1", "+", "1", "+", "1", "+", "1", "+", "1", "+", "1", "+",
         "1", "+", "1", "+", "1", "+", "1", "+", "1", "+", "1", "+", "1", "+", "1", "+", "1", "+",
         "1", "+", "1", "+", "1", "+", "1", "+", "1", "+", "1", "+", "1", "+", "1", "+", "1", "+",
         "1", "+", "1", "+", "1", "+", "1", "+", "1", "+", "1", "+", "1", "+", "1", "+", "1", "+",
         "1", "+", "1", "+", "1", "+", "1", "+", "1", "+", "1", "+", "1", "+", "1", "+", "1", "+",
         "1", "+", "1", "+", "1", "+", "1", "+", "1", "+", "1", "+", "1", "+", "1", "+", "1", "+",
         "1", "+", "1", "+", "1", "+", "1", "+", "1", "+", "1", "+", "1", "+", "1", "+", "1", "+",
         "1", "+", "1", "+", "1", "+", "1", "+", "1", "+", "1", "+", "1", "+", "1", "+", "1", "+",
         "1", "+", "1", "+", "1", "+", "1", "+", "1", "+", "1", "+", "1", "+", "1", "+", "1", "+",
         "1", "+", "1", "+", "1", "+", "1", "+", "1", "+", "1", "+", "1", "+", "1", "+", "1", "+",
         "1", "+", "1", "+", "1", "+", "1", "+", "1", "+", "1", "+", "1", "+", "1", "+", "1", "+",
         "1", "+", "1", "+", "1", "+", "1", "+", "1", "+", "1", "+", "1", "+", "1", "+", "1", "+",
         "1", "+", "1", "+", "1", "+", "1", "+", "1", "+", "1", "+", "1", "+", "1", "+", "1", "+",
         "1", "+", "1", "+", "1"
     }, // lhs
     {
         "246"
     } // rhs
        },
            { { "1", "+", "1" }, { "2" } },
{ { "1", "+", "2" }, { "3" } },
{ { "2", "+", "2" }, { "4" } },
{ { "1", "+", "4" }, { "5" } },
{ { "3", "+", "3" }, { "6" } },
{ { "1", "+", "6" }, { "7" } },
{ { "4", "+", "4" }, { "8" } },
{ { "1", "+", "8" }, { "9" } },
{ { "5", "+", "5" }, { "10" } },
{ { "1", "+", "10" }, { "11" } },
{ { "6", "+", "6" }, { "12" } },
{ { "1", "+", "12" }, { "13" } },
{ { "7", "+", "7" }, { "14" } },
{ { "1", "+", "14" }, { "15" } },
{ { "8", "+", "8" }, { "16" } },
{ { "1", "+", "16" }, { "17" } },
{ { "9", "+", "9" }, { "18" } },
{ { "1", "+", "18" }, { "19" } },
{ { "10", "+", "10" }, { "20" } },
{ { "1", "+", "20" }, { "21" } },
{ { "11", "+", "11" }, { "22" } },
{ { "1", "+", "22" }, { "23" } },
{ { "12", "+", "12" }, { "24" } },
{ { "1", "+", "24" }, { "25" } },
{ { "13", "+", "13" }, { "26" } },
{ { "1", "+", "26" }, { "27" } },
{ { "14", "+", "14" }, { "28" } },
{ { "1", "+", "28" }, { "29" } },
{ { "15", "+", "15" }, { "30" } },
{ { "1", "+", "30" }, { "31" } },
{ { "16", "+", "16" }, { "32" } },
{ { "1", "+", "32" }, { "33" } },
{ { "17", "+", "17" }, { "34" } },
{ { "1", "+", "34" }, { "35" } },
{ { "18", "+", "18" }, { "36" } },
{ { "1", "+", "36" }, { "37" } },
{ { "19", "+", "19" }, { "38" } },
{ { "1", "+", "38" }, { "39" } },
{ { "20", "+", "20" }, { "40" } },
{ { "1", "+", "40" }, { "41" } },
{ { "21", "+", "21" }, { "42" } },
{ { "1", "+", "42" }, { "43" } },
{ { "22", "+", "22" }, { "44" } },
{ { "1", "+", "44" }, { "45" } },
{ { "23", "+", "23" }, { "46" } },
{ { "1", "+", "46" }, { "47" } },
{ { "24", "+", "24" }, { "48" } },
{ { "1", "+", "48" }, { "49" } },
{ { "25", "+", "25" }, { "50" } },
{ { "1", "+", "50" }, { "51" } },
{ { "26", "+", "26" }, { "52" } },
{ { "1", "+", "52" }, { "53" } },
{ { "27", "+", "27" }, { "54" } },
{ { "1", "+", "54" }, { "55" } },
{ { "28", "+", "28" }, { "56" } },
{ { "1", "+", "56" }, { "57" } },
{ { "29", "+", "29" }, { "58" } },
{ { "1", "+", "58" }, { "59" } },
{ { "30", "+", "30" }, { "60" } },
{ { "1", "+", "60" }, { "61" } },
{ { "31", "+", "31" }, { "62" } },
{ { "1", "+", "62" }, { "63" } },
{ { "32", "+", "32" }, { "64" } },
{ { "1", "+", "64" }, { "65" } },
{ { "33", "+", "33" }, { "66" } },
{ { "1", "+", "66" }, { "67" } },
{ { "34", "+", "34" }, { "68" } },
{ { "1", "+", "68" }, { "69" } },
{ { "35", "+", "35" }, { "70" } },
{ { "1", "+", "70" }, { "71" } },
{ { "36", "+", "36" }, { "72" } },
{ { "1", "+", "72" }, { "73" } },
{ { "37", "+", "37" }, { "74" } },
{ { "1", "+", "74" }, { "75" } },
{ { "38", "+", "38" }, { "76" } },
{ { "1", "+", "76" }, { "77" } },
{ { "39", "+", "39" }, { "78" } },
{ { "1", "+", "78" }, { "79" } },
{ { "40", "+", "40" }, { "80" } },
{ { "1", "+", "80" }, { "81" } },
{ { "41", "+", "41" }, { "82" } },
{ { "1", "+", "82" }, { "83" } },
{ { "42", "+", "42" }, { "84" } },
{ { "1", "+", "84" }, { "85" } },
{ { "43", "+", "43" }, { "86" } },
{ { "1", "+", "86" }, { "87" } },
{ { "44", "+", "44" }, { "88" } },
{ { "1", "+", "88" }, { "89" } },
{ { "45", "+", "45" }, { "90" } },
{ { "1", "+", "90" }, { "91" } },
{ { "46", "+", "46" }, { "92" } },
{ { "1", "+", "92" }, { "93" } },
{ { "47", "+", "47" }, { "94" } },
{ { "1", "+", "94" }, { "95" } },
{ { "48", "+", "48" }, { "96" } },
{ { "1", "+", "96" }, { "97" } },
{ { "49", "+", "49" }, { "98" } },
{ { "1", "+", "98" }, { "99" } },
{ { "50", "+", "50" }, { "100" } },
{ { "1", "+", "100" }, { "101" } },
{ { "51", "+", "51" }, { "102" } },
{ { "1", "+", "102" }, { "103" } },
{ { "52", "+", "52" }, { "104" } },
{ { "1", "+", "104" }, { "105" } },
{ { "53", "+", "53" }, { "106" } },
{ { "1", "+", "106" }, { "107" } },
{ { "54", "+", "54" }, { "108" } },
{ { "1", "+", "108" }, { "109" } },
{ { "55", "+", "55" }, { "110" } },
{ { "1", "+", "110" }, { "111" } },
{ { "56", "+", "56" }, { "112" } },
{ { "1", "+", "112" }, { "113" } },
{ { "57", "+", "57" }, { "114" } },
{ { "1", "+", "114" }, { "115" } },
{ { "58", "+", "58" }, { "116" } },
{ { "1", "+", "116" }, { "117" } },
{ { "59", "+", "59" }, { "118" } },
{ { "1", "+", "118" }, { "119" } },
{ { "60", "+", "60" }, { "120" } },
{ { "1", "+", "120" }, { "121" } },
{ { "61", "+", "61" }, { "122" } },
{ { "1", "+", "122" }, { "123" } },
{ { "62", "+", "62" }, { "124" } },
{ { "1", "+", "124" }, { "125" } },
{ { "63", "+", "63" }, { "126" } },
{ { "1", "+", "126" }, { "127" } },
{ { "64", "+", "64" }, { "128" } },
{ { "1", "+", "128" }, { "129" } },
{ { "65", "+", "65" }, { "130" } },
{ { "1", "+", "130" }, { "131" } },
{ { "66", "+", "66" }, { "132" } },
{ { "1", "+", "132" }, { "133" } },
{ { "67", "+", "67" }, { "134" } },
{ { "1", "+", "134" }, { "135" } },
{ { "68", "+", "68" }, { "136" } },
{ { "1", "+", "136" }, { "137" } },
{ { "69", "+", "69" }, { "138" } },
{ { "1", "+", "138" }, { "139" } },
{ { "70", "+", "70" }, { "140" } },
{ { "1", "+", "140" }, { "141" } },
{ { "71", "+", "71" }, { "142" } },
{ { "1", "+", "142" }, { "143" } },
{ { "72", "+", "72" }, { "144" } },
{ { "1", "+", "144" }, { "145" } },
{ { "73", "+", "73" }, { "146" } },
{ { "1", "+", "146" }, { "147" } },
{ { "74", "+", "74" }, { "148" } },
{ { "1", "+", "148" }, { "149" } },
{ { "75", "+", "75" }, { "150" } },
{ { "1", "+", "150" }, { "151" } },
{ { "76", "+", "76" }, { "152" } },
{ { "1", "+", "152" }, { "153" } },
{ { "77", "+", "77" }, { "154" } },
{ { "1", "+", "154" }, { "155" } },
{ { "78", "+", "78" }, { "156" } },
{ { "1", "+", "156" }, { "157" } },
{ { "79", "+", "79" }, { "158" } },
{ { "1", "+", "158" }, { "159" } },
{ { "80", "+", "80" }, { "160" } },
{ { "1", "+", "160" }, { "161" } },
{ { "81", "+", "81" }, { "162" } },
{ { "1", "+", "162" }, { "163" } },
{ { "82", "+", "82" }, { "164" } },
{ { "1", "+", "164" }, { "165" } },
{ { "83", "+", "83" }, { "166" } },
{ { "1", "+", "166" }, { "167" } },
{ { "84", "+", "84" }, { "168" } },
{ { "1", "+", "168" }, { "169" } },
{ { "85", "+", "85" }, { "170" } },
{ { "1", "+", "170" }, { "171" } },
{ { "86", "+", "86" }, { "172" } },
{ { "1", "+", "172" }, { "173" } },
{ { "87", "+", "87" }, { "174" } },
{ { "1", "+", "174" }, { "175" } },
{ { "88", "+", "88" }, { "176" } },
{ { "1", "+", "176" }, { "177" } },
{ { "89", "+", "89" }, { "178" } },
{ { "1", "+", "178" }, { "179" } },
{ { "90", "+", "90" }, { "180" } },
{ { "1", "+", "180" }, { "181" } },
{ { "91", "+", "91" }, { "182" } },
{ { "1", "+", "182" }, { "183" } },
{ { "92", "+", "92" }, { "184" } },
{ { "1", "+", "184" }, { "185" } },
{ { "93", "+", "93" }, { "186" } },
{ { "1", "+", "186" }, { "187" } },
{ { "94", "+", "94" }, { "188" } },
{ { "1", "+", "188" }, { "189" } },
{ { "95", "+", "95" }, { "190" } },
{ { "1", "+", "190" }, { "191" } },
{ { "96", "+", "96" }, { "192" } },
{ { "1", "+", "192" }, { "193" } },
{ { "97", "+", "97" }, { "194" } },
{ { "1", "+", "194" }, { "195" } },
{ { "98", "+", "98" }, { "196" } },
{ { "1", "+", "196" }, { "197" } },
{ { "99", "+", "99" }, { "198" } },
{ { "1", "+", "198" }, { "199" } },
{ { "100", "+", "100" }, { "200" } },
{ { "1", "+", "200" }, { "201" } },
{ { "101", "+", "101" }, { "202" } },
{ { "1", "+", "202" }, { "203" } },
{ { "102", "+", "102" }, { "204" } },
{ { "1", "+", "204" }, { "205" } },
{ { "103", "+", "103" }, { "206" } },
{ { "1", "+", "206" }, { "207" } },
{ { "104", "+", "104" }, { "208" } },
{ { "1", "+", "208" }, { "209" } },
{ { "105", "+", "105" }, { "210" } },
{ { "1", "+", "210" }, { "211" } },
{ { "106", "+", "106" }, { "212" } },
{ { "1", "+", "212" }, { "213" } },
{ { "107", "+", "107" }, { "214" } },
{ { "1", "+", "214" }, { "215" } },
{ { "108", "+", "108" }, { "216" } },
{ { "1", "+", "216" }, { "217" } },
{ { "109", "+", "109" }, { "218" } },
{ { "1", "+", "218" }, { "219" } },
{ { "110", "+", "110" }, { "220" } },
{ { "1", "+", "220" }, { "221" } },
{ { "111", "+", "111" }, { "222" } },
{ { "1", "+", "222" }, { "223" } },
{ { "112", "+", "112" }, { "224" } },
{ { "1", "+", "224" }, { "225" } },
{ { "113", "+", "113" }, { "226" } },
{ { "1", "+", "226" }, { "227" } },
{ { "114", "+", "114" }, { "228" } },
{ { "1", "+", "228" }, { "229" } },
{ { "115", "+", "115" }, { "230" } },
{ { "1", "+", "230" }, { "231" } },
{ { "116", "+", "116" }, { "232" } },
{ { "1", "+", "232" }, { "233" } },
{ { "117", "+", "117" }, { "234" } },
{ { "1", "+", "234" }, { "235" } },
{ { "118", "+", "118" }, { "236" } },
{ { "1", "+", "236" }, { "237" } },
{ { "119", "+", "119" }, { "238" } },
{ { "1", "+", "238" }, { "239" } },
{ { "120", "+", "120" }, { "240" } },
{ { "1", "+", "240" }, { "241" } },
{ { "121", "+", "121" }, { "242" } },
{ { "1", "+", "242" }, { "243" } },
{ { "122", "+", "122" }, { "244" } },
{ { "1", "+", "244" }, { "245" } },
{ { "123", "+", "123" }, { "246" } }
        };

        PROOF_STEP OutProofStep3DStdStrVec;

        OutProofStep3DStdStrVec.emplace_back(InProofLibrary3DStdStrVec[0]);
        OutProofStep3DStdStrVec[0].push_back({ "root", theorem_name, "0" });

        /*
            // internal representation //
            std::vector<
            std::vector<
            std::vector<std::string>>> OutProofStep3DStdStrVec =
            {
                // {{opcode},{lhs},{rhs}} //
                {{"1","+","1","+","1","+","1"},{"4"},{"root","Theorem_","0"}}
            };
        */

        std::priority_queue<PROOF_STEP> Tasks_Thread;

        Tasks_Thread.push(OutProofStep3DStdStrVec);

        // *** Core Proof Engine (Loop) *** //
        while (!Tasks_Thread.empty() && !QED)
        {
            PROOF_STEP TempProofStep3DStdStrVec{ Tasks_Thread.top() };

            Tasks_Thread.pop();

            const
                std::vector<
                std::vector<std::string>>&Theorem{ TempProofStep3DStdStrVec.back() };

            if (Theorem[LHS] == Theorem[RHS])
            {
                __stdlog__({ " Proof found " });
                QED = true;
            } else {
                const BigInt512_t I = InProofLibrary3DStdStrVec.size();
                for (BigInt512_t i = 1; i < I; ++i)
                {
                    const
                        std::vector<
                        std::vector<std::string>>&Axiom = InProofLibrary3DStdStrVec[std::size_t{ i }];

                    std::vector<
                        std::vector<std::string>>
                        Theorem_0000{ Theorem },
                        Theorem_0001{ Theorem },
                        Theorem_0002{ Theorem },
                        Theorem_0003{ Theorem },
                        Theorem_0004{ Theorem },
                        Theorem_0005{ Theorem },
                        Theorem_0006{ Theorem },
                        Theorem_0007{ Theorem };

                    Theorem_0000[LHS].clear();
                    Theorem_0001[LHS].clear();

                    Theorem_0002[RHS].clear();
                    Theorem_0003[RHS].clear();

                    bool lhs_reduce_flag;
                    bool lhs_expand_flag;
                    bool rhs_reduce_flag;
                    bool rhs_expand_flag;

                    if (lhs_reduce_flag = SubnetFound(Theorem[LHS], Axiom[LHS], Axiom[RHS], Theorem_0000[LHS]))
                    {
                        Theorem_0000[opcode_field][opcode] = OpcodeStruct.lhs_reduce + " via: ";
                        Theorem_0000[opcode_field][axiom_label] = axiom_name;
                        Theorem_0000[opcode_field][guid_UInt64] = i.str();

                        PROOF_STEP TempProofStep3DStdStrVec_0000{ TempProofStep3DStdStrVec };
                        TempProofStep3DStdStrVec_0000.emplace_back(Theorem_0000);

                        Tasks_Thread.push(TempProofStep3DStdStrVec_0000);
                    }
                    /*
                    if (lhs_expand_flag = SubnetFound(Theorem[LHS], Axiom[RHS], Axiom[LHS], Theorem_0001[LHS]))
                    {
                        Theorem_0001[opcode_field][opcode] = OpcodeStruct.lhs_expand + " via: ";
                        Theorem_0001[opcode_field][axiom_label] = axiom_name;
                        Theorem_0001[opcode_field][guid_UInt64] = i.str();

                        PROOF_STEP TempProofStep3DStdStrVec_0001{ TempProofStep3DStdStrVec };
                        TempProofStep3DStdStrVec_0001.emplace_back(Theorem_0001);

                        Tasks_Thread.push(TempProofStep3DStdStrVec_0001);
                    }

                    if (rhs_reduce_flag = SubnetFound(Theorem[RHS], Axiom[LHS], Axiom[RHS], Theorem_0002[RHS]))
                    {
                        Theorem_0002[opcode_field][opcode] = OpcodeStruct.rhs_reduce + " via: ";
                        Theorem_0002[opcode_field][axiom_label] = axiom_name;
                        Theorem_0002[opcode_field][guid_UInt64] = i.str();

                        PROOF_STEP TempProofStep3DStdStrVec_0002{ TempProofStep3DStdStrVec };
                        TempProofStep3DStdStrVec_0002.emplace_back(Theorem_0002);

                        Tasks_Thread.push(TempProofStep3DStdStrVec_0002);
                    }

                    if (rhs_expand_flag = SubnetFound(Theorem[RHS], Axiom[RHS], Axiom[LHS], Theorem_0003[RHS]))
                    {
                        Theorem_0003[opcode_field][opcode] = OpcodeStruct.rhs_expand + " via: ";
                        Theorem_0003[opcode_field][axiom_label] = axiom_name;
                        Theorem_0003[opcode_field][guid_UInt64] = i.str();

                        PROOF_STEP TempProofStep3DStdStrVec_0003{ TempProofStep3DStdStrVec };
                        TempProofStep3DStdStrVec_0003.emplace_back(Theorem_0003);

                        Tasks_Thread.push(TempProofStep3DStdStrVec_0003);
                    }

                    // Advanced Rewrites //

                    if (lhs_reduce_flag && rhs_reduce_flag) 
                    {
                        Theorem_0004[opcode_field][opcode] = OpcodeStruct.lhs_reduce + " + " + OpcodeStruct.rhs_reduce + " via: ";
                        Theorem_0004[opcode_field][axiom_label] = axiom_name;
                        Theorem_0004[opcode_field][guid_UInt64] = i.str();

                        Theorem_0004[LHS] = Theorem_0000[LHS];
                        Theorem_0004[RHS] = Theorem_0002[RHS];

                        PROOF_STEP TempProofStep3DStdStrVec_0004{ TempProofStep3DStdStrVec };
                        TempProofStep3DStdStrVec_0004.emplace_back(Theorem_0004);

                        Tasks_Thread.push(TempProofStep3DStdStrVec_0004);
                    }

                    if (lhs_reduce_flag && rhs_expand_flag)
                    {
                        Theorem_0005[opcode_field][opcode] = OpcodeStruct.lhs_reduce + " + " + OpcodeStruct.rhs_expand + " via: ";
                        Theorem_0005[opcode_field][axiom_label] = axiom_name;
                        Theorem_0005[opcode_field][guid_UInt64] = i.str();

                        Theorem_0005[LHS] = Theorem_0000[LHS];
                        Theorem_0005[RHS] = Theorem_0003[RHS];

                        PROOF_STEP TempProofStep3DStdStrVec_0005{ TempProofStep3DStdStrVec };
                        TempProofStep3DStdStrVec_0005.emplace_back(Theorem_0005);

                        Tasks_Thread.push(TempProofStep3DStdStrVec_0005);
                    }

                    if (lhs_expand_flag && rhs_reduce_flag)
                    {
                        Theorem_0006[opcode_field][opcode] = OpcodeStruct.lhs_expand + " + " + OpcodeStruct.rhs_reduce + " via: ";
                        Theorem_0006[opcode_field][axiom_label] = axiom_name;
                        Theorem_0006[opcode_field][guid_UInt64] = i.str();

                        Theorem_0006[LHS] = Theorem_0001[LHS];
                        Theorem_0006[RHS] = Theorem_0002[RHS];

                        PROOF_STEP TempProofStep3DStdStrVec_0006{ TempProofStep3DStdStrVec };
                        TempProofStep3DStdStrVec_0006.emplace_back(Theorem_0006);

                        Tasks_Thread.push(TempProofStep3DStdStrVec_0006);
                    }

                    if (lhs_expand_flag && rhs_expand_flag)
                    {
                        Theorem_0007[opcode_field][opcode] = OpcodeStruct.lhs_expand + " + " + OpcodeStruct.rhs_expand + " via: ";
                        Theorem_0007[opcode_field][axiom_label] = axiom_name;
                        Theorem_0007[opcode_field][guid_UInt64] = i.str();

                        Theorem_0007[LHS] = Theorem_0001[LHS];
                        Theorem_0007[RHS] = Theorem_0003[RHS];

                        PROOF_STEP TempProofStep3DStdStrVec_0007{ TempProofStep3DStdStrVec };
                        TempProofStep3DStdStrVec_0007.emplace_back(Theorem_0007);

                        Tasks_Thread.push(TempProofStep3DStdStrVec_0007);
                    }
                    */
                } // end for(...InProofLibrary3DStdStrVec)

            } // end if (Theorem[LHS] == Theorem[RHS])

        } // end while  (!Tasks_Thread.empty() && !QED)
        // *** End Core Proof Engine (Loop) *** //

        __stdlog__({ ( QED ? "" : "\n\nQ.E.D\n" ) });
        __stdtraceout__("Prove");
    }; // end Prove(...)

} // end namespace Proof
/*
#include <string>
#include <chrono>
//#include <Euclid.h>

int main()
{
    Euclid_Prover::__stdtracein__("Main");

    const auto start_time_chrono = std::chrono::high_resolution_clock::now();

    Euclid_Prover::Prove();

    std::cout << std::endl;
    const auto end_time_chrono = std::chrono::high_resolution_clock::now();
    const auto duration_chrono = std::chrono::duration_cast<std::chrono::nanoseconds>( end_time_chrono - start_time_chrono ).count();
    std::cout << "Total Duration (nanoseconds): " << duration_chrono << std::endl;

    Euclid_Prover::__stdtraceout__("Main");

    std::string Hold_for_user_input{};
    std::cin >> Hold_for_user_input;

    return EXIT_SUCCESS;
}
*/
