#include "pin.H"
extern "C" {
#include "xed-interface.h"
}
#include <iostream>
#include <iomanip>
#include <fstream>
#include <sys/mman.h>
#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <unistd.h>
#include <malloc.h>
#include <errno.h>
#include <assert.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <fcntl.h>
#include <values.h>
#include <unordered_map>
#include <string>
#include <vector>
#include <algorithm>

using namespace std;

#define MAX_PROBE_JUMP_INSTR_BYTES  14
#define CANDIDATE_COUNT 10
/* ===================================================================== */
/* Commandline Switches */
/* ===================================================================== */
KNOB< BOOL > KnobVerbose(KNOB_MODE_WRITEONCE, "pintool", "verbose", "0", "Verbose run");
KNOB< BOOL > KnobDumpTranslatedCode(KNOB_MODE_WRITEONCE, "pintool", "dump", "0", "Dump Translated Code");
KNOB< BOOL > KnobProf(KNOB_MODE_WRITEONCE, "pintool", "prof", "0", "Run profiling mode");
KNOB< BOOL > KnobInst(KNOB_MODE_WRITEONCE, "pintool", "inst", "0", "Run instrument mode");


/* ===================================================================== */
/* Print Help Message                                                    */
/* ===================================================================== */

INT32 Usage()
{
    std::cerr << "This tool prints information on RTN instruction counts.\n";

    std::cerr << KNOB_BASE::StringKnobSummary();

    std::cerr << std::endl;

    return -1;
}


// Ex 2
struct Loop
{
    ADDRINT _target_addr;
    int32_t _count_seen; // backward edge execution count
    int32_t _count_loop_invoked;
    int32_t _diff_count = -1;
    std::string _routine_name;
    ADDRINT _routine_addr;
    int32_t _old_iter_count;
    int32_t _cur_iter_count;
};

// instruction map with an entry for each new instruction:
typedef struct {
    ADDRINT orig_ins_addr;
    ADDRINT new_ins_addr;
    ADDRINT orig_targ_addr;
    bool hasNewTargAddr;
    char encoded_ins[XED_MAX_INSTRUCTION_BYTES];
    xed_category_enum_t category_enum;
    unsigned int size;
    int new_targ_entry;
} instr_map_t;

/* ===================================================================== */
/* Global Variables */
/* ===================================================================== */
std::ifstream in_file;
std::ofstream out_file;
const char* filename = "loop-count.csv";
std::unordered_map<ADDRINT, uint32_t> routine_map; // values are default initialized to 0
std::unordered_map<ADDRINT, Loop> loops_profiler;
// Ex 3
std::unordered_map<ADDRINT, uint32_t> candidates_map;
std::vector<std::pair<ADDRINT, uint32_t>> candidates;

std::ofstream* out = 0;
// For XED:
#if defined(TARGET_IA32E)
xed_state_t dstate = {XED_MACHINE_MODE_LONG_64, XED_ADDRESS_WIDTH_64b};
#else
xed_state_t dstate = { XED_MACHINE_MODE_LEGACY_32, XED_ADDRESS_WIDTH_32b};
#endif
/* ===================================================================== */
/* From rtn-translation.cpp */
/* ===================================================================== */
//For XED: Pass in the proper length: 15 is the max. But if you do not want to
//cross pages, you can pass less than 15 bytes, of course, the
//instruction might not decode if not enough bytes are provided.
const unsigned int max_inst_len = XED_MAX_INSTRUCTION_BYTES;

ADDRINT lowest_sec_addr = 0;
ADDRINT highest_sec_addr = 0;

// tc containing the new code:
char *tc;
int tc_cursor = 0;
instr_map_t *instr_map = NULL;
int num_of_instr_map_entries = 0;
int max_ins_count = 0;


// total number of routines in the main executable module:
int max_rtn_count = 0;

// Tables of all candidate routines to be translated:
typedef struct {
    ADDRINT rtn_addr;
    USIZE rtn_size;
    int instr_map_entry;   // negative instr_map_entry means routine does not have a translation.
    bool isSafeForReplacedProbe;
} translated_rtn_t;

translated_rtn_t *translated_rtn;
int translated_rtn_num = 0;
/* ===================================================================== */

VOID PIN_FAST_ANALYSIS_CALL docount(uint32_t* ptr, uint32_t c)
{
    (*ptr) += c;
}

VOID PIN_FAST_ANALYSIS_CALL inc_branch(
                INT32 taken,
                INT32* count_seen,
                INT32* count_loop_invoked,
                INT32* old_iter_count,
                INT32* cur_iter_count,
                INT32* diff_count)
{
    // Important Note: count_seen field is calculated to match the given example file.
    // If only backward edges calls are required (instead of total count), it would be incremented only if BRANCH=TAKEN!
    (*count_seen)++;
    (*cur_iter_count)++;
    if (!taken)
    {
        (*count_loop_invoked)++;

        if (*cur_iter_count != *old_iter_count)
        {
            (*diff_count)++;
        }
        *old_iter_count = *cur_iter_count;
        *cur_iter_count = 0;
    }
}

/* ===================================================================== */

// Pin calls this function every time a new basic block is encountered
// It inserts a call to docount
VOID Trace(TRACE trace, VOID* v)
{
    const RTN& trace_routine = TRACE_Rtn(trace);
    const ADDRINT& routine_addr = RTN_Address(trace_routine);
    // Visit every basic block  in the trace
    for (BBL bbl = TRACE_BblHead(trace); BBL_Valid(bbl); bbl = BBL_Next(bbl))
    {
        // Insert a call to docount for every bbl, passing the number of instructions.
        // IPOINT_ANYWHERE allows Pin to schedule the call anywhere in the bbl to obtain best performance.
        BBL_InsertCall(bbl, IPOINT_ANYWHERE, (AFUNPTR)docount,
                       IARG_FAST_ANALYSIS_CALL,
                       IARG_PTR, &routine_map[routine_addr], IARG_UINT32, BBL_NumIns(bbl), IARG_END);
    }
}

VOID Instruction(INS ins, VOID* v)
{
    if (!INS_Valid(ins)) { return; }

    const ADDRINT& ins_addr = INS_Address(ins);
    const RTN& ins_routine = RTN_FindByAddress(ins_addr);
    if (!RTN_Valid(ins_routine)) { return; }

    const IMG& routine_img = IMG_FindByAddress(ins_addr);
    if (!IMG_Valid(routine_img)) { return; }


    const ADDRINT& routine_addr = RTN_Address(ins_routine);
    const std::string &routine_name = RTN_Name(ins_routine);


    /* Ex 2 - verify this is a candidate for loop instruction
     * */
    if (!INS_IsDirectBranch(ins) || !INS_IsControlFlow(ins))
    {
        return;
    }

    const ADDRINT& target_addr = INS_DirectControlFlowTargetAddress(ins);
    if (target_addr >= ins_addr) // not a backward edge
    {
        return;
    }

    loops_profiler[ins_addr]._target_addr = target_addr;
    loops_profiler[ins_addr]._routine_addr = routine_addr;
    loops_profiler[ins_addr]._routine_name = routine_name;

    INS_InsertCall(ins, IPOINT_BEFORE, (AFUNPTR)inc_branch,
                   IARG_FAST_ANALYSIS_CALL,
                   IARG_BRANCH_TAKEN,
                   IARG_PTR, &loops_profiler[ins_addr]._count_seen,
                   IARG_PTR, &loops_profiler[ins_addr]._count_loop_invoked,
                   IARG_PTR, &loops_profiler[ins_addr]._old_iter_count,
                   IARG_PTR, &loops_profiler[ins_addr]._cur_iter_count,
                   IARG_PTR, &loops_profiler[ins_addr]._diff_count,
                   IARG_END);
}

/* ============================================================= */
/* Service dump routines                                         */
/* ============================================================= */

/*************************/
/* dump_all_image_instrs */
/*************************/
void dump_all_image_instrs(IMG img)
{
    for (SEC sec = IMG_SecHead(img); SEC_Valid(sec); sec = SEC_Next(sec))
    {
        for (RTN rtn = SEC_RtnHead(sec); RTN_Valid(rtn); rtn = RTN_Next(rtn))
        {

            // Open the RTN.
            RTN_Open( rtn );

            cerr << RTN_Name(rtn) << ":" << endl;

            for( INS ins = RTN_InsHead(rtn); INS_Valid(ins); ins = INS_Next(ins) )
            {
                cerr << "0x" << hex << INS_Address(ins) << ": " << INS_Disassemble(ins) << endl;
            }

            // Close the RTN.
            RTN_Close( rtn );
        }
    }
}


/*************************/
/* dump_instr_from_xedd */
/*************************/
void dump_instr_from_xedd (xed_decoded_inst_t* xedd, ADDRINT address)
{
    // debug print decoded instr:
    char disasm_buf[2048];

    xed_uint64_t runtime_address = static_cast<UINT64>(address);  // set the runtime adddress for disassembly

    xed_format_context(XED_SYNTAX_INTEL, xedd, disasm_buf, sizeof(disasm_buf), static_cast<UINT64>(runtime_address), 0, 0);

    cerr << hex << address << ": " << disasm_buf <<  endl;
}


/************************/
/* dump_instr_from_mem */
/************************/
void dump_instr_from_mem (ADDRINT *address, ADDRINT new_addr)
{
    char disasm_buf[2048];
    xed_decoded_inst_t new_xedd;

    xed_decoded_inst_zero_set_mode(&new_xedd,&dstate);

    xed_error_enum_t xed_code = xed_decode(&new_xedd, reinterpret_cast<UINT8*>(address), max_inst_len);

    BOOL xed_ok = (xed_code == XED_ERROR_NONE);
    if (!xed_ok){
        cerr << "invalid opcode" << endl;
        return;
    }

    xed_format_context(XED_SYNTAX_INTEL, &new_xedd, disasm_buf, 2048, static_cast<UINT64>(new_addr), 0, 0);

    if (KnobVerbose)
    {
        cerr << "0x" << hex << new_addr << ": " << disasm_buf <<  endl;
    }
}


/****************************/
/*  dump_entire_instr_map() */
/****************************/
void dump_entire_instr_map()
{
    for (int i=0; i < num_of_instr_map_entries; i++) {
        for (int j=0; j < translated_rtn_num; j++) {
            if (translated_rtn[j].instr_map_entry == i) {

                RTN rtn = RTN_FindByAddress(translated_rtn[j].rtn_addr);

                if (rtn == RTN_Invalid()) {
                    cerr << "Unknwon"  << ":" << endl;
                } else {
                    cerr << RTN_Name(rtn) << ":" << endl;
                }
            }
        }
        dump_instr_from_mem ((ADDRINT *)instr_map[i].new_ins_addr, instr_map[i].new_ins_addr);
    }
}


/**************************/
/* dump_instr_map_entry */
/**************************/
void dump_instr_map_entry(int instr_map_entry)
{
    cerr << dec << instr_map_entry << ": ";
    cerr << " orig_ins_addr: " << hex << instr_map[instr_map_entry].orig_ins_addr;
    cerr << " new_ins_addr: " << hex << instr_map[instr_map_entry].new_ins_addr;
    cerr << " orig_targ_addr: " << hex << instr_map[instr_map_entry].orig_targ_addr;

    ADDRINT new_targ_addr;
    if (instr_map[instr_map_entry].new_targ_entry >= 0)
        new_targ_addr = instr_map[instr_map[instr_map_entry].new_targ_entry].new_ins_addr;
    else
        new_targ_addr = instr_map[instr_map_entry].orig_targ_addr;

    cerr << " new_targ_addr: " << hex << new_targ_addr;
    cerr << "    new instr:";
    dump_instr_from_mem((ADDRINT *)instr_map[instr_map_entry].encoded_ins, instr_map[instr_map_entry].new_ins_addr);
}


/*************/
/* dump_tc() */
/*************/
void dump_tc()
{
    char disasm_buf[2048];
    xed_decoded_inst_t new_xedd;
    ADDRINT address = (ADDRINT)&tc[0];
    unsigned int size = 0;

    while (address < (ADDRINT)&tc[tc_cursor]) {

        address += size;

        xed_decoded_inst_zero_set_mode(&new_xedd,&dstate);

        xed_error_enum_t xed_code = xed_decode(&new_xedd, reinterpret_cast<UINT8*>(address), max_inst_len);

        BOOL xed_ok = (xed_code == XED_ERROR_NONE);
        if (!xed_ok){
            cerr << "invalid opcode" << endl;
            return;
        }

        xed_format_context(XED_SYNTAX_INTEL, &new_xedd, disasm_buf, 2048, static_cast<UINT64>(address), 0, 0);

        cerr << "0x" << hex << address << ": " << disasm_buf <<  endl;

        size = xed_decoded_inst_get_length (&new_xedd);
    }
}


/* ============================================================= */
/* Translation routines                                         */
/* ============================================================= */


// Ex4 - itay addition
int patched_add_new_instr_entry(xed_decoded_inst_t *xedd, ADDRINT pc, unsigned int size)
{
    // copy orig instr to instr map:
    ADDRINT orig_targ_addr = 0;

    if (xed_decoded_inst_get_length (xedd) != size) {
        cerr << "Invalid instruction decoding" << endl;
        return -1;
    }

    xed_uint_t disp_byts = xed_decoded_inst_get_branch_displacement_width(xedd);
    if (disp_byts > 0)
    {
        // We want to reverse the condition - so the fallthrough address is the new target address for the instructions
        // The cool trick is setting the displacement value to 0, so that it will point towards the original next instr
        xed_decoded_inst_set_branch_displacement(xedd, 0, disp_byts);
        orig_targ_addr = pc + size;
    }

    // Converts the decoder request to a valid encoder request:
    xed_encoder_request_init_from_decode (xedd);

    unsigned int new_size = 0;

    xed_error_enum_t xed_error = xed_encode (xedd, reinterpret_cast<UINT8*>(instr_map[num_of_instr_map_entries].encoded_ins), max_inst_len , &new_size);
    if (xed_error != XED_ERROR_NONE) {
        cerr << "ENCODE ERROR: " << xed_error_enum_t2str(xed_error) << endl;
        return -1;
    }

    // add a new entry in the instr_map:

    instr_map[num_of_instr_map_entries].orig_ins_addr = pc;
    instr_map[num_of_instr_map_entries].new_ins_addr = (ADDRINT)&tc[tc_cursor];  // set an initial estimated addr in tc
    instr_map[num_of_instr_map_entries].orig_targ_addr = orig_targ_addr;
    instr_map[num_of_instr_map_entries].hasNewTargAddr = false;
    instr_map[num_of_instr_map_entries].new_targ_entry = -1;
    instr_map[num_of_instr_map_entries].size = new_size;
    instr_map[num_of_instr_map_entries].category_enum = xed_decoded_inst_get_category(xedd);

    num_of_instr_map_entries++;

    // update expected size of tc:
    tc_cursor += new_size;

    if (num_of_instr_map_entries >= max_ins_count) {
        cerr << "out of memory for map_instr" << endl;
        return -1;
    }


    // debug print new encoded instr:
    if (KnobVerbose) {
        cerr << "    new instr:";
        dump_instr_from_mem((ADDRINT *)instr_map[num_of_instr_map_entries-1].encoded_ins, instr_map[num_of_instr_map_entries-1].new_ins_addr);
    }

    return new_size;
}

/*************************/
/* add_new_instr_entry() */
/*************************/
int add_new_instr_entry(xed_decoded_inst_t *xedd, ADDRINT pc, unsigned int size)
{

    // copy orig instr to instr map:
    ADDRINT orig_targ_addr = 0;

    if (xed_decoded_inst_get_length (xedd) != size) {
        cerr << "Invalid instruction decoding" << endl;
        return -1;
    }

    xed_uint_t disp_byts = xed_decoded_inst_get_branch_displacement_width(xedd);

    xed_int32_t disp;

    if (disp_byts > 0) { // there is a branch offset.
        disp = xed_decoded_inst_get_branch_displacement(xedd);
        orig_targ_addr = pc + xed_decoded_inst_get_length (xedd) + disp;
    }

    // Converts the decoder request to a valid encoder request:
    xed_encoder_request_init_from_decode (xedd);

    unsigned int new_size = 0;

    xed_error_enum_t xed_error = xed_encode (xedd, reinterpret_cast<UINT8*>(instr_map[num_of_instr_map_entries].encoded_ins), max_inst_len , &new_size);
    if (xed_error != XED_ERROR_NONE) {
        cerr << "ENCODE ERROR: " << xed_error_enum_t2str(xed_error) << endl;
        return -1;
    }

    // add a new entry in the instr_map:

    instr_map[num_of_instr_map_entries].orig_ins_addr = pc;
    instr_map[num_of_instr_map_entries].new_ins_addr = (ADDRINT)&tc[tc_cursor];  // set an initial estimated addr in tc
    instr_map[num_of_instr_map_entries].orig_targ_addr = orig_targ_addr;
    instr_map[num_of_instr_map_entries].hasNewTargAddr = false;
    instr_map[num_of_instr_map_entries].new_targ_entry = -1;
    instr_map[num_of_instr_map_entries].size = new_size;
    instr_map[num_of_instr_map_entries].category_enum = xed_decoded_inst_get_category(xedd);

    num_of_instr_map_entries++;

    // update expected size of tc:
    tc_cursor += new_size;

    if (num_of_instr_map_entries >= max_ins_count) {
        cerr << "out of memory for map_instr" << endl;
        return -1;
    }


    // debug print new encoded instr:
    if (KnobVerbose) {
        cerr << "    new instr:";
        dump_instr_from_mem((ADDRINT *)instr_map[num_of_instr_map_entries-1].encoded_ins, instr_map[num_of_instr_map_entries-1].new_ins_addr);
    }

    return new_size;
}


/*************************************************/
/* chain_all_direct_br_and_call_target_entries() */
/*************************************************/
int chain_all_direct_br_and_call_target_entries()
{
    for (int i=0; i < num_of_instr_map_entries; i++) {

        if (instr_map[i].orig_targ_addr == 0)
            continue;

        if (instr_map[i].hasNewTargAddr)
            continue;

        for (int j = 0; j < num_of_instr_map_entries; j++) {

            if (j == i)
                continue;

            if (instr_map[j].orig_ins_addr == instr_map[i].orig_targ_addr) {
                instr_map[i].hasNewTargAddr = true;
                instr_map[i].new_targ_entry = j;
                break;
            }
        }
    }

    return 0;
}


/**************************/
/* fix_rip_displacement() */
/**************************/
int fix_rip_displacement(int instr_map_entry)
{
    //debug print:
    //dump_instr_map_entry(instr_map_entry);

    xed_decoded_inst_t xedd;
    xed_decoded_inst_zero_set_mode(&xedd,&dstate);

    xed_error_enum_t xed_code = xed_decode(&xedd, reinterpret_cast<UINT8*>(instr_map[instr_map_entry].encoded_ins), max_inst_len);
    if (xed_code != XED_ERROR_NONE) {
        cerr << "ERROR: xed decode failed for instr at: " << "0x" << hex << instr_map[instr_map_entry].new_ins_addr << endl;
        return -1;
    }

    unsigned int memops = xed_decoded_inst_number_of_memory_operands(&xedd);

    if (instr_map[instr_map_entry].orig_targ_addr != 0)  // a direct jmp or call instruction.
        return 0;

    //cerr << "Memory Operands" << endl;
    bool isRipBase = false;
    xed_reg_enum_t base_reg = XED_REG_INVALID;
    xed_int64_t disp = 0;
    for(unsigned int i=0; i < memops ; i++)   {

        base_reg = xed_decoded_inst_get_base_reg(&xedd,i);
        disp = xed_decoded_inst_get_memory_displacement(&xedd,i);

        if (base_reg == XED_REG_RIP) {
            isRipBase = true;
            break;
        }

    }

    if (!isRipBase)
        return 0;


    //xed_uint_t disp_byts = xed_decoded_inst_get_memory_displacement_width(xedd,i); // how many byts in disp ( disp length in byts - for example FFFFFFFF = 4
    xed_int64_t new_disp = 0;
    xed_uint_t new_disp_byts = 4;   // set maximal num of byts for now.

    unsigned int orig_size = xed_decoded_inst_get_length (&xedd);

    // modify rip displacement. use direct addressing mode:
    new_disp = instr_map[instr_map_entry].orig_ins_addr + disp + orig_size; // xed_decoded_inst_get_length (&xedd_orig);
    xed_encoder_request_set_base0 (&xedd, XED_REG_INVALID);

    //Set the memory displacement using a bit length
    xed_encoder_request_set_memory_displacement (&xedd, new_disp, new_disp_byts);

    unsigned int size = XED_MAX_INSTRUCTION_BYTES;
    unsigned int new_size = 0;

    // Converts the decoder request to a valid encoder request:
    xed_encoder_request_init_from_decode (&xedd);

    xed_error_enum_t xed_error = xed_encode (&xedd, reinterpret_cast<UINT8*>(instr_map[instr_map_entry].encoded_ins), size , &new_size); // &instr_map[i].size
    if (xed_error != XED_ERROR_NONE) {
        cerr << "ENCODE ERROR: " << xed_error_enum_t2str(xed_error) << endl;
        dump_instr_map_entry(instr_map_entry);
        return -1;
    }

    if (KnobVerbose) {
        dump_instr_map_entry(instr_map_entry);
    }

    return new_size;
}


/************************************/
/* fix_direct_br_call_to_orig_addr */
/************************************/
int fix_direct_br_call_to_orig_addr(int instr_map_entry)
{

    xed_decoded_inst_t xedd;
    xed_decoded_inst_zero_set_mode(&xedd,&dstate);

    xed_error_enum_t xed_code = xed_decode(&xedd, reinterpret_cast<UINT8*>(instr_map[instr_map_entry].encoded_ins), max_inst_len);
    if (xed_code != XED_ERROR_NONE) {
        cerr << "ERROR: xed decode failed for instr at: " << "0x" << hex << instr_map[instr_map_entry].new_ins_addr << endl;
        return -1;
    }

    xed_category_enum_t category_enum = xed_decoded_inst_get_category(&xedd);

    if (category_enum != XED_CATEGORY_CALL && category_enum != XED_CATEGORY_UNCOND_BR) {

        cerr << "ERROR: Invalid direct jump from translated code to original code in rotuine: "
             << RTN_Name(RTN_FindByAddress(instr_map[instr_map_entry].orig_ins_addr)) << endl;
        dump_instr_map_entry(instr_map_entry);
        return -1;
    }

    // check for cases of direct jumps/calls back to the orginal target address:
    if (instr_map[instr_map_entry].new_targ_entry >= 0) {
        cerr << "ERROR: Invalid jump or call instruction" << endl;
        return -1;
    }

    unsigned int ilen = XED_MAX_INSTRUCTION_BYTES;
    unsigned int olen = 0;


    xed_encoder_instruction_t  enc_instr;

    ADDRINT new_disp = (ADDRINT)&instr_map[instr_map_entry].orig_targ_addr -
                                 instr_map[instr_map_entry].new_ins_addr -
                                 xed_decoded_inst_get_length (&xedd);

    if (category_enum == XED_CATEGORY_CALL)
        xed_inst1(&enc_instr, dstate,
                  XED_ICLASS_CALL_NEAR, 64,
                  xed_mem_bd (XED_REG_RIP, xed_disp(new_disp, 32), 64));

    if (category_enum == XED_CATEGORY_UNCOND_BR)
        xed_inst1(&enc_instr, dstate,
                  XED_ICLASS_JMP, 64,
                  xed_mem_bd (XED_REG_RIP, xed_disp(new_disp, 32), 64));


    xed_encoder_request_t enc_req;

    xed_encoder_request_zero_set_mode(&enc_req, &dstate);
    xed_bool_t convert_ok = xed_convert_to_encoder_request(&enc_req, &enc_instr);
    if (!convert_ok) {
        cerr << "conversion to encode request failed" << endl;
        return -1;
    }


    xed_error_enum_t xed_error = xed_encode(&enc_req, reinterpret_cast<UINT8*>(instr_map[instr_map_entry].encoded_ins), ilen, &olen);
    if (xed_error != XED_ERROR_NONE) {
        cerr << "ENCODE ERROR: " << xed_error_enum_t2str(xed_error) << endl;
        dump_instr_map_entry(instr_map_entry);
        return -1;
    }

    // handle the case where the original instr size is different from new encoded instr:
    if (olen != xed_decoded_inst_get_length (&xedd)) {

        new_disp = (ADDRINT)&instr_map[instr_map_entry].orig_targ_addr -
                             instr_map[instr_map_entry].new_ins_addr - olen;

        if (category_enum == XED_CATEGORY_CALL)
            xed_inst1(&enc_instr, dstate,
                      XED_ICLASS_CALL_NEAR, 64,
                      xed_mem_bd (XED_REG_RIP, xed_disp(new_disp, 32), 64));

        if (category_enum == XED_CATEGORY_UNCOND_BR)
            xed_inst1(&enc_instr, dstate,
                      XED_ICLASS_JMP, 64,
                      xed_mem_bd (XED_REG_RIP, xed_disp(new_disp, 32), 64));


        xed_encoder_request_zero_set_mode(&enc_req, &dstate);
        xed_bool_t convert_ok = xed_convert_to_encoder_request(&enc_req, &enc_instr);
        if (!convert_ok) {
            cerr << "conversion to encode request failed" << endl;
            return -1;
        }

        xed_error = xed_encode (&enc_req, reinterpret_cast<UINT8*>(instr_map[instr_map_entry].encoded_ins), ilen , &olen);
        if (xed_error != XED_ERROR_NONE) {
            cerr << "ENCODE ERROR: " << xed_error_enum_t2str(xed_error) << endl;
            dump_instr_map_entry(instr_map_entry);
            return -1;
        }
    }


    // debug prints:
    if (KnobVerbose) {
        dump_instr_map_entry(instr_map_entry);
    }

    instr_map[instr_map_entry].hasNewTargAddr = true;
    return olen;
}


/***********************************/
/* fix_direct_br_call_displacement */
/***********************************/
int fix_direct_br_call_displacement(int instr_map_entry)
{

    xed_decoded_inst_t xedd;
    xed_decoded_inst_zero_set_mode(&xedd,&dstate);

    xed_error_enum_t xed_code = xed_decode(&xedd, reinterpret_cast<UINT8*>(instr_map[instr_map_entry].encoded_ins), max_inst_len);
    if (xed_code != XED_ERROR_NONE) {
        cerr << "ERROR: xed decode failed for instr at: " << "0x" << hex << instr_map[instr_map_entry].new_ins_addr << endl;
        return -1;
    }

    xed_int32_t  new_disp = 0;
    unsigned int size = XED_MAX_INSTRUCTION_BYTES;
    unsigned int new_size = 0;


    xed_category_enum_t category_enum = xed_decoded_inst_get_category(&xedd);

    if (category_enum != XED_CATEGORY_CALL && category_enum != XED_CATEGORY_COND_BR && category_enum != XED_CATEGORY_UNCOND_BR) {
        cerr << "ERROR: unrecognized branch displacement" << endl;
        return -1;
    }

    // fix branches/calls to original targ addresses:
    if (instr_map[instr_map_entry].new_targ_entry < 0) {
        int rc = fix_direct_br_call_to_orig_addr(instr_map_entry);
        return rc;
    }

    ADDRINT new_targ_addr;
    new_targ_addr = instr_map[instr_map[instr_map_entry].new_targ_entry].new_ins_addr;

    new_disp = (new_targ_addr - instr_map[instr_map_entry].new_ins_addr) - instr_map[instr_map_entry].size; // orig_size;

    xed_uint_t   new_disp_byts = 4; // num_of_bytes(new_disp);  ???

    // the max displacement size of loop instructions is 1 byte:
    xed_iclass_enum_t iclass_enum = xed_decoded_inst_get_iclass(&xedd);
    if (iclass_enum == XED_ICLASS_LOOP ||  iclass_enum == XED_ICLASS_LOOPE || iclass_enum == XED_ICLASS_LOOPNE) {
        new_disp_byts = 1;
    }

    // the max displacement size of jecxz instructions is ???:
    xed_iform_enum_t iform_enum = xed_decoded_inst_get_iform_enum (&xedd);
    if (iform_enum == XED_IFORM_JRCXZ_RELBRb){
        new_disp_byts = 1;
    }

    // Converts the decoder request to a valid encoder request:
    xed_encoder_request_init_from_decode (&xedd);

    //Set the branch displacement:
    xed_encoder_request_set_branch_displacement (&xedd, new_disp, new_disp_byts);

    xed_uint8_t enc_buf[XED_MAX_INSTRUCTION_BYTES];
    unsigned int max_size = XED_MAX_INSTRUCTION_BYTES;

    xed_error_enum_t xed_error = xed_encode (&xedd, enc_buf, max_size , &new_size);
    if (xed_error != XED_ERROR_NONE) {
        cerr << "ENCODE ERROR: " << xed_error_enum_t2str(xed_error) <<  endl;
        char buf[2048];
        xed_format_context(XED_SYNTAX_INTEL, &xedd, buf, 2048, static_cast<UINT64>(instr_map[instr_map_entry].orig_ins_addr), 0, 0);
        cerr << " instr: " << "0x" << hex << instr_map[instr_map_entry].orig_ins_addr << " : " << buf <<  endl;
        return -1;
    }

    new_targ_addr = instr_map[instr_map[instr_map_entry].new_targ_entry].new_ins_addr;

    new_disp = new_targ_addr - (instr_map[instr_map_entry].new_ins_addr + new_size);  // this is the correct displacemnet.

    //Set the branch displacement:
    xed_encoder_request_set_branch_displacement (&xedd, new_disp, new_disp_byts);

    xed_error = xed_encode (&xedd, reinterpret_cast<UINT8*>(instr_map[instr_map_entry].encoded_ins), size , &new_size); // &instr_map[i].size
    if (xed_error != XED_ERROR_NONE) {
        cerr << "ENCODE ERROR: " << xed_error_enum_t2str(xed_error) << endl;
        dump_instr_map_entry(instr_map_entry);
        return -1;
    }

    //debug print of new instruction in tc:
    if (KnobVerbose) {
        dump_instr_map_entry(instr_map_entry);
    }

    return new_size;
}


/************************************/
/* fix_instructions_displacements() */
/************************************/
int fix_instructions_displacements()
{
    // fix displacemnets of direct branch or call instructions:

    int size_diff = 0;

    do {

        size_diff = 0;

        if (KnobVerbose) {
            cerr << "starting a pass of fixing instructions displacements: " << endl;
        }

        for (int i=0; i < num_of_instr_map_entries; i++) {

            instr_map[i].new_ins_addr += size_diff;

            int rc = 0;

            // fix rip displacement:
            rc = fix_rip_displacement(i);
            if (rc < 0)
                return -1;

            if (rc > 0) { // this was a rip-based instruction which was fixed.

                if (instr_map[i].size != (unsigned int)rc) {
                    size_diff += (rc - instr_map[i].size);
                    instr_map[i].size = (unsigned int)rc;
                }

                continue;
            }

            // check if it is a direct branch or a direct call instr:
            if (instr_map[i].orig_targ_addr == 0) {
                continue;  // not a direct branch or a direct call instr.
            }


            // fix instr displacement:
            rc = fix_direct_br_call_displacement(i);
            if (rc < 0)
                return -1;

            if (instr_map[i].size != (unsigned int)rc) {
                size_diff += (rc - instr_map[i].size);
                instr_map[i].size = (unsigned int)rc;
            }

        }  // end int i=0; i ..

    } while (size_diff != 0);

    return 0;
}


void get_inverse_inst(INS ins, xed_decoded_inst_t* output_inst)
{
    xed_decoded_inst_t *xedd = INS_XedDec(ins);
    xed_category_enum_t category_enum = xed_decoded_inst_get_category(xedd);

    if (category_enum != XED_CATEGORY_COND_BR)
        return;

    xed_iclass_enum_t iclass_enum = xed_decoded_inst_get_iclass(xedd);

    if (iclass_enum == XED_ICLASS_JRCXZ)
        return;    // do not revert JRCXZ

    xed_iclass_enum_t 	retverted_iclass;

    switch (iclass_enum)
    {
        case XED_ICLASS_JB:
            retverted_iclass = XED_ICLASS_JNB;
            break;

        case XED_ICLASS_JBE:
            retverted_iclass = XED_ICLASS_JNBE;
            break;

        case XED_ICLASS_JL:
            retverted_iclass = XED_ICLASS_JNL;
            break;

        case XED_ICLASS_JLE:
            retverted_iclass = XED_ICLASS_JNLE;
            break;

        case XED_ICLASS_JNB:
            retverted_iclass = XED_ICLASS_JB;
            break;

        case XED_ICLASS_JNBE:
            retverted_iclass = XED_ICLASS_JBE;
            break;

        case XED_ICLASS_JNL:
            retverted_iclass = XED_ICLASS_JL;
            break;

        case XED_ICLASS_JNLE:
            retverted_iclass = XED_ICLASS_JLE;
            break;

        case XED_ICLASS_JNO:
            retverted_iclass = XED_ICLASS_JO;
            break;

        case XED_ICLASS_JNP:
            retverted_iclass = XED_ICLASS_JP;
            break;

        case XED_ICLASS_JNS:
            retverted_iclass = XED_ICLASS_JS;
            break;

        case XED_ICLASS_JNZ:
            retverted_iclass = XED_ICLASS_JZ;
            break;

        case XED_ICLASS_JO:
            retverted_iclass = XED_ICLASS_JNO;
            break;

        case XED_ICLASS_JP:
            retverted_iclass = XED_ICLASS_JNP;
            break;

        case XED_ICLASS_JS:
            retverted_iclass = XED_ICLASS_JNS;
            break;

        case XED_ICLASS_JZ:
            retverted_iclass = XED_ICLASS_JNZ;
            break;

        default:
            return;
    }

    // Converts the decoder request to a valid encoder request:
    xed_encoder_request_init_from_decode(xedd);

    // set the reverted opcode;
    xed_encoder_request_set_iclass(xedd, retverted_iclass);

    xed_uint8_t enc_buf[XED_MAX_INSTRUCTION_BYTES];
    unsigned int max_size = XED_MAX_INSTRUCTION_BYTES;
    unsigned int new_size = 0;

    xed_error_enum_t xed_error = xed_encode (xedd, enc_buf, max_size, &new_size);
    if (xed_error != XED_ERROR_NONE) {
        cerr << "ENCODE ERROR: " << xed_error_enum_t2str(xed_error) <<  endl;
        return;
    }


    //print the original and the new reverted cond instructions:
    //
    cerr << "orig instr: " << hex << INS_Address(ins) << " " << INS_Disassemble(ins) << endl;

    char buf[2048];
    xed_decoded_inst_t new_xedd;
    xed_decoded_inst_zero_set_mode(&new_xedd,&dstate);

    xed_error_enum_t xed_code = xed_decode(&new_xedd, enc_buf, XED_MAX_INSTRUCTION_BYTES);
    if (xed_code != XED_ERROR_NONE)
    {
        cerr << "ERROR: xed decode failed for instr at: " << "0x" << hex << INS_Address(ins) << endl;
        return;
    }

    xed_format_context(XED_SYNTAX_INTEL, &new_xedd, buf, 2048, INS_Address(ins), 0, 0);
    cerr << "new  instr: " << hex << INS_Address(ins) << " " << buf << endl << endl;

    *output_inst = new_xedd;
}

// Exercise 4 - Itay addition
void add_regular_instr_helper(INS ins)
{
    int rc;
    ADDRINT addr = INS_Address(ins);

    xed_decoded_inst_t xedd;
    xed_error_enum_t xed_code;
    xed_decoded_inst_zero_set_mode(&xedd, &dstate);
    xed_code = xed_decode(&xedd, reinterpret_cast<UINT8 *>(addr), max_inst_len);
    if (xed_code != XED_ERROR_NONE)
    {
        cerr << "ERROR: xed decode failed for instr at: " << "0x" << hex << addr << endl;
        translated_rtn[translated_rtn_num].instr_map_entry = -1;
        return;
    }
    // Add instr into instr map:
    rc = add_new_instr_entry(&xedd, INS_Address(ins), INS_Size(ins));
    if (rc < 0)
    {
        cerr << "ERROR: failed during instructon translation." << endl;
        translated_rtn[translated_rtn_num].instr_map_entry = -1;
        return;
    }
}


int optimize_loop_unrolling(RTN rtn, int factor, uint64_t loop_start_addr, uint64_t loop_end_addr)
{
    bool during_loop_unroll = false;
    std::vector<INS> cached_insts = std::vector<INS>();

    for (INS ins = RTN_InsHead(rtn); INS_Valid(ins); ins = INS_Next(ins))
    {
        //debug print of orig instruction:
        if (KnobVerbose)
        {
            cerr << "old instr: ";
            cerr << "0x" << hex << INS_Address(ins) << ": " << INS_Disassemble(ins) << endl;
            //xed_print_hex_line(reinterpret_cast<UINT8*>(INS_Address (ins)), INS_Size(ins));
        }
        ADDRINT addr = INS_Address(ins);

        // Non-optimized inst
        if (((addr < loop_start_addr) || (addr > loop_end_addr)) && (!during_loop_unroll))
        {
            add_regular_instr_helper(ins);
        }
        // First Loop-unrolling optimized inst
        else if (addr == loop_start_addr)
        {
            during_loop_unroll = true;
            cached_insts.push_back(ins);
            add_regular_instr_helper(ins);
        }

        // Last optimized inst
        else if (addr == loop_end_addr)
        {
            xed_decoded_inst_t patched_inst;
            xed_decoded_inst_zero_set_mode(&patched_inst,&dstate);
            get_inverse_inst(ins, &patched_inst);

            for (int i = 0 ; i < (factor - 1) ; i++)
            {
                patched_add_new_instr_entry(&patched_inst, INS_Address(ins), INS_Size(ins));
                for (auto &cached_inst : cached_insts)
                {
                    add_regular_instr_helper(cached_inst);
                }
            }
            // Last condition instruction remains the same
            add_regular_instr_helper(ins);

            during_loop_unroll = false;
        }

        // Intermediate optimized instructions (between start and end)
        else
        {
            cached_insts.push_back(ins);
            add_regular_instr_helper(ins);
        }
    }

    return 0;
}


/*****************************************/
/* find_candidate_rtns_for_translation() */
/*****************************************/
int find_candidate_rtns_for_translation(IMG img)
{
    int rc;

    // go over routines and check if they are candidates for translation and mark them for translation:
//    for (SEC sec = IMG_SecHead(img); SEC_Valid(sec); sec = SEC_Next(sec))
//    {
//        if (!SEC_IsExecutable(sec) || SEC_IsWriteable(sec) || !SEC_Address(sec))
//            continue;
//
//        for (RTN rtn = SEC_RtnHead(sec); RTN_Valid(rtn); rtn = RTN_Next(rtn))
//        {

    uint32_t candidates_counter = 0;
    for (const auto &candid: candidates)
    {
        if (candidates_counter == CANDIDATE_COUNT)
        {
            break;
        }
        RTN rtn = RTN_FindByAddress(candid.first);

        if (rtn == RTN_Invalid()) {
            cerr << "Warning: invalid routine " << RTN_Name(rtn) << endl;
            continue;
        }

        translated_rtn[translated_rtn_num].rtn_addr = RTN_Address(rtn);
        translated_rtn[translated_rtn_num].rtn_size = RTN_Size(rtn);
        translated_rtn[translated_rtn_num].instr_map_entry = num_of_instr_map_entries;
        translated_rtn[translated_rtn_num].isSafeForReplacedProbe = true;

        // Open the RTN.
        RTN_Open(rtn);

        if (RTN_Name(rtn) == "fallbackSort")
        {
            optimize_loop_unrolling(rtn, 4, 0x409fde, 0x40a076);
        }

        else
        {
            for (INS ins = RTN_InsHead(rtn); INS_Valid(ins); ins = INS_Next(ins))
            {
                //debug print of orig instruction:
                if (KnobVerbose)
                {
                    cerr << "old instr: ";
                    cerr << "0x" << hex << INS_Address(ins) << ": " << INS_Disassemble(ins) << endl;
                    //xed_print_hex_line(reinterpret_cast<UINT8*>(INS_Address (ins)), INS_Size(ins));
                }
                ADDRINT addr = INS_Address(ins);

                xed_decoded_inst_t xedd;
                xed_error_enum_t xed_code;
                xed_decoded_inst_zero_set_mode(&xedd, &dstate);
                xed_code = xed_decode(&xedd, reinterpret_cast<UINT8 *>(addr), max_inst_len);
                if (xed_code != XED_ERROR_NONE)
                {
                    cerr << "ERROR: xed decode failed for instr at: " << "0x" << hex << addr << endl;
                    translated_rtn[translated_rtn_num].instr_map_entry = -1;
                    break;
                }
                // Add instr into instr map:
                rc = add_new_instr_entry(&xedd, INS_Address(ins), INS_Size(ins));
                if (rc < 0)
                {
                    cerr << "ERROR: failed during instructon translation." << endl;
                    translated_rtn[translated_rtn_num].instr_map_entry = -1;
                    break;
                }
            } // end for INS...
        }

        // debug print of routine name:
        if (KnobVerbose)
        {
            cerr << "rtn name: " << RTN_Name(rtn) << " : " << dec << translated_rtn_num << endl;
        }

        // Close the RTN.
        RTN_Close(rtn);

        translated_rtn_num++;
        candidates_counter++;
    } // end for RTN..
//    } // end for SEC...

    return 0;
}


/***************************/
/* int copy_instrs_to_tc() */
/***************************/
int copy_instrs_to_tc()
{
    int cursor = 0;

    for (int i=0; i < num_of_instr_map_entries; i++) {

        if ((ADDRINT)&tc[cursor] != instr_map[i].new_ins_addr) {
            cerr << "ERROR: Non-matching instruction addresses: " << hex << (ADDRINT)&tc[cursor] << " vs. " << instr_map[i].new_ins_addr << endl;
            return -1;
        }

        memcpy(&tc[cursor], &instr_map[i].encoded_ins, instr_map[i].size);

        cursor += instr_map[i].size;
    }

    return 0;
}


/*************************************/
/* void commit_translated_routines() */
/*************************************/
inline void commit_translated_routines()
{
    // Commit the translated functions:
    // Go over the candidate functions and replace the original ones by their new successfully translated ones:

    for (int i=0; i < translated_rtn_num; i++) {

        //replace function by new function in tc

        if (translated_rtn[i].instr_map_entry >= 0) {

            if (translated_rtn[i].rtn_size > MAX_PROBE_JUMP_INSTR_BYTES && translated_rtn[i].isSafeForReplacedProbe) {

                RTN rtn = RTN_FindByAddress(translated_rtn[i].rtn_addr);

                //debug print:
                if (rtn == RTN_Invalid()) {
                    cerr << "committing rtN: Unknown";
                } else {
                    cerr << "committing rtN: " << RTN_Name(rtn);
                }
                cerr << " from: 0x" << hex << RTN_Address(rtn) << " to: 0x" << hex
                     << instr_map[translated_rtn[i].instr_map_entry].new_ins_addr << endl;


                if (RTN_IsSafeForProbedReplacement(rtn)) {

                    AFUNPTR origFptr = RTN_ReplaceProbed(rtn,  (AFUNPTR)instr_map[translated_rtn[i].instr_map_entry].new_ins_addr);

                    if (KnobVerbose)
                    {
                        if (origFptr == NULL) {
                            cerr << "RTN_ReplaceProbed failed.";
                        } else {
                            cerr << "RTN_ReplaceProbed succeeded. ";
                        }
                        cerr << " orig routine addr: 0x" << hex << translated_rtn[i].rtn_addr
                             << " replacement routine addr: 0x" << hex
                             << instr_map[translated_rtn[i].instr_map_entry].new_ins_addr << endl;

                    }
                    dump_instr_from_mem((ADDRINT *)translated_rtn[i].rtn_addr, translated_rtn[i].rtn_addr);
                }
            }
        }
    }
}

/****************************/
/* allocate_and_init_memory */
/****************************/
int allocate_and_init_memory(IMG img)
{
    // Calculate size of executable sections and allocate required memory:
    //
    for (SEC sec = IMG_SecHead(img); SEC_Valid(sec); sec = SEC_Next(sec))
    {
        if (!SEC_IsExecutable(sec) || SEC_IsWriteable(sec) || !SEC_Address(sec))
            continue;


        if (!lowest_sec_addr || lowest_sec_addr > SEC_Address(sec))
            lowest_sec_addr = SEC_Address(sec);

        if (highest_sec_addr < SEC_Address(sec) + SEC_Size(sec))
            highest_sec_addr = SEC_Address(sec) + SEC_Size(sec);

        // need to avouid using RTN_Open as it is expensive...
        for (RTN rtn = SEC_RtnHead(sec); RTN_Valid(rtn); rtn = RTN_Next(rtn))
        {

            if (rtn == RTN_Invalid())
                continue;
            // TODO: check if RTN_SIZE calculation is needed here

            max_ins_count += RTN_NumIns  (rtn);
            max_rtn_count++;
        }
    }

    max_ins_count *= 4; // estimating that the num of instrs of the inlined functions will not exceed the total nunmber of the entire code.

    // Allocate memory for the instr map needed to fix all branch targets in translated routines:
    instr_map = (instr_map_t *)calloc(max_ins_count, sizeof(instr_map_t));
    if (instr_map == NULL) {
        perror("calloc");
        return -1;
    }


    // Allocate memory for the array of candidate routines containing inlineable function calls:
    // Need to estimate size of inlined routines.. ???
    translated_rtn = (translated_rtn_t *)calloc(max_rtn_count, sizeof(translated_rtn_t));
    if (translated_rtn == NULL) {
        perror("calloc");
        return -1;
    }


    // TODO: check if such a huge TC is needed
    // get a page size in the system:
    int pagesize = sysconf(_SC_PAGE_SIZE);
    if (pagesize == -1) {
        perror("sysconf");
        return -1;
    }

    ADDRINT text_size = (highest_sec_addr - lowest_sec_addr) * 2 + pagesize * 4;

    int tclen = 2 * text_size + pagesize * 4;   // need a better estimate???

    // Allocate the needed tc with RW+EXEC permissions and is not located in an address that is more than 32bits afar:
    char * addr = (char *) mmap(NULL, tclen, PROT_READ | PROT_WRITE | PROT_EXEC, MAP_PRIVATE | MAP_ANONYMOUS, 0, 0);
    if ((ADDRINT) addr == 0xffffffffffffffff) {
        cerr << "failed to allocate tc" << endl;
        return -1;
    }

    tc = (char *)addr;
    return 0;
}

size_t find_nth(const string& haystack, size_t pos, const string& needle, size_t nth)
{
    size_t found_pos = haystack.find(needle, pos);
    if(0 == nth || string::npos == found_pos)
    {
        return found_pos;
    }

    return find_nth(haystack, found_pos+1, needle, nth-1);
}

void read_profile(IMG img)
{
    std::string line;
    uint64_t candidates_counter = 0;
    while(std::getline(in_file, line))
    {
        std::istringstream iss(line);
        std::string segment;
        uint64_t counter = 0;
        uint64_t candid_addr = 0;
        uint32_t candid_inst_count = 0;
        IMG routine_img;
        while(std::getline(iss, segment, ','))
        {
            // Taking the 7'th element out of 8
            if (counter % 8 == 6)
            {
                std::istringstream converter(segment);
                converter >> std::hex >> candid_addr;
                routine_img = IMG_FindByAddress(candid_addr);
            }
            if (counter % 8 == 7)
            {
                std::istringstream converter(segment);
                converter >> candid_inst_count;

                if (!IMG_Valid(routine_img) || !IMG_IsMainExecutable(routine_img))
                {
                    counter++;
                    continue;
                }

                candidates_map[candid_addr] = candid_inst_count;
                candidates_counter++;
            }
            counter++;
        }
    }
    candidates = std::vector<std::pair<ADDRINT, uint32_t>>(candidates_map.begin(), candidates_map.end());
    auto cmp_lambda = [](const std::pair<ADDRINT, uint32_t>& a, const std::pair<ADDRINT, uint32_t>& b)
    {
        return a.second > b.second;
    };
    std::sort(candidates.begin(), candidates.end(), cmp_lambda);
}
/* ============================================ */
/* Main translation routine                     */
/* ============================================ */
VOID ImageLoad(IMG img, VOID *v)
{
    // debug print of all images' instructions
    //dump_all_image_instrs(img);

    // Step 0: Check the image and the CPU:
    if (!IMG_IsMainExecutable(img))
    {
        return;
    }

    read_profile(img);

    // step 1: Check size of executable sections and allocate required memory:
    int rc = 0;
    rc = allocate_and_init_memory(img);
    if (rc < 0)
    {
        return;
    }
    //cout << "after memory allocation" << endl;

    // Step 2: go over all routines and identify candidate routines and copy their code into the instr map IR:
    rc = find_candidate_rtns_for_translation(img);
    if (rc < 0)
    {
        return;
    }
    //cout << "after identifying candidate routines" << endl;

    // Step 3: Chaining - calculate direct branch and call instructions to point to corresponding target instr entries:
    rc = chain_all_direct_br_and_call_target_entries();
    if (rc < 0 )
    {
        return;
    }
    //cout << "after calculate direct br targets" << endl;

    // Step 4: fix rip-based, direct branch and direct call displacements:
    rc = fix_instructions_displacements();
    if (rc < 0 )
    {
        return;
    }
    //cout << "after fix instructions displacements" << endl;

    // Step 5: write translated routines to new tc:
    rc = copy_instrs_to_tc();
    if (rc < 0 )
    {
        return;
    }
    //cout << "after write all new instructions to memory tc" << endl;

    if (KnobDumpTranslatedCode)
    {
        cerr << "Translation Cache dump:" << endl;
        dump_tc();  // dump the entire tc

        cerr << endl << "instructions map dump:" << endl;
        dump_entire_instr_map();     // dump all translated instructions in map_instr
    }

    // Step 6: Commit the translated routines:
    //Go over the candidate functions and replace the original ones by their new successfully translated ones:
    commit_translated_routines();
    // cout << "after commit translated routines" << endl;

    return;
}

/* ===================================================================== */

VOID Fini(INT32 code, VOID* v)
{
    std::vector<std::pair<ADDRINT, Loop>> loops(loops_profiler.begin(), loops_profiler.end());
    auto cmp_lambda = [](const std::pair<ADDRINT, Loop>& a, const std::pair<ADDRINT, Loop>& b)
            {
                return a.second._count_seen > b.second._count_seen;
            };
    std::sort(loops.begin(), loops.end(), cmp_lambda);

    for (const auto& x : loops)
    {
        std::stringstream ss;
        ss << std::hex << x.first;
        std::string target_addr = "0x" + ss.str();

        double mean_taken = 0;
        if (x.second._count_loop_invoked == 0)
        {
            mean_taken = x.second._count_seen;
        }
        else
        {
            mean_taken = double(x.second._count_seen) / x.second._count_loop_invoked;
        }
        std::stringstream ss2;
        ss2 << std::hex << x.second._routine_addr;
        std::string routine_addr = "0x" + ss2.str();

        uint32_t routine_inst_count = routine_map[x.second._routine_addr];

        out_file << target_addr << "," << x.second._count_seen << "," << x.second._count_loop_invoked << "," << mean_taken << "," << x.second._diff_count << "," << x.second._routine_name << "," << routine_addr << "," << routine_inst_count << "\n";
    }
    out_file.close();
}

VOID InstFini(INT32 code, VOID* v)
{
    in_file.close();
}
/* ===================================================================== */

int main(int argc, char* argv[])
{
    PIN_InitSymbols();

    if (PIN_Init(argc, argv))
    {
        return Usage();
    }

    if (KnobProf)
    {
        std::cout << "Running profiling..\n";
        INS_AddInstrumentFunction(Instruction, 0);
        TRACE_AddInstrumentFunction(Trace, NULL);
        PIN_AddFiniFunction(Fini, 0);
        out_file << std::setprecision(5);
        out_file.open(filename);

        PIN_StartProgram(); // Never returns
    }

    else if (KnobInst)
    {
        std::cout << "Running instrument..\n";
        IMG_AddInstrumentFunction(ImageLoad, 0);
        PIN_AddFiniFunction(InstFini, 0);
        in_file.open(filename);
        if (!in_file)
        {
            std::cout << "Profiling file (" << filename << ") was not generated. exiting..\n";
            exit(0);
        }
        PIN_StartProgramProbed(); // Never returns
    }

    else
    {
        std::cout << "Regular run..\n";
        Usage();
        PIN_StartProgram(); // Never returns
    }

    return 0;
}
