#include "r2u2.h"

#include "atomic_checker.h"

extern r2u2_bool (*r2u2_at_compare_int[])(r2u2_int, r2u2_int);
extern r2u2_bool (*r2u2_at_compare_float[])(r2u2_float, r2u2_float, r2u2_float);
extern r2u2_status_t (*r2u2_at_decode[])(r2u2_monitor_t*, r2u2_at_instruction_t *);

r2u2_status_t r2u2_at_instruction_dispatch(r2u2_monitor_t *monitor, r2u2_at_instruction_t *instr) {

  // Copy to buffer to avoid alignment issues
  // TODO(bckempa): Make this optional based on bin packing switch
  r2u2_at_instruction_t inst_buff;
  memcpy(&inst_buff, instr, sizeof(r2u2_at_instruction_t));

  R2U2_DEBUG_PRINT("\tSig# %d -> Filt# %d-> Comp# %d -> Atom#: %d\n",
                   inst_buff.sig_addr, inst_buff.filter,
                   inst_buff.conditional, inst_buff.atom_addr);
  return r2u2_at_decode[inst_buff.filter](monitor, &inst_buff);
}
