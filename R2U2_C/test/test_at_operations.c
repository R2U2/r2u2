#include <stdio.h>
#include <stdbool.h>

#define MUNIT_ENABLE_ASSERT_ALIASES
#include "munit/munit.h"

#include "../src/AT/at_operations.h"
#include "../src/AT/at_globals.h"
#include "../src/TL/TL_observers.h"

FILE* r2u2_debug_fptr = NULL;

/* Test Suite Layout
**
** This file creates the `test_at_operations` test executable  which runs tests
** for `at_operations.c` which are contained in `at_operations_suite`
**
** To organize the tests, the `at_operations_suite` contains a list of
** sub-suites, `function_suites`, one per function of `at_operations.c`
**
** New tests should be added to the per-function test-suites such as
** `op_rate_tests` which will propagated automatically.
**
*/


/* Tests for op_bool */
static MunitResult op_bool_int_eq_const_test(const MunitParameter params[], void* user_data) {

  at_instruction_t inst = {
    .cond = EQ,
    .filter = OP_BOOL,
    .sig_addr = 0,
    .atom_addr = 1,
    .comp_is_sig = false,
    .comp.b = 0
  };

  signals_vector[inst.sig_addr] = "0";

  op_bool(&inst);

  assert_int(atomics_vector[inst.atom_addr], ==, 1);

  return MUNIT_OK;
}
static MunitResult op_bool_int_eq_int_test(const MunitParameter params[], void* user_data) {

  at_instruction_t inst = {
    .cond = EQ,
    .filter = OP_BOOL,
    .sig_addr = 0,
    .atom_addr = 1,
    .comp_is_sig = true,
    .comp.s = 1
  };

  signals_vector[inst.sig_addr] = "0";
  signals_vector[inst.comp.s] = "0";

  op_bool(&inst);

  assert_int(atomics_vector[inst.atom_addr], ==, 1);

  return MUNIT_OK;
}
MunitTest op_bool_tests[] = {
  {
    "/int_eq_const", /* name */
    op_bool_int_eq_const_test, /* test */
    NULL, /* setup */
    NULL, /* tear_down */
    MUNIT_TEST_OPTION_NONE, /* options */
    NULL /* parameters */
  },
  {
    "/int_eq_int", /* name */
    op_bool_int_eq_int_test, /* test */
    NULL, /* setup */
    NULL, /* tear_down */
    MUNIT_TEST_OPTION_NONE, /* options */
    NULL /* parameters */
  },
  /* Mark the end of the array with an entry where the test
   * function is NULL */
  { NULL, NULL, NULL, NULL, MUNIT_TEST_OPTION_NONE, NULL }
};


/* Tests for op_int */
static MunitResult op_int_int_eq_const_test(const MunitParameter params[], void* user_data) {

  at_instruction_t inst = {
    .cond = EQ,
    .filter = OP_INT,
    .sig_addr = 0,
    .atom_addr = 1,
    .comp_is_sig = false,
    .comp.i = 2
  };

  signals_vector[inst.sig_addr] = "2";

  op_int(&inst);

  assert_int(atomics_vector[inst.atom_addr], ==, 1);

  return MUNIT_OK;
}
static MunitResult op_int_int_eq_int_test(const MunitParameter params[], void* user_data) {

  at_instruction_t inst = {
    .cond = EQ,
    .filter = OP_INT,
    .sig_addr = 0,
    .atom_addr = 1,
    .comp_is_sig = true,
    .comp.s = 1
  };

  signals_vector[inst.sig_addr] = "2";
  signals_vector[inst.comp.s] = "2";

  op_int(&inst);

  assert_int(atomics_vector[inst.atom_addr], ==, 1);

  return MUNIT_OK;
}
MunitTest op_int_tests[] = {
  {
    "/int_eq_const", /* name */
    op_int_int_eq_const_test, /* test */
    NULL, /* setup */
    NULL, /* tear_down */
    MUNIT_TEST_OPTION_NONE, /* options */
    NULL /* parameters */
  },
  {
    "/int_eq_int", /* name */
    op_int_int_eq_int_test, /* test */
    NULL, /* setup */
    NULL, /* tear_down */
    MUNIT_TEST_OPTION_NONE, /* options */
    NULL /* parameters */
  },
  /* Mark the end of the array with an entry where the test
   * function is NULL */
  { NULL, NULL, NULL, NULL, MUNIT_TEST_OPTION_NONE, NULL }
};


/* Tests for op_double */
static MunitResult op_double_int_gt_const_test(const MunitParameter params[], void* user_data) {

  at_instruction_t inst = {
    .cond = GT,
    .filter = OP_DOUBLE,
    .sig_addr = 0,
    .atom_addr = 1,
    .comp_is_sig = false,
    .comp = 7
  };

  signals_vector[inst.sig_addr] = "1234";

  op_double(&inst);

  assert_int(atomics_vector[inst.atom_addr], ==, 1);

  return MUNIT_OK;
}
static MunitResult op_double_sig_eq_sig_test(const MunitParameter params[], void* user_data) {

  at_instruction_t inst = {
    .cond = EQ,
    .filter = OP_DOUBLE,
    .sig_addr = 0,
    .atom_addr = 1,
    .comp_is_sig = true,
    .comp = 1
  };

  signals_vector[inst.sig_addr] = "1234";
  signals_vector[inst.comp.s] = "1234";

  op_double(&inst);

  assert_int(atomics_vector[inst.atom_addr], ==, 1);

  return MUNIT_OK;
}
MunitTest op_double_tests[] = {
  {
    "/int_gt_const", /* name */
    op_double_int_gt_const_test, /* test */
    NULL, /* setup */
    NULL, /* tear_down */
    MUNIT_TEST_OPTION_NONE, /* options */
    NULL /* parameters */
  },
  {
    "/sig_eq_sig", /* name */
    op_double_sig_eq_sig_test, /* test */
    NULL, /* setup */
    NULL, /* tear_down */
    MUNIT_TEST_OPTION_NONE, /* options */
    NULL /* parameters */
  },
  /* Mark the end of the array with an entry where the test
   * function is NULL */
  { NULL, NULL, NULL, NULL, MUNIT_TEST_OPTION_NONE, NULL }
};


/* Tests for op_error */
// static MunitResult op_error_test(const MunitParameter params[], void* user_data) {

//   at_instruction_t inst = {
//     .cond = EQ,
//     .filter = OP_DOUBLE,
//     .sig_addr = 0,
//     .atom_addr = 1,
//     .comp_is_sig = false,
//     .comp = 7
//   };

//   signals_vector[inst.sig_addr] = "1234";

//   op_double(&inst);

//   assert_int(atomics_vector[inst.atom_addr], ==, 1);

//   return MUNIT_OK;
// }
// MunitTest op_error_tests[] = {
//   {
//     "/op_error_test", /* name */
//     op_error_test, /* test */
//     NULL, /* setup */
//     NULL, /* tear_down */
//     MUNIT_TEST_OPTION_NONE, /* options */
//     NULL /* parameters */
//   },
//   /* Mark the end of the array with an entry where the test
//    * function is NULL */
//   { NULL, NULL, NULL, NULL, MUNIT_TEST_OPTION_NONE, NULL }
// };


/* Tests for decode */
// static MunitResult decode_test(const MunitParameter params[], void* user_data) {

//   at_instruction_t inst = {
//     .cond = EQ,
//     .filter = OP_DOUBLE,
//     .sig_addr = 0,
//     .atom_addr = 1,
//     .comp_is_sig = false,
//     .comp = 7
//   };

//   signals_vector[inst.sig_addr] = "1.2";

//   op_double(&inst);

//   assert_int(atomics_vector[inst.atom_addr], ==, 1);

//   return MUNIT_OK;
// }
// MunitTest decode_tests[] = {
//   {
//     "/decode_test", /* name */
//     decode_test, /* test */
//     NULL, /* setup */
//     NULL, /* tear_down */
//     MUNIT_TEST_OPTION_NONE, /* options */
//     NULL /* parameters */
//   },
//   /* Mark the end of the array with an entry where the test
//    * function is NULL */
//   { NULL, NULL, NULL, NULL, MUNIT_TEST_OPTION_NONE, NULL }
// };


/* Test runner setup */

static const MunitSuite function_suites[] = {
  // { "/op_abs_diff_angle", op_abs_diff_angle_tests, NULL, 1, MUNIT_SUITE_OPTION_NONE },
  // { "/op_movavg", op_movavg_tests, NULL, 1, MUNIT_SUITE_OPTION_NONE },
  // { "/op_rate", op_rate_tests, NULL, 1, MUNIT_SUITE_OPTION_NONE },
  { "/op_bool", op_bool_tests, NULL, 1, MUNIT_SUITE_OPTION_NONE },
  { "/op_int", op_int_tests, NULL, 1, MUNIT_SUITE_OPTION_NONE },
  { "/op_double", op_double_tests, NULL, 1, MUNIT_SUITE_OPTION_NONE },
  // { "/op_error", op_error_tests, NULL, 1, MUNIT_SUITE_OPTION_NONE },
  // { "/decode", decode_tests, NULL, 1, MUNIT_SUITE_OPTION_NONE },
  { NULL, NULL, NULL, 0, MUNIT_SUITE_OPTION_NONE }
};

static const MunitSuite at_operations_suite = {
  "at_operations", /* name */
  NULL, /* tests */
  function_suites, /* suites */
  1, /* iterations */
  MUNIT_SUITE_OPTION_NONE /* options */
};

int main (int argc, const char* argv[]) {
  r2u2_debug_fptr = stderr;
  return munit_suite_main(&at_operations_suite, NULL, argc, argv);
}
