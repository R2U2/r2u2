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

/* op_bool test1 */
static MunitResult op_bool_test1(const MunitParameter params[], void* user_data) {

  at_instruction_t inst = {
    .cond = EQ,
    .filter = OP_BOOL,
    .sig_addr = 0,
    .atom_addr = 1,
    .comp_is_sig = false,
    .comp = 0
  };

  signals_vector[inst.sig_addr] = "0";

  op_double(&inst);

  assert_int(atomics_vector[inst.atom_addr], ==, 1);

  return MUNIT_OK;
}

/* op_int test */
static MunitResult op_int_test(const MunitParameter params[], void* user_data) {

  at_instruction_t inst = {
    .cond = EQ,
    .filter = OP_INT,
    .sig_addr = 0,
    .atom_addr = 1,
    .comp_is_sig = false,
    .comp = 2
  };

  signals_vector[inst.sig_addr] = "2";

  op_double(&inst);

  assert_int(atomics_vector[inst.atom_addr], ==, 1);

  return MUNIT_OK;
}

/* op_double test */
static MunitResult op_double_test(const MunitParameter params[], void* user_data) {

  at_instruction_t inst = {
    .cond = EQ,
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

/* op_error test */
static MunitResult op_error_test(const MunitParameter params[], void* user_data) {

  at_instruction_t inst = {
    .cond = EQ,
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

/* decode test */
static MunitResult decode_test(const MunitParameter params[], void* user_data) {

  at_instruction_t inst = {
    .cond = EQ,
    .filter = OP_DOUBLE,
    .sig_addr = 0,
    .atom_addr = 1,
    .comp_is_sig = false,
    .comp = 7
  };

  signals_vector[inst.sig_addr] = "1.2";

  op_double(&inst);

  assert_int(atomics_vector[inst.atom_addr], ==, 1);

  return MUNIT_OK;
}

/* Tests for op_bool */

MunitTest op_bool_tests[] = {
  {
    "/op_bool_test1", /* name */
    op_bool_test1, /* test */
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

MunitTest op_int_tests[] = {
  {
    "/op_int_test", /* name */
    op_int_test, /* test */
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

MunitTest op_double_tests[] = {
  {
    "/op_double_test", /* name */
    op_double_test, /* test */
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

MunitTest op_error_tests[] = {
  {
    "/op_error_test", /* name */
    op_error_test, /* test */
    NULL, /* setup */
    NULL, /* tear_down */
    MUNIT_TEST_OPTION_NONE, /* options */
    NULL /* parameters */
  },
  /* Mark the end of the array with an entry where the test
   * function is NULL */
  { NULL, NULL, NULL, NULL, MUNIT_TEST_OPTION_NONE, NULL }
};


/* Tests for decode */

MunitTest decode_tests[] = {
  {
    "/decode_test", /* name */
    decode_test, /* test */
    NULL, /* setup */
    NULL, /* tear_down */
    MUNIT_TEST_OPTION_NONE, /* options */
    NULL /* parameters */
  },
  /* Mark the end of the array with an entry where the test
   * function is NULL */
  { NULL, NULL, NULL, NULL, MUNIT_TEST_OPTION_NONE, NULL }
};


/* Test runner setup */

static const MunitSuite function_suites[] = {
  // { "/op_abs_diff_angle", op_abs_diff_angle_tests, NULL, 1, MUNIT_SUITE_OPTION_NONE },
  // { "/op_movavg", op_movavg_tests, NULL, 1, MUNIT_SUITE_OPTION_NONE },
  // { "/op_rate", op_rate_tests, NULL, 1, MUNIT_SUITE_OPTION_NONE },
  { "/op_bool", op_bool_tests, NULL, 1, MUNIT_SUITE_OPTION_NONE },
  { "/op_int", op_int_tests, NULL, 1, MUNIT_SUITE_OPTION_NONE },
  { "/op_double", op_double_tests, NULL, 1, MUNIT_SUITE_OPTION_NONE },
  { "/op_error", op_error_tests, NULL, 1, MUNIT_SUITE_OPTION_NONE },
  { "/decode", decode_tests, NULL, 1, MUNIT_SUITE_OPTION_NONE },
  { NULL, NULL, NULL, 0, MUNIT_SUITE_OPTION_NONE }
};

static const MunitSuite at_operations_suite = {
  "at_operations_tests", /* name */
  NULL, /* tests */
  function_suites, /* suites */
  1, /* iterations */
  MUNIT_SUITE_OPTION_NONE /* options */
};

int main (int argc, const char* argv[]) {
  r2u2_debug_fptr = stderr;
  return munit_suite_main(&at_operations_suite, NULL, argc, argv);
}
