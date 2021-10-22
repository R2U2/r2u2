#define MUNIT_ENABLE_ASSERT_ALIASES
#include "munit/munit.h"

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

/* Stand-in test */
static MunitResult my_test(const MunitParameter params[], void* user_data) {

  assert_int(1, ==, 1);

  return MUNIT_OK;
}

/* Tests for op_abs_diff_angle */

MunitTest op_abs_diff_angle_tests[] = {
  {
    "/my-test", /* name */
    my_test, /* test */
    NULL, /* setup */
    NULL, /* tear_down */
    MUNIT_TEST_OPTION_NONE, /* options */
    NULL /* parameters */
  },
  /* Mark the end of the array with an entry where the test
   * function is NULL */
  { NULL, NULL, NULL, NULL, MUNIT_TEST_OPTION_NONE, NULL }
};


/* Tests for op_movavg */

MunitTest op_movavg_tests[] = {
  {
    "/my-test", /* name */
    my_test, /* test */
    NULL, /* setup */
    NULL, /* tear_down */
    MUNIT_TEST_OPTION_NONE, /* options */
    NULL /* parameters */
  },
  /* Mark the end of the array with an entry where the test
   * function is NULL */
  { NULL, NULL, NULL, NULL, MUNIT_TEST_OPTION_NONE, NULL }
};


/* Tests for op_rate */

MunitTest op_rate_tests[] = {
  {
    "/my-test", /* name */
    my_test, /* test */
    NULL, /* setup */
    NULL, /* tear_down */
    MUNIT_TEST_OPTION_NONE, /* options */
    NULL /* parameters */
  },
  /* Mark the end of the array with an entry where the test
   * function is NULL */
  { NULL, NULL, NULL, NULL, MUNIT_TEST_OPTION_NONE, NULL }
};


/* Tests for op_bool */

MunitTest op_bool_tests[] = {
  {
    "/my-test", /* name */
    my_test, /* test */
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
    "/my-test", /* name */
    my_test, /* test */
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
    "/my-test", /* name */
    my_test, /* test */
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
    "/my-test", /* name */
    my_test, /* test */
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
    "/my-test", /* name */
    my_test, /* test */
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
  { "/op_abs_diff_angle", op_abs_diff_angle_tests, NULL, 1, MUNIT_SUITE_OPTION_NONE },
  { "/op_movavg", op_movavg_tests, NULL, 1, MUNIT_SUITE_OPTION_NONE },
  { "/op_rate", op_rate_tests, NULL, 1, MUNIT_SUITE_OPTION_NONE },
  { "/op_bool", op_bool_tests, NULL, 1, MUNIT_SUITE_OPTION_NONE },
  { "/op_int", op_int_tests, NULL, 1, MUNIT_SUITE_OPTION_NONE },
  { "/op_double", op_double_tests, NULL, 1, MUNIT_SUITE_OPTION_NONE },
  { "/op_error", op_error_tests, NULL, 1, MUNIT_SUITE_OPTION_NONE },
  { "/decode", decode_tests, NULL, 1, MUNIT_SUITE_OPTION_NONE },
  { NULL, NULL, NULL, 0, MUNIT_SUITE_OPTION_NONE }
};

static const MunitSuite at_operations_suite = {
  "at_operations-tests", /* name */
  NULL, /* tests */
  function_suites, /* suites */
  1, /* iterations */
  MUNIT_SUITE_OPTION_NONE /* options */
};

int main (int argc, const char* argv[]) {
  return munit_suite_main(&at_operations_suite, NULL, argc, argv);
}
