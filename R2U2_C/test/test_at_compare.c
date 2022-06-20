#include <stdio.h>

#define MUNIT_ENABLE_ASSERT_ALIASES
#include "munit/munit.h"

#include "../src/AT/at_compare.h"

FILE* r2u2_debug_fptr = NULL;

/* Test Suite Layout
**
** This file creates the `test_at_compare` test executable  which runs tests
** for `at_compare.c` which are contained in `at_compare_suite`
**
** To organize the tests, the `at_compare_suite` contains a list of
** sub-suites, `function_suites`, one per function of `at_compare.c`
**
*/

/* compare_int_eq tests */
static MunitResult compare_int_eq_test(const MunitParameter params[], void* user_data) {

  assert_int(compare_int_eq(1,1), ==, 1);
  assert_int(compare_int_eq(1,-1), ==, 0);
  assert_int(compare_int_eq(1,0), ==, 0);
  assert_int(compare_int_eq(1.5,1), ==, 1);
  assert_int(compare_int_eq(-1,-1), ==, 1);
  assert_int(compare_int_eq(0,0), ==, 1);
  assert_int(compare_int_eq(-0,0), ==, 1);
  assert_int(compare_int_eq(-0,+0), ==, 1);
  assert_int(compare_int_eq(2.5,2.5), ==, 1);
  assert_int(compare_int_eq(1.0,1), ==, 1);

  return MUNIT_OK;
}

/* compare_int_neq tests */
static MunitResult compare_int_neq_test(const MunitParameter params[], void* user_data) {

  assert_int(compare_int_neq(1,1), ==, 0);
  assert_int(compare_int_neq(1,-1), ==, 1);
  assert_int(compare_int_neq(1,0), ==, 1);
  assert_int(compare_int_neq(1.5,1), ==, 0);
  assert_int(compare_int_neq(-1,-1), ==, 0);
  assert_int(compare_int_neq(0,0), ==, 0);
  assert_int(compare_int_neq(-0,0), ==, 0);
  assert_int(compare_int_neq(-0,+0), ==, 0);
  assert_int(compare_int_neq(2.5,2.5), ==, 0);
  assert_int(compare_int_neq(1.0,1), ==, 0);

  return MUNIT_OK;
}

/* compare_int_lt tests */
static MunitResult compare_int_lt_test(const MunitParameter params[], void* user_data) {

  assert_int(compare_int_lt(1,1), ==, 0);
  assert_int(compare_int_lt(-1,1), ==, 1);
  assert_int(compare_int_lt(1,0), ==, 0);
  assert_int(compare_int_lt(1.5,1), ==, 0);
  assert_int(compare_int_lt(-1,-1), ==, 0);
  assert_int(compare_int_lt(0,0), ==, 0);
  assert_int(compare_int_lt(-0,0), ==, 0);
  assert_int(compare_int_lt(1.5,2.0), ==, 1);
  assert_int(compare_int_lt(1.0,1), ==, 0);
  assert_int(compare_int_lt(2,4), ==, 1);

  return MUNIT_OK;
}

/* compare_int_leq tests */
static MunitResult compare_int_leq_test(const MunitParameter params[], void* user_data) {

  assert_int(compare_int_leq(1,1), ==, 1);
  assert_int(compare_int_leq(-1,1), ==, 1);
  assert_int(compare_int_leq(1,0), ==, 0);
  assert_int(compare_int_leq(1.5,1), ==, 1);
  assert_int(compare_int_leq(-1,-1), ==, 1);
  assert_int(compare_int_leq(0,0), ==, 1);
  assert_int(compare_int_leq(-0,0), ==, 1);
  assert_int(compare_int_leq(2.5,2.5), ==, 1);
  assert_int(compare_int_leq(1.0,1), ==, 1);
  assert_int(compare_int_leq(2,4), ==, 1);

  return MUNIT_OK;
}

/* compare_int_gt tests */
static MunitResult compare_int_gt_test(const MunitParameter params[], void* user_data) {

  assert_int(compare_int_gt(1,1), ==, 0);
  assert_int(compare_int_gt(1,-1), ==, 1);
  assert_int(compare_int_gt(1,0), ==, 1);
  assert_int(compare_int_gt(1.5,1), ==, 0);
  assert_int(compare_int_gt(-1,-1), ==, 0);
  assert_int(compare_int_gt(0,0), ==, 0);
  assert_int(compare_int_gt(-0,0), ==, 0);
  assert_int(compare_int_gt(2.5,2.5), ==, 0);
  assert_int(compare_int_gt(1.0,1), ==, 0);
  assert_int(compare_int_gt(4,1), ==, 1);
  assert_int(compare_int_gt(2,-3), ==, 1);

  return MUNIT_OK;
}

/* compare_int_geq tests */
static MunitResult compare_int_geq_test(const MunitParameter params[], void* user_data) {

  assert_int(compare_int_geq(1,1), ==, 1);
  assert_int(compare_int_geq(-1,1), ==, 0);
  assert_int(compare_int_geq(1,0), ==, 1);
  assert_int(compare_int_geq(1.5,1), ==, 1);
  assert_int(compare_int_geq(1,1.7), ==, 1);
  assert_int(compare_int_geq(-1,-1), ==, 1);
  assert_int(compare_int_geq(0,0), ==, 1);
  assert_int(compare_int_geq(-0,0), ==, 1);
  assert_int(compare_int_geq(2.5,2.5), ==, 1);
  assert_int(compare_int_geq(1.0,1), ==, 1);
  assert_int(compare_int_geq(2,4), ==, 0);

  return MUNIT_OK;
}

/* compare_int tests */
static MunitResult compare_int_test(const MunitParameter params[], void* user_data) {

  assert_int(compare_int[0](1,1), ==, 1);
  assert_int(compare_int[1](1,1), ==, 0);
  assert_int(compare_int[2](1,1), ==, 0);
  assert_int(compare_int[3](1,1), ==, 1);
  assert_int(compare_int[4](1,1), ==, 0);
  assert_int(compare_int[5](1,1), ==, 1);

  return MUNIT_OK;
}

/* compare_double_eq tests */
static MunitResult compare_double_eq_test(const MunitParameter params[], void* user_data) {

  assert_int(compare_double_eq(1.0,1.0), ==, 1);
  assert_int(compare_double_eq(1.2,-1.2), ==, 0);
  assert_int(compare_double_eq(1.5,0), ==, 0);
  assert_int(compare_double_eq(1.5,1.0), ==, 0);
  assert_int(compare_double_eq(-1.4,-1.4), ==, 1);
  assert_int(compare_double_eq(0,0), ==, 1);
  assert_int(compare_double_eq(-0,0), ==, 1);
  assert_int(compare_double_eq(2.5,2.5), ==, 1);
  assert_int(compare_double_eq(1.0,1), ==, 1);
  assert_int(compare_double_eq(3.0,-3), ==, 0);

  return MUNIT_OK;
}

/* compare_double_neq tests */
static MunitResult compare_double_neq_test(const MunitParameter params[], void* user_data) {

  assert_int(compare_double_neq(1.1,1.3), ==, 1);
  assert_int(compare_double_neq(1.0,-1.0), ==, 1);
  assert_int(compare_double_neq(2.0,2.0), ==, 0);
  assert_int(compare_double_neq(1.5,1), ==, 1);
  assert_int(compare_double_neq(-1,-1), ==, 0);
  assert_int(compare_double_neq(0,0), ==, 0);
  assert_int(compare_double_neq(-0,0), ==, 0);
  assert_int(compare_double_neq(2.5,2.5), ==, 0);
  assert_int(compare_double_neq(-3.0,3.0), ==, 1);

  return MUNIT_OK;
}

/* compare_double_lt tests */
static MunitResult compare_double_lt_test(const MunitParameter params[], void* user_data) {

  assert_int(compare_double_lt(1.0,1.0), ==, 0);
  assert_int(compare_double_lt(1.3,1.5), ==, 1);
  assert_int(compare_double_lt(0,-1), ==, 0);
  assert_int(compare_double_lt(1.5,1), ==, 0);
  assert_int(compare_double_lt(-1.3,-1.3), ==, 0);
  assert_int(compare_double_lt(0,0), ==, 0);
  assert_int(compare_double_lt(-0,0), ==, 0);
  assert_int(compare_double_lt(2.5,2.5), ==, 0);
  assert_int(compare_double_lt(-4.5,4), ==, 1);
  assert_int(compare_double_lt(-4.5,4.5), ==, 1);

  return MUNIT_OK;
}

/* compare_double_leq tests */
static MunitResult compare_double_leq_test(const MunitParameter params[], void* user_data) {

  assert_int(compare_double_leq(2.0,2.0), ==, 1);
  assert_int(compare_double_leq(1,-1), ==, 0);
  assert_int(compare_double_leq(1.5,0.5), ==, 0);
  assert_int(compare_double_leq(-1.4,-0.5), ==, 1);
  assert_int(compare_double_leq(-1,-1), ==, 1);
  assert_int(compare_double_leq(0,0), ==, 1);
  assert_int(compare_double_leq(-0,0), ==, 1);
  assert_int(compare_double_leq(-0,+0), ==, 1);
  assert_int(compare_double_leq(2.5,2.5), ==, 1);
  assert_int(compare_double_leq(1.0,1), ==, 1);
  assert_int(compare_double_leq(2.6,1), ==, 0);

  return MUNIT_OK;
}

/* compare_double_gt tests */
static MunitResult compare_double_gt_test(const MunitParameter params[], void* user_data) {

  assert_int(compare_double_gt(1.3,1.3), ==, 0);
  assert_int(compare_double_gt(1.4,-1.4), ==, 1);
  assert_int(compare_double_gt(4.5,0), ==, 1);
  assert_int(compare_double_gt(1.5,1), ==, 1);
  assert_int(compare_double_gt(-1,-1), ==, 0);
  assert_int(compare_double_gt(0,0), ==, 0);
  assert_int(compare_double_gt(-0,0), ==, 0);
  assert_int(compare_double_gt(2.6,2.5), ==, 1);
  assert_int(compare_double_gt(1.0,1), ==, 0);
  assert_int(compare_double_gt(-3.2,1.3), ==, 0);

  return MUNIT_OK;
}

/* compare_double_geq tests */
static MunitResult compare_double_geq_test(const MunitParameter params[], void* user_data) {

  assert_int(compare_double_geq(1.2,1.2), ==, 1);
  assert_int(compare_double_geq(2.4,-2.4), ==, 1);
  assert_int(compare_double_geq(3.7,0), ==, 1);
  assert_int(compare_double_geq(1,1.5), ==, 0);
  assert_int(compare_double_geq(-1,-1), ==, 1);
  assert_int(compare_double_geq(0,0), ==, 1);
  assert_int(compare_double_geq(0,+0), ==, 1);
  assert_int(compare_double_geq(5.4,5.0), ==, 1);
  assert_int(compare_double_geq(1.0,1), ==, 1);
  assert_int(compare_double_geq(-2.3,1.2), ==, 0);

  return MUNIT_OK;
}

/* compare_double_geq tests */
static MunitResult compare_double_test(const MunitParameter params[], void* user_data) {

  assert_int(compare_double[0](1.2,1.2), ==, 1);
  assert_int(compare_double[1](1.2,1.2), ==, 0);
  assert_int(compare_double[2](1.2,1.2), ==, 0);
  assert_int(compare_double[3](1.2,1.2), ==, 1);
  assert_int(compare_double[4](1.2,1.2), ==, 0);
  assert_int(compare_double[5](1.2,1.2), ==, 1);

  return MUNIT_OK;
}
/* Tests for compare_int_eq */

MunitTest compare_int_eq_tests[] = {
  {
    "/compare_int_eq_test", /* name */
    compare_int_eq_test, /* test */
    NULL, /* setup */
    NULL, /* tear_down */
    MUNIT_TEST_OPTION_NONE, /* options */
    NULL /* parameters */
  },
  /* Mark the end of the array with an entry where the test
   * function is NULL */
  { NULL, NULL, NULL, NULL, MUNIT_TEST_OPTION_NONE, NULL }
};


/* Tests for compare_int_neq */

MunitTest compare_int_neq_tests[] = {
  {
    "/compare_int_eq_test", /* name */
    compare_int_neq_test, /* test */
    NULL, /* setup */
    NULL, /* tear_down */
    MUNIT_TEST_OPTION_NONE, /* options */
    NULL /* parameters */
  },
  /* Mark the end of the array with an entry where the test
   * function is NULL */
  { NULL, NULL, NULL, NULL, MUNIT_TEST_OPTION_NONE, NULL }
};


/* Tests for compare_int_lt */

MunitTest compare_int_lt_tests[] = {
  {
    "/compare_int_lt_test", /* name */
    compare_int_lt_test, /* test */
    NULL, /* setup */
    NULL, /* tear_down */
    MUNIT_TEST_OPTION_NONE, /* options */
    NULL /* parameters */
  },
  /* Mark the end of the array with an entry where the test
   * function is NULL */
  { NULL, NULL, NULL, NULL, MUNIT_TEST_OPTION_NONE, NULL }
};


/* Tests for compare_int_leq */

MunitTest compare_int_leq_tests[] = {
  {
    "/compare_int_leq_test", /* name */
    compare_int_leq_test, /* test */
    NULL, /* setup */
    NULL, /* tear_down */
    MUNIT_TEST_OPTION_NONE, /* options */
    NULL /* parameters */
  },
  /* Mark the end of the array with an entry where the test
   * function is NULL */
  { NULL, NULL, NULL, NULL, MUNIT_TEST_OPTION_NONE, NULL }
};


/* Tests for compare_int_gt */

MunitTest compare_int_gt_tests[] = {
  {
    "/compare_int_gt_test", /* name */
    compare_int_gt_test, /* test */
    NULL, /* setup */
    NULL, /* tear_down */
    MUNIT_TEST_OPTION_NONE, /* options */
    NULL /* parameters */
  },
  /* Mark the end of the array with an entry where the test
   * function is NULL */
  { NULL, NULL, NULL, NULL, MUNIT_TEST_OPTION_NONE, NULL }
};


/* Tests for compare_int_geq */

MunitTest compare_int_geq_tests[] = {
  {
    "/compare_int_geq_test", /* name */
    compare_int_geq_test, /* test */
    NULL, /* setup */
    NULL, /* tear_down */
    MUNIT_TEST_OPTION_NONE, /* options */
    NULL /* parameters */
  },
  /* Mark the end of the array with an entry where the test
   * function is NULL */
  { NULL, NULL, NULL, NULL, MUNIT_TEST_OPTION_NONE, NULL }
};

/* Tests for compare_int */

MunitTest compare_int_tests[] = {
  {
    "/compare_int_test", /* name */
    compare_int_test, /* test */
    NULL, /* setup */
    NULL, /* tear_down */
    MUNIT_TEST_OPTION_NONE, /* options */
    NULL /* parameters */
  },
  /* Mark the end of the array with an entry where the test
   * function is NULL */
  { NULL, NULL, NULL, NULL, MUNIT_TEST_OPTION_NONE, NULL }
};

/* Tests for compare_double_eq */

MunitTest compare_double_eq_tests[] = {
  {
    "/compare_double_eq_test", /* name */
    compare_double_eq_test, /* test */
    NULL, /* setup */
    NULL, /* tear_down */
    MUNIT_TEST_OPTION_NONE, /* options */
    NULL /* parameters */
  },
  /* Mark the end of the array with an entry where the test
   * function is NULL */
  { NULL, NULL, NULL, NULL, MUNIT_TEST_OPTION_NONE, NULL }
};

/* Tests for compare_double_neq */

MunitTest compare_double_neq_tests[] = {
  {
    "/compare_double_neq_test", /* name */
    compare_double_neq_test, /* test */
    NULL, /* setup */
    NULL, /* tear_down */
    MUNIT_TEST_OPTION_NONE, /* options */
    NULL /* parameters */
  },
  /* Mark the end of the array with an entry where the test
   * function is NULL */
  { NULL, NULL, NULL, NULL, MUNIT_TEST_OPTION_NONE, NULL }
};

/* Tests for compare_double_lt */

MunitTest compare_double_lt_tests[] = {
  {
    "/compare_double_lt_test", /* name */
    compare_double_lt_test, /* test */
    NULL, /* setup */
    NULL, /* tear_down */
    MUNIT_TEST_OPTION_NONE, /* options */
    NULL /* parameters */
  },
  /* Mark the end of the array with an entry where the test
   * function is NULL */
  { NULL, NULL, NULL, NULL, MUNIT_TEST_OPTION_NONE, NULL }
};

/* Tests for compare_double_leq */

MunitTest compare_double_leq_tests[] = {
  {
    "/compare_double_leq_test", /* name */
    compare_double_leq_test, /* test */
    NULL, /* setup */
    NULL, /* tear_down */
    MUNIT_TEST_OPTION_NONE, /* options */
    NULL /* parameters */
  },
  /* Mark the end of the array with an entry where the test
   * function is NULL */
  { NULL, NULL, NULL, NULL, MUNIT_TEST_OPTION_NONE, NULL }
};

/* Tests for compare_double_gt */

MunitTest compare_double_gt_tests[] = {
  {
    "/compare_double_gt_test", /* name */
    compare_double_gt_test, /* test */
    NULL, /* setup */
    NULL, /* tear_down */
    MUNIT_TEST_OPTION_NONE, /* options */
    NULL /* parameters */
  },
  /* Mark the end of the array with an entry where the test
   * function is NULL */
  { NULL, NULL, NULL, NULL, MUNIT_TEST_OPTION_NONE, NULL }
};

/* Tests for compare_double_geq */

MunitTest compare_double_geq_tests[] = {
  {
    "/compare_double_geq_test", /* name */
    compare_double_geq_test, /* test */
    NULL, /* setup */
    NULL, /* tear_down */
    MUNIT_TEST_OPTION_NONE, /* options */
    NULL /* parameters */
  },
  /* Mark the end of the array with an entry where the test
   * function is NULL */
  { NULL, NULL, NULL, NULL, MUNIT_TEST_OPTION_NONE, NULL }
};

/* Tests for compare_double */

MunitTest compare_double_tests[] = {
  {
    "/compare_double_test", /* name */
    compare_double_test, /* test */
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
  { "/compare_int_eq", compare_int_eq_tests, NULL, 1, MUNIT_SUITE_OPTION_NONE },
  { "/compare_int_neq", compare_int_neq_tests, NULL, 1, MUNIT_SUITE_OPTION_NONE },
  { "/compare_int_lt", compare_int_lt_tests, NULL, 1, MUNIT_SUITE_OPTION_NONE },
  { "/compare_int_leq", compare_int_leq_tests, NULL, 1, MUNIT_SUITE_OPTION_NONE },
  { "/compare_int_gt", compare_int_gt_tests, NULL, 1, MUNIT_SUITE_OPTION_NONE },
  { "/compare_int_geq", compare_int_geq_tests, NULL, 1, MUNIT_SUITE_OPTION_NONE },
  { "/compare_int", compare_int_tests, NULL, 1, MUNIT_SUITE_OPTION_NONE },
  { "/compare_double_eq", compare_double_eq_tests, NULL, 1, MUNIT_SUITE_OPTION_NONE },
  { "/compare_double_neq", compare_double_neq_tests, NULL, 1, MUNIT_SUITE_OPTION_NONE },
  { "/compare_double_lt", compare_double_lt_tests, NULL, 1, MUNIT_SUITE_OPTION_NONE },
  { "/compare_double_leq", compare_double_leq_tests, NULL, 1, MUNIT_SUITE_OPTION_NONE },
  { "/compare_double_gt", compare_double_gt_tests, NULL, 1, MUNIT_SUITE_OPTION_NONE },
  { "/compare_double_geq", compare_double_geq_tests, NULL, 1, MUNIT_SUITE_OPTION_NONE },
  { "/compare_double", compare_double_tests, NULL, 1, MUNIT_SUITE_OPTION_NONE },
  { NULL, NULL, NULL, 0, MUNIT_SUITE_OPTION_NONE }
};

static const MunitSuite at_compare_suite = {
  "at_compare_tests", /* name */
  NULL, /* tests */
  function_suites, /* suites */
  1, /* iterations */
  MUNIT_SUITE_OPTION_NONE /* options */
};

int main (int argc, const char* argv[]) {
  r2u2_debug_fptr = stderr;
  return munit_suite_main(&at_compare_suite, NULL, argc, argv);
}
