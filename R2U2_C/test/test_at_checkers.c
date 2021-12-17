#include <stdio.h>

#define MUNIT_ENABLE_ASSERT_ALIASES
#include "munit/munit.h"

#include "../src/AT/at_globals.h"
#include "../src/AT/at_checkers.h"

FILE* r2u2_debug_fptr = NULL;

/* Test Suite Layout
**
** This file creates the `test_at_checkers` test executable  which runs tests
** for `at_checkers.c` which are contained in `at_checkers_suite`
**
** To organize the tests, the `at_checkers_suite` contains a list of
** sub-suites, `function_suites`, one per function of `at_checkers.c`
**
*/

/* Tests for at_config */
static MunitResult at_config_call(const MunitParameter params[], void* user_data){
    /* AT_config delegates to parse.c, just test API */

    AT_config(NULL);

    return MUNIT_OK;
}

MunitTest at_config_tests[] = {
  {
    "/callable",            /* name */
    at_config_call,         /* test */
    NULL,                   /* setup */
    NULL,                   /* tear_down */
    MUNIT_TEST_OPTION_NONE, /* options */
    NULL                    /* parameters */
  },
  /* Terminate array with an entry where the test is function is NULL */
  { NULL, NULL, NULL, NULL, MUNIT_TEST_OPTION_NONE, NULL }
};

/* Tests for at_init */
static MunitResult at_init_call(const MunitParameter params[], void* user_data){
    /* at_init currently doesn't do anything, but it is in the API */

    AT_init();

    return MUNIT_OK;
}

MunitTest at_init_tests[] = {
  {
    "/callable",            /* name */
    at_init_call,         /* test */
    NULL,                   /* setup */
    NULL,                   /* tear_down */
    MUNIT_TEST_OPTION_NONE, /* options */
    NULL                    /* parameters */
  },
  /* Terminate array with an entry where the test is function is NULL */
  { NULL, NULL, NULL, NULL, MUNIT_TEST_OPTION_NONE, NULL }
};

/* Tests for at_update */
static MunitResult at_update_call(const MunitParameter params[], void* user_data){

    /* Set number of AT instructions to zero */
    num_instr = 0;

    AT_update();

    return MUNIT_OK;
}

static MunitResult at_update_one_loop(const MunitParameter params[], void* user_data){
    /* Without mocking we'll have to defer to testing on decode itself */

    /* Set number of AT instructions to one */
    num_instr = 1;

    AT_update();

    return MUNIT_OK;
}

MunitTest at_update_tests[] = {
  {
    "/callable", /* name */
    at_update_call, /* test */
    NULL, /* setup */
    NULL, /* tear_down */
    MUNIT_TEST_OPTION_NONE, /* options */
    NULL /* parameters */
  },
  {
    "/one_loop", /* name */
    at_update_one_loop, /* test */
    NULL, /* setup */
    NULL, /* tear_down */
    MUNIT_TEST_OPTION_NONE, /* options */
    NULL /* parameters */
  },
  /* Terminate array with an entry where the test is function is NULL */
  { NULL, NULL, NULL, NULL, MUNIT_TEST_OPTION_NONE, NULL }
};

/* Tests for at_free */
static MunitResult at_free_call(const MunitParameter params[], void* user_data){

    AT_free();

    return MUNIT_OK;
}

MunitTest at_free_tests[] = {
  {
    "/callable", /* name */
    at_free_call, /* test */
    NULL, /* setup */
    NULL, /* tear_down */
    MUNIT_TEST_OPTION_NONE, /* options */
    NULL /* parameters */
  },
  /* Terminate array with an entry where the test is function is NULL */
  { NULL, NULL, NULL, NULL, MUNIT_TEST_OPTION_NONE, NULL }
};

/* Test runner setup */
static const MunitSuite function_suites[] = {
  { "/at_config", at_config_tests, NULL, 1, MUNIT_SUITE_OPTION_NONE },
  { "/at_init", at_init_tests, NULL, 1, MUNIT_SUITE_OPTION_NONE },
  { "/at_updates", at_update_tests, NULL, 1, MUNIT_SUITE_OPTION_NONE },
  { "/at_free", at_free_tests, NULL, 1, MUNIT_SUITE_OPTION_NONE },
  { NULL, NULL, NULL, 0, MUNIT_SUITE_OPTION_NONE }
};

static const MunitSuite at_checkers_suite = {
  "at_checkers",          /* name */
  NULL,                   /* tests */
  function_suites,        /* suites */
  1,                      /* iterations */
  MUNIT_SUITE_OPTION_NONE /* options */
};

int main (int argc, const char* argv[]) {
  return munit_suite_main(&at_checkers_suite, NULL, argc, argv);
}
