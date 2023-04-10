#include <stdio.h>
#include <stdbool.h>

/* Load unit test framework, without "munit_" prefix on asserts */
#define MUNIT_ENABLE_ASSERT_ALIASES
#include "munit.h"

#include "../src/r2u2.h"

static void* test_setup(const MunitParameter params[], void* user_data) {
    UNUSED(params);
    UNUSED(user_data);

    return NULL;
}

static MunitResult test_libr2u2_init (const MunitParameter params[], void* user_data) {
    UNUSED(params);
    UNUSED(user_data);

    r2u2_init();

    return MUNIT_OK;

}

/* Test runner setup */
static const MunitTest function_tests[] = {
    {
        (char*) "/test_libr2u2_init",
        test_libr2u2_init,
        test_setup,
        NULL,
        MUNIT_TEST_OPTION_NONE,
        NULL
    },
  { NULL, NULL, NULL, NULL, MUNIT_TEST_OPTION_NONE, NULL }
};

static const MunitSuite lib_suite = {
  (char*) "lib", /* name */
  function_tests, /* tests */
  NULL, /* suites */
  1, /* iterations */
  MUNIT_SUITE_OPTION_NONE /* options */
};

int main (int argc, const char* argv[]) {
  return munit_suite_main(&lib_suite, NULL, argc, argv);
}
