#!/usr/bin/env bash
# collect_coverage_metrics.sh
#
#
#

find $(DBG_PATH) -name "*.gcno" -exec gcov -b -l -p -c {} \; && mv *.gcov $(TST_RPT_PATH)
