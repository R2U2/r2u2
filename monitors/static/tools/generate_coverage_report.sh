#!/usr/bin/env bash

gcovr -g -k -r $(SRC_PATH) -e '.*_pt\.c' $(TST_RPT_PATH) --html --html-details -o $(TST_RPT_PATH)/index.html
