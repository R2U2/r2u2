#!/usr/bin/env bash

find ./bin/test -maxdepth 1 -type f -name 'test_*' -exec {} \;
