import pathlib
import difflib

TEST_DIR = pathlib.Path(__file__).parent

TEST_DIRS = [
    TEST_DIR / "atomic_checkers",
    TEST_DIR / "cse",
    TEST_DIR / "operators",
    TEST_DIR / "set_agg",
    TEST_DIR / "struct",
    TEST_DIR / "type_check"
]

for test_dir in TEST_DIRS:
    pass

