# C2PO Test Framework

C2PO uses [pytest](https://docs.pytest.org/en/7.4.x/) as its testing framework. To run it, first install `pytest` via

    pip install pytest

then the run the test suite from `r2u2/compiler/test` by calling

    pytest test.py

End-to-end tests that interface with R2U2 are run as part of the larger repo-wide test framework, these tests exercise the various classes and functions internal to C2PO.