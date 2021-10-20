# filters.py
# Functions here define how to parse arguments for filters
# To add a filter add the name of the filter to the parse_filters dict and
# then define a function which takes the 'arg' list argument and returns a
# binary string of the result

from .config import data
from .util import toBinary

max_const_width = int(data['L_NUM'])

# we use underscores in front of filter names to avoid conflicts with keywords

def _null(args):
    print('ERROR: invalid filter index in call to parse_filter')
    return ''


def _bool(args):
    global max_const_width
    binary = ''
    sig = args[0]

    if sig[0] == 's':
        binary += '1'
        binary += toBinary(sig[1:], max_const_width)
    else:
        binary += '0'
        binary += toBinary(sig, max_const_width)

    return binary


def _int(args):
    global max_const_width
    binary = ''
    sig = args[0]

    if sig[0] == 's':
        binary += '1'
        binary += toBinary(sig[1:], max_const_width)
    else:
        binary += '0'
        binary += toBinary(sig, max_const_width)

    return binary


def _float(args):
    global max_const_width
    binary = ''
    sig = args[0]

    if sig[0] == 's':
        binary += '1'
        binary += toBinary(sig[1:], max_const_width)
    else:
        binary += '0'
        binary += toBinary(sig, max_const_width)

    return binary


def _abs_diff_angle(args):
    global max_const_width
    binary = ''
    sig = args[0]
    const = args[1]

    if sig[0] == 's':
        binary += '1'
        binary += toBinary(sig[1:], max_const_width)
    else:
        binary += '0'
        binary += toBinary(sig, max_const_width)

    binary += toBinary(const, max_const_width)

    return binary


def _rate(args):
    global max_const_width
    binary = ''
    sig = args[0]

    if sig[0] == 's':
        binary += '1'
        binary += toBinary(sig[1:], max_const_width)
    else:
        binary += '0'
        binary += toBinary(sig, max_const_width)

    return binary


def _movavg(args):
    global max_const_width
    binary = ''
    sig = args[0]
    const = args[1]

    if sig[0] == 's':
        binary += '1'
        binary += toBinary(sig[1:], max_const_width)
    else:
        binary += '0'
        binary += toBinary(sig, max_const_width)

    binary += toBinary(const, max_const_width)

    return binary


def _exactly_one_of(args):
    global max_const_width
    binary = ''
    setIdent = args[0]

    binary += toBinary(setIdent[1:], max_const_width)

    return binary


parse_filters = {
    0: _null,
    1: _bool,
    2: _int,
    3: _float,
    4: _abs_diff_angle,
    5: _rate,
    6: _movavg,
    7: _exactly_one_of
}


def valid_filters():
    filters = []
    for idx, filter_func in parse_filters.items():
        filters.append(filter_func.__name__[1:])
    return filters


def parse_filter(filter,args):
    filters = valid_filters()
    return parse_filters[filters.index(filter)](args)