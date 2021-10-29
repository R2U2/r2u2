
#include "filter_exactly_one_of.h"

bool filter_exactly_one_of(bool *set, size_t len)
{
    bool res = 0;
    int i;
    for(i = 0; i < len; i++) {
        if(res && set[i]) return 0;
        res = res || set[i];
    }
    return res;
}
