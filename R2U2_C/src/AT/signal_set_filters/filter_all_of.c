
#include "filter_all_of.h"

bool filter_all_of(bool *set, uint8_t len)
{
    uint8_t i;

    for(i = 0; i < len; i++) {
        if(!set[i]) return 0;
    }

    return 1;
}
