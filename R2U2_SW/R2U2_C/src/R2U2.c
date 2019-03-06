#include <stdio.h>
#include "R2U2Config.h"

#include "TL/TL_observers.h"
#include "AT/at_checkers.h"

int main(int argc, char const *argv[])
{
    printf("Hello, world!\n");
    fprintf(stdout,"%s Version %d.%d\n",
            argv[0],
            R2U2_C_VERSION_MAJOR,
            R2U2_C_VERSION_MINOR);
    return 0;
}