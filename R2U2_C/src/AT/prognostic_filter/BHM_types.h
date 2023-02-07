/* 
 * File: BHM_types.h 
 *  
 * MATLAB Coder version            : 2.7 
 * C/C++ source code generated on  : 02-Apr-2015 17:30:11 
 */

#ifndef __BHM_TYPES_H__
#define __BHM_TYPES_H__

/* Include Files */ 
#include "rtwtypes.h"

/* Type Definitions */ 
#include <stdio.h>
#ifndef struct_emxArray__common
#define struct_emxArray__common
struct emxArray__common
{
    void *data;
    int *size;
    int allocatedSize;
    int numDimensions;
    boolean_T canFreeData;
};
#endif /*struct_emxArray__common*/
#ifndef typedef_emxArray__common
#define typedef_emxArray__common
typedef struct emxArray__common emxArray__common;
#endif /*typedef_emxArray__common*/
#ifndef struct_emxArray_boolean_T
#define struct_emxArray_boolean_T
struct emxArray_boolean_T
{
    boolean_T *data;
    int *size;
    int allocatedSize;
    int numDimensions;
    boolean_T canFreeData;
};
#endif /*struct_emxArray_boolean_T*/
#ifndef typedef_emxArray_boolean_T
#define typedef_emxArray_boolean_T
typedef struct emxArray_boolean_T emxArray_boolean_T;
#endif /*typedef_emxArray_boolean_T*/
#ifndef struct_emxArray_int32_T
#define struct_emxArray_int32_T
struct emxArray_int32_T
{
    int *data;
    int *size;
    int allocatedSize;
    int numDimensions;
    boolean_T canFreeData;
};
#endif /*struct_emxArray_int32_T*/
#ifndef typedef_emxArray_int32_T
#define typedef_emxArray_int32_T
typedef struct emxArray_int32_T emxArray_int32_T;
#endif /*typedef_emxArray_int32_T*/
#ifndef struct_emxArray_int32_T_1x2
#define struct_emxArray_int32_T_1x2
struct emxArray_int32_T_1x2
{
    int data[2];
    int size[2];
};
#endif /*struct_emxArray_int32_T_1x2*/
#ifndef typedef_emxArray_int32_T_1x2
#define typedef_emxArray_int32_T_1x2
typedef struct emxArray_int32_T_1x2 emxArray_int32_T_1x2;
#endif /*typedef_emxArray_int32_T_1x2*/
#ifndef struct_emxArray_real_T
#define struct_emxArray_real_T
struct emxArray_real_T
{
    double *data;
    int *size;
    int allocatedSize;
    int numDimensions;
    boolean_T canFreeData;
};
#endif /*struct_emxArray_real_T*/
#ifndef typedef_emxArray_real_T
#define typedef_emxArray_real_T
typedef struct emxArray_real_T emxArray_real_T;
#endif /*typedef_emxArray_real_T*/
#ifndef struct_emxArray_real_T_2
#define struct_emxArray_real_T_2
struct emxArray_real_T_2
{
    double data[2];
    int size[1];
};
#endif /*struct_emxArray_real_T_2*/
#ifndef typedef_emxArray_real_T_2
#define typedef_emxArray_real_T_2
typedef struct emxArray_real_T_2 emxArray_real_T_2;
#endif /*typedef_emxArray_real_T_2*/
#ifndef struct_emxArray_real_T_2x1
#define struct_emxArray_real_T_2x1
struct emxArray_real_T_2x1
{
    double data[2];
    int size[2];
};
#endif /*struct_emxArray_real_T_2x1*/
#ifndef typedef_emxArray_real_T_2x1
#define typedef_emxArray_real_T_2x1
typedef struct emxArray_real_T_2x1 emxArray_real_T_2x1;
#endif /*typedef_emxArray_real_T_2x1*/
#ifndef struct_emxArray_real_T_2x2
#define struct_emxArray_real_T_2x2
struct emxArray_real_T_2x2
{
    double data[4];
    int size[2];
};
#endif /*struct_emxArray_real_T_2x2*/
#ifndef typedef_emxArray_real_T_2x2
#define typedef_emxArray_real_T_2x2
typedef struct emxArray_real_T_2x2 emxArray_real_T_2x2;
#endif /*typedef_emxArray_real_T_2x2*/

#endif
/* 
 * File trailer for BHM_types.h 
 *  
 * [EOF] 
 */
