#ifndef COMMON_H_
#define COMMON_H_

#include <string>
using namespace std;
typedef	struct{
	int verdict;//0:false, 1:true, 2:maybe
	int time_stamp;
}en;

typedef struct{
	int rdPtr_mem;
	int rdPtr2_mem;
	en result_mem;
}mem;

#endif
