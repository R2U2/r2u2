//all the attributes of observers
#include "Observer.h"
#include <iostream>
#include <string>
#include "common.h"
using namespace std;
//constructor
Observer::Observer():child_observer_1(NULL),child_observer_2(NULL){};

Observer::Observer(Observer *cob1, Observer *cob2):child_observer_1(cob1),child_observer_2(cob2){}

Observer::Observer(Observer *cob):child_observer_1(cob),child_observer_2(NULL){}

//bool Observer::is_positive_edge_occur(en pre, en pos){
//	return pos.verdict==1&&pre.verdict==0;
//}
//
//bool Observer::is_negative_edge_occur(en pre, en pos){
//	return pre.verdict==1&&pos.verdict==0;
//}


//support functions
//string verdict_interprete(int num){
//	switch(num){
//		case -1: return "_____";
// 		case 0: return "FALSE";
//		case 1: return "TRUE ";
//		case 2: return "MAYBE";
//		default: return "ERROR";
//	}
//}

