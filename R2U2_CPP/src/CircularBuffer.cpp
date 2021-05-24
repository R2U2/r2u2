/*
 * CircularBuffer.cpp
 *
 *  Created on: Jul 25, 2017
 *      Author: PEI
 */
// #include <string>
// #include <vector>
// #include "CircularBuffer.h"
// #include "common.h"
// #include "Observer.h"


// CircularBuffer::CircularBuffer(): wrPtr(0){
// 	// TODO Auto-generated constructor stub

// }

// void CircularBuffer::write(en res) {//write with aggregation
// 	if(res.time_stamp==-1) return;
// 	if(isBottom) atomic.push_back(res);
// 	else{
// 		if(everWrite){
// 			if(res.verdict!=data[preWrPtr()].verdict) wrPtr=wrPtr==circularQueue_size-1?0:wrPtr+1;
// 			data[preWrPtr()]=res;
// 		}else{
// 			data[wrPtr]=res;
// 			wrPtr=wrPtr==circularQueue_size-1?0:wrPtr+1;
// 		}
// 		everWrite=true;
// 	}

// }

// en CircularBuffer::read(int &ptr) {
// 	if(isBottom){
// 		return atomic.at(ptr++);
// 	}else{
// 		return data[ptr];
// 	}
// }

// int CircularBuffer::preWrPtr(){
// 	return wrPtr==0?circularQueue_size-1:wrPtr-1;
// }

// void CircularBuffer::incPtr(int &ptr){
// 	ptr=ptr==circularQueue_size-1?0:ptr+1;
// }

// void CircularBuffer::decPtr(int &ptr){
// 	ptr=ptr==0?circularQueue_size-1:ptr-1;
// }

// void CircularBuffer::debug(){
// 	for(int i=0;i<circularQueue_size;i++) cout<<"CB["<<i<<"]: ("<<data[i].verdict<<","<<data[i].time_stamp<<")"<<endl;
// }

// bool CircularBuffer::isEmpty(int ptr){
// 	return ptr==wrPtr||!everWrite;
// }

// bool CircularBuffer::recedPtr(int ptr){
// 	return ptr==wrPtr&&everWrite;
// }

// CircularBuffer::~CircularBuffer() {
// 	// TODO Auto-generated destructor stub
// }

#include <stdio.h>
#include "CircularBuffer.h"
#include "common.h"

#define AGGREGATION  // do aggregation

using namespace std;

CircularBuffer::CircularBuffer(): size(circularQueue_size){
	queue = new en[size];
	queue[0] = {false,-1};
	for(int i=1;i<size;i++) queue[i]={false,0};
}

CircularBuffer::CircularBuffer(int size): size(size){
	queue = new en[size];
	queue[0] = {false,-1};
	for(int i=1;i<size;i++) queue[i]={false,0};
}


int CircularBuffer::inc_ptr(int ptr) {
	if(ptr==size-1) return 0;
	return ptr+1;
}
int CircularBuffer::dec_ptr(int ptr) {
	if(ptr==0) return size-1;
	return ptr-1;
}

// add new element to the SCQ 
void CircularBuffer::add(en newData) {
	#ifdef AGGREGATION
		if(queue[dec_ptr(wr_ptr)].verdict==newData.verdict &&\
			queue[dec_ptr(wr_ptr)].time_stamp<newData.time_stamp) { // assign to previous address
			queue[dec_ptr(wr_ptr)] = newData;
		} else {
			queue[wr_ptr] = newData;
			wr_ptr = inc_ptr(wr_ptr);
		}
	#else
		queue[wr_ptr] = newData;
		wr_ptr = inc_ptr(wr_ptr);
	#endif
}

bool CircularBuffer::isEmpty(int& rd_ptr, int desired_time_stamp) {
	if(rd_ptr==wr_ptr && queue[rd_ptr].time_stamp>=desired_time_stamp) return false;
	while(rd_ptr!=wr_ptr && queue[rd_ptr].time_stamp<desired_time_stamp) rd_ptr=inc_ptr(rd_ptr);
	if(rd_ptr==wr_ptr) {
		rd_ptr = dec_ptr(rd_ptr);
		return true;
	}
	return false;
}

// bool CircularBuffer::debug_display_queue() {
// 	for(int i=0;i<size;i++) {
		
// 	}
// }

en CircularBuffer::pop(int rd_ptr) {
	return queue[rd_ptr];
}


