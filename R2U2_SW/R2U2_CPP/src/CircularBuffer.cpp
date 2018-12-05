/*
 * CircularBuffer.cpp
 *
 *  Created on: Jul 25, 2017
 *      Author: PEI
 */
#include <string>
#include <vector>
#include "CircularBuffer.h"
#include "Observer.h"
#include "common.h"

CircularBuffer::CircularBuffer(): wrPtr(0){
	// TODO Auto-generated constructor stub

}

void CircularBuffer::write(en res) {//write with aggregation
	if(res.time_stamp==-1) return;
	if(isBottom) atomic.push_back(res);
	else{
		if(everWrite){
			if(res.verdict!=data[preWrPtr()].verdict) wrPtr=wrPtr==circularQueue_size-1?0:wrPtr+1;
			data[preWrPtr()]=res;
		}else{
			data[wrPtr]=res;
			wrPtr=wrPtr==circularQueue_size-1?0:wrPtr+1;
		}
		everWrite=true;
	}

}

en CircularBuffer::read(int &ptr) {
	if(isBottom){
		return atomic.at(ptr++);
	}else{
		return data[ptr];
	}
}

int CircularBuffer::preWrPtr(){
	return wrPtr==0?circularQueue_size-1:wrPtr-1;
}

void CircularBuffer::incPtr(int &ptr){
	ptr=ptr==circularQueue_size-1?0:ptr+1;
}

void CircularBuffer::decPtr(int &ptr){
	ptr=ptr==0?circularQueue_size-1:ptr-1;
}

void CircularBuffer::debug(){
	for(int i=0;i<circularQueue_size;i++) cout<<"CB["<<i<<"]: ("<<data[i].verdict<<","<<data[i].time_stamp<<")"<<endl;
}

bool CircularBuffer::isEmpty(int ptr){
	return ptr==wrPtr||!everWrite;
}

bool CircularBuffer::recedPtr(int ptr){
	return ptr==wrPtr&&everWrite;
}

CircularBuffer::~CircularBuffer() {
	// TODO Auto-generated destructor stub
}

