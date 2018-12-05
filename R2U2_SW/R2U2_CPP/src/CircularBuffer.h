/*
 * CircularBuffer.h
 *
 *  Created on: Jul 25, 2017
 *      Author: PEI
 */
#ifndef SRC_CIRCULARBUFFER_H_
#define SRC_CIRCULARBUFFER_H_

#define circularQueue_size 32
#include <vector>
#include "common.h"

class CircularBuffer {
public:
	CircularBuffer();
	virtual ~CircularBuffer();
	void write(en);
	en read(int&);//read from observer
	en read();//read from sensor(only for load operation)
	bool isEmpty(int);
	en peek(int);
	void incPtr(int&);
	void decPtr(int&);
	int preWrPtr();
	bool recedPtr(int);
	void debug();

public:
	en data[circularQueue_size];
	int wrPtr;
	std::vector<en> atomic;
	bool isBottom=false;
	bool everWrite=false;
};


#endif /* SRC_CIRCULARBUFFER_H_ */
