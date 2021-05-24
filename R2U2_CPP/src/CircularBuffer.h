/*
 * CircularBuffer.h
 *
 *  Created on: Jul 25, 2017
 *      Author: PEI
 */
#ifndef SRC_CIRCULARBUFFER_H_
#define SRC_CIRCULARBUFFER_H_

#define circularQueue_size 32
#include "common.h"

class CircularBuffer {
public:
	//CircularBuffer(int size);
	CircularBuffer(int size);
	CircularBuffer();
	~CircularBuffer();

	int inc_ptr(int ptr);
	int dec_ptr(int ptr);
	void add(en newData);
	en pop(int rd_ptr);
	bool isEmpty(int& rd_ptr, int desired_time_stamp);

private:
	en* queue; //dynamically allocated queue
	int size;
	int wr_ptr=0;
};


#endif /* SRC_CIRCULARBUFFER_H_ */
