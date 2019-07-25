//============================================================================
// Name        : Observer.h
// Author      : Pei Zhang
// Institution : Iowa State University
// Description : Class of different observers
//============================================================================

#ifndef SRC_OBSERVER_H_
#define SRC_OBSERVER_H_

#include <iostream>
#include <stdio.h>
#include <list>
#include <fstream>
#include <sstream>
#include <string>
#include "CircularBuffer.h"
#include "common.h"
#include "Loader.h"

using namespace std;

#define to_verdict(x) x?"True":"False"


// case OP_FT_GJ:
// 			ft_sync_queues[i].pre = (elt_ft_queue_t){false,-1};
// 			break;
// 		case OP_FT_UJ: 
// 			ft_sync_queues[i].pre = (elt_ft_queue_t){true,-1};
// 			break;
// 		default: 
// 			ft_sync_queues[i].pre = (elt_ft_queue_t){true,0};


class Observer{
public:
	Observer(int pc);
	Observer(Observer *cob1, Observer *cob2, int pc);
	Observer(Observer *cob, int pc);
	virtual void run(FILE*){};
	virtual void dprint1(FILE*){};
	virtual void dprint1(){};
	virtual bool read_buffer(){return false;};
	virtual ~Observer(){};
	CircularBuffer *cb=new CircularBuffer();
	static int time_stamp;

protected:
	Observer *child_observer_1=0;
	Observer *child_observer_2=0;
	int rdPtr=0,rdPtr_2=0;
	en result={0,-1};
	int pc=0;
	int desired_time_stamp=0;
};

//END (for assembly only)
class END : public Observer{
public:
	~END(){}
	END(Observer *cob, int pc):Observer(cob,pc){}
	void dprint1(FILE* pFile){
		fprintf(pFile,"PC:%d END = [%d,%s]\n",pc,result.time_stamp,to_verdict(result.verdict));
	}
	
	void run(FILE* pFile){
		bool isEmpty = child_observer_1->cb->isEmpty(rdPtr,desired_time_stamp);
		while(!isEmpty){
			en read_data = child_observer_1->cb->pop(rdPtr);
			result = read_data;
			cb->add(result);
			dprint1(pFile);
			desired_time_stamp=result.time_stamp+1;
			isEmpty = child_observer_1->cb->isEmpty(rdPtr,desired_time_stamp);
		}
	}
};

//LOAD
class ATOM : public Observer{
public:
	~ATOM(){}
//constructor
	ATOM(string atom_name, Loader* sensor_loader, int pc):Observer(pc),atom_name(atom_name),sensor_loader(sensor_loader){}
//override
	void dprint1(FILE* pFile) {fprintf(pFile,"PC:%d LOAD = [%d,%s]\n",pc,result.time_stamp,to_verdict(result.verdict));}
	void run(FILE* pFile){
		result={sensor_loader->get(atom_name),time_stamp};
		cb->add(result);
		dprint1(pFile);
	}
private:
	string atom_name;
	Loader* sensor_loader;
};

//NOT
class NEG : public Observer{
public:
	~NEG(){}
//constructor
	NEG(Observer *cob, int pc):Observer(cob,pc){}
	void dprint1(FILE* pFile) {
		fprintf(pFile,"PC:%d NOT = [%d,%s]\n",pc,result.time_stamp,to_verdict(result.verdict));
	}
	void run(FILE* pFile){
		bool isEmpty = child_observer_1->cb->isEmpty(rdPtr,desired_time_stamp);
		en read_data = child_observer_1->cb->pop(rdPtr);
		while(!isEmpty) {
			result = {!read_data.verdict,read_data.time_stamp};
			desired_time_stamp = read_data.time_stamp+1;
			cb->add(result);
			dprint1(pFile);
			isEmpty = child_observer_1->cb->isEmpty(rdPtr,desired_time_stamp);
		}
	}
};


//AND
class AND : public Observer{
public:
	~AND(){}
	AND(Observer *cob1, Observer *cob2, int pc):Observer(cob1,cob2,pc){}
	
	void dprint1(FILE* pFile){
		fprintf(pFile,"PC:%d AND = [%d,%s]\n",pc,result.time_stamp,to_verdict(result.verdict));
	}
	void run(FILE* pFile){

		bool isEmpty = child_observer_1->cb->isEmpty(rdPtr,desired_time_stamp);
		bool isEmpty_2 = child_observer_2->cb->isEmpty(rdPtr_2,desired_time_stamp);
		en read_data = child_observer_1->cb->pop(rdPtr);
		en read_data_2 = child_observer_2->cb->pop(rdPtr_2);
		while(!isEmpty || !isEmpty_2) {
			result = {false,-1};

			if(!isEmpty && !isEmpty_2) {
				if(read_data.verdict && read_data_2.verdict) {
					result = {true,min(read_data.time_stamp,read_data_2.time_stamp)};
				} else if(!read_data.verdict && !read_data_2.verdict) {
					result = {false,max(read_data.time_stamp,read_data_2.time_stamp)};
				} else if(read_data.verdict) {
					result = {false,read_data_2.time_stamp};
				} else {
					result = {false,read_data.time_stamp};
				}

			} else if(isEmpty) {
				if(!read_data_2.verdict) {
					result = {false,read_data_2.time_stamp};
				}
			} else {
				if(!read_data.verdict) {
					result = {false,read_data.time_stamp};
				}
			}

			if(result.time_stamp!=-1) {
				cb->add(result);
				dprint1(pFile);
				desired_time_stamp = result.time_stamp+1;
			} else break;

			isEmpty = child_observer_1->cb->isEmpty(rdPtr,desired_time_stamp);
			isEmpty_2 = child_observer_2->cb->isEmpty(rdPtr_2,desired_time_stamp);
		}
	}
};

//ALW
class GLOBAL : public Observer{
public:
	~GLOBAL(){}

	GLOBAL(Observer *cob, int tau1, int tau2, int pc):Observer(cob,pc),tau1(tau1),tau2(tau2){}
	GLOBAL(Observer *cob, int tau2, int pc):Observer(cob,pc),tau1(0),tau2(tau2){}
	
	void dprint1(FILE* pFile){
		fprintf(pFile,"PC:%d G[%d,%d] = [%d,%s]\n",pc,tau1,tau2,result.time_stamp,to_verdict(result.verdict));
	}

	void run(FILE* pFile){
		bool isEmpty = child_observer_1->cb->isEmpty(rdPtr,desired_time_stamp);
		int pre_time_stamp = pre.time_stamp;
		bool pre_verdict = pre.verdict;

		while(!isEmpty) {
			en read_data = child_observer_1->cb->pop(rdPtr);
			desired_time_stamp = read_data.time_stamp+1;
			if(read_data.verdict && !pre_verdict) m_up = pre_time_stamp+1;
			if(read_data.verdict) {
				if(read_data.time_stamp-m_up>=tau2-tau1 && time_stamp-tau2>=0) {
					result = {true,read_data.time_stamp-tau2};
					cb->add(result);
					dprint1(pFile);
				}
			} else if(read_data.time_stamp-tau1>=0) {
				result = {false,read_data.time_stamp-tau1};
				cb->add(result);
				dprint1(pFile);
			}
			pre = {read_data.verdict,read_data.time_stamp};
			isEmpty = child_observer_1->cb->isEmpty(rdPtr,desired_time_stamp);
		}
	}
private:
	int tau1,tau2;
	en pre = {false,-1};
	int m_up = 0;
};

class UNTIL : public Observer{
public:
	~UNTIL(){}
	UNTIL(Observer *cob1, Observer *cob2, int tau1, int tau2, int pc):Observer(cob1,cob2,pc),tau1(tau1), tau2(tau2){}
	void dprint1(FILE* pFile){
		fprintf(pFile,"PC:%d U[%d,%d] = [%d,%s]\n",pc,tau1,tau2,result.time_stamp,to_verdict(result.verdict));
	}

	void run(FILE* pFile){
		bool isEmpty = child_observer_1->cb->isEmpty(rdPtr,desired_time_stamp);
		bool isEmpty_2 = child_observer_2->cb->isEmpty(rdPtr_2,desired_time_stamp);
		
		int pre_time_stamp_2 = pre.time_stamp;
		int pre_verdict_2 = pre.verdict;
		while(!isEmpty and !isEmpty_2) {
			
			en read_data = child_observer_1->cb->pop(rdPtr);
			en read_data_2 = child_observer_2->cb->pop(rdPtr_2);
			
			result = {false,-1};
			int tau = min(read_data.time_stamp,read_data_2.time_stamp);
			desired_time_stamp = tau + 1;

			if(pre_verdict_2 && !read_data_2.verdict) m_down = pre_time_stamp_2+1;
			if(read_data_2.verdict) result = {true,tau-tau1};
			else if(!read_data.verdict) result = {false,tau-tau1};
			else if(tau>=tau2-tau1+m_down) result = {false,tau-tau2};
			if(result.time_stamp>=preResult) {
				cb->add(result);
				dprint1(pFile);
			}
			pre = {read_data_2.verdict,read_data_2.time_stamp};
			isEmpty = child_observer_1->cb->isEmpty(rdPtr,desired_time_stamp);
			isEmpty_2 = child_observer_2->cb->isEmpty(rdPtr_2,desired_time_stamp);
		}
	}
private:
	en pre = {true,-1};
	int m_down = 0;
	int preResult = 0;//time stamp of previous result
	int tau1,tau2;

};

#endif
