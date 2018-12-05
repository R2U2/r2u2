//============================================================================
// Name        : Observer.h
// Author      : Pei Zhang
// Institution : Iowa State University
// Description : Class of different observers
//============================================================================

#pragma once
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

using namespace std;


class Observer{
public:
	Observer();
	Observer(Observer *cob1, Observer *cob2);
	Observer(Observer *cob);
	virtual void run(FILE*,string){};
	virtual void run(){};
	virtual void dprint1(FILE*,string){};
	virtual void dprint2(FILE*,string){};
	virtual void dprint1(){};
	virtual void dprint2(){};
	virtual bool read_buffer(){return false;};
	virtual ~Observer(){};
	CircularBuffer *cb=new CircularBuffer();

protected:
	Observer *child_observer_1=0;
	Observer *child_observer_2=0;
	bool hasPrint=false;
	int rdPtr=0,rdPtr2=0;
	en read_data={0,0};
	int last_tau=-1;
	en result={0,-1};
	mem track={-1,-1,{0,-1}};
};


class Event: public Observer{
public:
	Event(string filename){
		cb->isBottom=true;
		ifstream infile(filename.c_str());
		if(!infile){cout<<"Cannot find file!"<<endl;}
		else{
			string line;
			while (getline(infile, line)){
				istringstream iss(line);
				int verdict,time_stamp;
				if (!(iss >> verdict>> time_stamp )) { break; } // error
				en cur_node={verdict,time_stamp};
				cb->write(cur_node);
			}
		}
	}
};

//END (for assembly only)
class Observer_type_end : public Observer{
public:
	int pc=0;
	~Observer_type_end(){}
	Observer_type_end(Observer *cob):Observer(cob){}
	Observer_type_end(Observer *cob, int pc):Observer(cob),pc(pc){}
	bool read_buffer(){
		read_data=child_observer_1->cb->read(rdPtr);
		return read_data.time_stamp>last_tau;
	}
	void dprint1(FILE* pFile,string s){
		if(result.time_stamp!=-1){
			hasPrint=true;
			fprintf(pFile,"END %s:%d = (%d,%d)\n",s.c_str(),pc,read_data.verdict,read_data.time_stamp);
			//cout<<"END "<<s<<":"<<pc<<" = ("<<read_data.verdict<<","<<read_data.time_stamp<<")"<<endl;
		}
	}
	void dprint2(FILE* pFile,string s) {if(!hasPrint) fprintf(pFile,"END %s:%d = (-,-)\n",s.c_str(),pc);}
	//cout<<"END "<<s<<":"<<pc<<" = (-,-)"<<endl;
	void run(FILE* pFile,string s){
		hasPrint=false;
		result={0,-1};
		while(!child_observer_1->cb->isEmpty(rdPtr)){
			if(read_buffer()){
				result=read_data;
				cb->write(result);
			}
			dprint1(pFile,s);
			rdPtr++;
			last_tau=result.time_stamp==-1?last_tau:result.time_stamp;
		}
		dprint2(pFile,s);
		if(child_observer_1->cb->recedPtr(rdPtr)) rdPtr--;
	}
};

//LOAD
class Observer_type_0 : public Observer{
public:
	~Observer_type_0(){}
//constructor
	Observer_type_0(Observer *cob):Observer(cob){}
	Observer_type_0(Observer *cob, int pc):Observer(cob),pc(pc){}
//override
	void dprint1(FILE* pFile, string s) {fprintf(pFile,"LOAD %s:%d = (%d,%d)\n",s.c_str(),pc,result.verdict,result.time_stamp);}
	//cout<<"LOAD "<<s<<":"<<pc<<" = ("<<result.verdict<<","<<result.time_stamp<<")"<<endl;
	void run(FILE* pFile, string s){//child_node_1.out_node
		result=child_observer_1->cb->read(rdPtr);;
		cb->write(result);
		dprint1(pFile,s);
	}
private:
	int pc=0;
};

//NOT
class Observer_type_1 : public Observer{
public:
	~Observer_type_1(){}
//constructor
	Observer_type_1(Observer *cob):Observer(cob){}
	Observer_type_1(Observer *cob, int pc):Observer(cob),pc(pc){}
//override
	bool read_buffer(){
		read_data=child_observer_1->cb->read(rdPtr);
		return read_data.time_stamp>last_tau;
	}
	void dprint1(FILE* pFile,string s){
		if(result.time_stamp!=-1){
			hasPrint=true;
			//cout<<"NOT "<<s<<":"<<pc<<" = ("<<result.verdict<<","<<result.time_stamp<<")"<<endl;
			fprintf(pFile,"NOT %s:%d = (%d,%d)\n",s.c_str(),pc,result.verdict,result.time_stamp);
		}
	}
	void dprint2(FILE* pFile,string s) {if(!hasPrint) fprintf(pFile,"NOT %s:%d = (-,-)\n",s.c_str(),pc);}
	//cout<<"NOT "<<s<<":"<<pc<<" = (-,-)"<<endl;
	void run(FILE* pFile,string s){//child_node_1.out_node
		hasPrint=false;
		result={0,-1};
		while(!child_observer_1->cb->isEmpty(rdPtr)){
			if(read_buffer()){
				result={!read_data.verdict,read_data.time_stamp};
				cb->write(result);
			}
			dprint1(pFile,s);
			last_tau=result.time_stamp==-1?last_tau:result.time_stamp;
			rdPtr++;
		}
		dprint2(pFile,s);
		if(child_observer_1->cb->recedPtr(rdPtr)) rdPtr--;
	}
private:
	int pc=0;
};

//KEP
class Observer_type_2 : public Observer{
public:
	~Observer_type_2(){}
	Observer_type_2(Observer *cob, int tau):Observer(cob),tau(tau){}
	Observer_type_2(Observer *cob, int tau, int pc):Observer(cob),pc(pc),tau(tau),counter(0){}
	bool read_buffer(){
		if(child_observer_1->cb->isEmpty(rdPtr)) return false;
		read_data=child_observer_1->cb->read(rdPtr);
		return read_data.time_stamp>last_tau;
	}
	void dprint1(FILE* pFile, string s){
		if(result.time_stamp!=-1){
			hasPrint=true;
			fprintf(pFile,"G[%d] %s:%d = (%d,%d)\n",tau,s.c_str(),pc,result.verdict,result.time_stamp);
			//cout<<"G["<<tau<<"] "<<s<<":"<<pc<<" = ("<<result.verdict<<","<<result.time_stamp<<")"<<endl;
		}
	}
	void dprint2(FILE* pFile, string s) {if(!hasPrint) fprintf(pFile,"G[%d] %s:%d = (-,-)\n",tau,s.c_str(),pc);}
	// cout<<"G["<<tau<<"] "<<s<<":"<<pc<<" = (-,-)"<<endl;
	void run(FILE* pFile,string s){
		hasPrint=false;
		while(true){
			track={rdPtr,rdPtr2,result};
			result={0,-1};
			while(!child_observer_1->cb->isEmpty(rdPtr)&&!read_buffer()) rdPtr++;
			if(read_buffer()){
				if(read_data.verdict==1){
					if(counter>=tau){
						result={1,read_data.time_stamp-tau};
						cb->write(result);
					}
					counter++;
				}else{
					counter=0;
					result={0,read_data.time_stamp};
					cb->write(result);
				}
			}
			last_tau=read_data.time_stamp;

			if(child_observer_1->cb->recedPtr(rdPtr)) rdPtr--;
			if(track.rdPtr_mem==rdPtr&&track.result_mem.time_stamp==result.time_stamp) break;
			if(track.result_mem.time_stamp!=result.time_stamp) dprint1(pFile,s);
		}
		dprint2(pFile,s);
	}
private:
	int pc=0,tau,counter=0;
};

//AND
class Observer_type_3 : public Observer{
public:
	~Observer_type_3(){}
	Observer_type_3(Observer *cob1, Observer *cob2):Observer(cob1,cob2){}
	Observer_type_3(Observer *cob1, Observer *cob2, int pc):Observer(cob1,cob2),pc(pc){}
	bool read_buffer(){
		if(child_observer_1->cb->isEmpty(rdPtr)) return false;
		read_data=child_observer_1->cb->read(rdPtr);
		return read_data.time_stamp>last_tau;
	}
	bool read_buffer2(){
		if(child_observer_2->cb->isEmpty(rdPtr2)) return false;
		read_data2=child_observer_2->cb->read(rdPtr2);
		return read_data2.time_stamp>last_tau;
	}
	void dprint1(FILE* pFile, string s){
		if(result.time_stamp!=-1){
			hasPrint=true;
			fprintf(pFile,"AND %s:%d = (%d,%d)\n",s.c_str(),pc,result.verdict,result.time_stamp);
			//cout<<"AND "<<s<<":"<<pc<<" = ("<<result.verdict<<","<<result.time_stamp<<")"<<endl;
		}
	}
	void dprint2(FILE* pFile, string s) {if(!hasPrint) fprintf(pFile,"AND %s:%d = (-,-)\n",s.c_str(),pc);}
	//cout<<"AND "<<s<<":"<<pc<<" = (-,-)"<<endl;
	void run(FILE* pFile, string s){
		result={0,-1};
		hasPrint=false;
		while(true){
			track={rdPtr,rdPtr2,result};
			while(!child_observer_1->cb->isEmpty(rdPtr)&&!read_buffer()) rdPtr++;
			while(!child_observer_2->cb->isEmpty(rdPtr2)&&!read_buffer2()) rdPtr2++;
			if(!child_observer_1->cb->isEmpty(rdPtr)&&!child_observer_2->cb->isEmpty(rdPtr2)){
				if(read_data.verdict==1&&read_data2.verdict==1){
					if((read_data.time_stamp<read_data2.time_stamp&&read_buffer())||\
							(read_data2.time_stamp<=read_data.time_stamp&&read_buffer2())){
						result={1,min(read_data.time_stamp,read_data2.time_stamp)};
					}
				}else if(read_data.verdict==0&&read_data2.verdict==0){
					result={0,max(read_data.time_stamp,read_data2.time_stamp)};
				}else if(read_data.verdict==1&&read_data2.verdict==0){
					result={0,read_data2.time_stamp};
				}else{
					result={0,read_data.time_stamp};
				}
			}
			else if(!child_observer_2->cb->isEmpty(rdPtr2)){//!q2.empty()&&q1.empty()
				if(read_data2.verdict==0){
					result={0,read_data2.time_stamp};
				}
			}
			else if(!child_observer_1->cb->isEmpty(rdPtr)&&child_observer_2->cb->isEmpty(rdPtr2)){
				if(read_data.verdict==0){
					result={0,read_data.time_stamp};
				}
			}

			if(result.time_stamp!=-1){
				last_tau=result.time_stamp;
				cb->write(result);
			}
			if(child_observer_1->cb->recedPtr(rdPtr)) rdPtr--;
			if(child_observer_2->cb->recedPtr(rdPtr2)) rdPtr2--;
			if(track.rdPtr_mem==rdPtr&&track.rdPtr2_mem==rdPtr2&&track.result_mem.time_stamp==result.time_stamp) break;
			if(track.result_mem.time_stamp!=result.time_stamp) dprint1(pFile,s);
		}
		dprint2(pFile,s);
	}
private:
	int pc=0;
	en read_data2={0,0};
};

//ALW
class Observer_type_4 : public Observer{
public:
	~Observer_type_4(){}
	Observer_type_4(Observer *cob, int tau1, int tau2):Observer(cob),tau1(tau1),tau2(tau2){}
	Observer_type_4(Observer *cob, int tau1, int tau2, int pc):Observer(cob),tau1(tau1),tau2(tau2),pc(pc){}
	bool read_buffer(){
		if(child_observer_1->cb->isEmpty(rdPtr)) return false;
		read_data=child_observer_1->cb->read(rdPtr);
		return read_data.time_stamp>last_tau;
	}
	void dprint1(FILE* pFile,string s){
		if(result.time_stamp!=-1){
			hasPrint=true;
			fprintf(pFile,"G[%d,%d] %s:%d = (%d,%d)\n",tau1,tau2,s.c_str(),pc,result.verdict,result.time_stamp);
			//cout<<"G["<<tau1<<","<<tau2<<"] "<<s<<":"<<pc<<" = ("<<result.verdict<<","<<result.time_stamp<<")"<<endl;
		}
	}
	void dprint2(FILE* pFile,string s){if(!hasPrint) fprintf(pFile,"G[%d,%d] %s:%d = (-,-)\n",tau1,tau2,s.c_str(),pc);}
	//cout<<"G["<<tau1<<","<<tau2<<"] "<<s<<":"<<pc<<" = (-,-)"<<endl;

	void run(FILE* pFile,string s){
		int tau=tau2-tau1;
		hasPrint=false;
		result={0,-1};
		while(true){
			track={rdPtr,rdPtr2,result};

			int new_time_stamp=0;
			while(!child_observer_1->cb->isEmpty(rdPtr)&&!read_buffer()) rdPtr++;
			if(read_buffer()){
				if(read_data.verdict==1){
					if(counter>=tau&&(new_time_stamp=read_data.time_stamp-tau2)>=0){
						result={1,new_time_stamp};
						cb->write(result);
					}
					counter++;
				}else{
					counter=0;
					if((new_time_stamp=read_data.time_stamp-tau1)>=0){
						result={0,new_time_stamp};
						cb->write(result);
					}
				}
			}
			last_tau=read_data.time_stamp;
			if(child_observer_1->cb->recedPtr(rdPtr)) rdPtr--;
			if(track.rdPtr_mem==rdPtr&&track.result_mem.time_stamp==result.time_stamp) break;
			if(track.result_mem.time_stamp!=result.time_stamp) dprint1(pFile,s);
		}
		dprint2(pFile,s);
	}
private:
	int tau1,tau2,counter=0,pc=0;
};

//TODO until
class Observer_type_5 : public Observer{};
#endif
