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

class Observer{
public:
	Observer();
	Observer(Observer *cob1, Observer *cob2);
	Observer(Observer *cob);
	// virtual void run(FILE*,string){};
	virtual void run(FILE*,string,int){};
	// virtual void run(){};
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

//END (for assembly only)
class END : public Observer{
public:
	int pc=0;
	~END(){}
	// END(Observer *cob):Observer(cob){}
	END(Observer *cob, int pc):Observer(cob),pc(pc){}
	bool read_buffer(){
		read_data=child_observer_1->cb->read(rdPtr);
		return read_data.time_stamp>last_tau;
	}
	void dprint1(FILE* pFile,string s){
		if(result.time_stamp!=-1){
			hasPrint=true;
			fprintf(pFile,"%s:%d END = [%d,%s]\n",s.c_str(),pc,read_data.time_stamp,to_verdict(read_data.verdict));
			//cout<<"END "<<s<<":"<<pc<<" = ("<<read_data.verdict<<","<<read_data.time_stamp<<")"<<endl;
		}
	}
	void dprint2(FILE* pFile,string s) {if(!hasPrint) fprintf(pFile,"END %s:%d = (-,-)\n",s.c_str(),pc);}
	//cout<<"END "<<s<<":"<<pc<<" = (-,-)"<<endl;
	void run(FILE* pFile,string s, int time_stamp){
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
		// dprint2(pFile,s);
		if(child_observer_1->cb->recedPtr(rdPtr)) rdPtr--;
	}
};

//LOAD
class ATOM : public Observer{
public:
	~ATOM(){}
//constructor
	// ATOM(Observer *cob):Observer(cob){}
	ATOM(string atom_name, Loader* sensor_loader, int pc):atom_name(atom_name),sensor_loader(sensor_loader),pc(pc){}
//override
	void dprint1(FILE* pFile, string s) {fprintf(pFile,"%s:%d LOAD = [%d,%s]\n",s.c_str(),pc,result.time_stamp,to_verdict(result.verdict));}
	//cout<<"LOAD "<<s<<":"<<pc<<" = ("<<result.verdict<<","<<result.time_stamp<<")"<<endl;
	void run(FILE* pFile, string s, int time_stamp){//child_node_1.out_node
		// result=child_observer_1->cb->read(rdPtr);
		result={sensor_loader->get(atom_name),time_stamp};
		cb->write(result);
		dprint1(pFile,s);
	}
private:
	string atom_name;
	Loader* sensor_loader;
	int pc=0;
};

//NOT
class NEG : public Observer{
public:
	~NEG(){}
//constructor
	// NEG(Observer *cob):Observer(cob){}
	NEG(Observer *cob, int pc):Observer(cob),pc(pc){}
//override
	bool read_buffer(){
		read_data=child_observer_1->cb->read(rdPtr);
		return read_data.time_stamp>last_tau;
	}
	void dprint1(FILE* pFile,string s){
		if(result.time_stamp!=-1){
			hasPrint=true;
			//cout<<"NOT "<<s<<":"<<pc<<" = ("<<result.verdict<<","<<result.time_stamp<<")"<<endl;
			fprintf(pFile,"%s:%d NOT = [%d,%s]\n",s.c_str(),pc,result.time_stamp,to_verdict(result.verdict));
		}
	}
	void dprint2(FILE* pFile,string s) {if(!hasPrint) fprintf(pFile,"NOT %s:%d = (-,-)\n",s.c_str(),pc);}
	//cout<<"NOT "<<s<<":"<<pc<<" = (-,-)"<<endl;
	void run(FILE* pFile,string s, int time_stamp){//child_node_1.out_node
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
		// dprint2(pFile,s);
		if(child_observer_1->cb->recedPtr(rdPtr)) rdPtr--;
	}
private:
	int pc=0;
};


//AND
class AND : public Observer{
public:
	~AND(){}
	// AND(Observer *cob1, Observer *cob2):Observer(cob1,cob2){}
	AND(Observer *cob1, Observer *cob2, int pc):Observer(cob1,cob2),pc(pc){}
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
			fprintf(pFile,"%s:%d AND = [%d,%s]\n",s.c_str(),pc,result.time_stamp,to_verdict(result.verdict));
			//cout<<"AND "<<s<<":"<<pc<<" = ("<<result.verdict<<","<<result.time_stamp<<")"<<endl;
		}
	}
	void dprint2(FILE* pFile, string s) {if(!hasPrint) fprintf(pFile,"AND %s:%d = (-,-)\n",s.c_str(),pc);}
	//cout<<"AND "<<s<<":"<<pc<<" = (-,-)"<<endl;
	void run(FILE* pFile, string s, int time_stamp){
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
		// dprint2(pFile,s);
	}
private:
	int pc=0;
	en read_data2={0,0};
};

//ALW
class GLOBAL : public Observer{
public:
	~GLOBAL(){}
	// GLOBAL(Observer *cob, int tau1, int tau2):Observer(cob),tau1(tau1),tau2(tau2){}
	GLOBAL(Observer *cob, int tau1, int tau2, int pc):Observer(cob),tau1(tau1),tau2(tau2),pc(pc){}
	GLOBAL(Observer *cob, int tau2, int pc):Observer(cob),tau1(0),tau2(tau2),pc(pc){}
	bool read_buffer(){
		if(child_observer_1->cb->isEmpty(rdPtr)) return false;
		read_data=child_observer_1->cb->read(rdPtr);
		return read_data.time_stamp>last_tau;
	}
	void dprint1(FILE* pFile,string s){
		if(result.time_stamp!=-1){
			hasPrint=true;
			fprintf(pFile,"%s:%d G[%d,%d] = [%d,%s]\n",s.c_str(),pc,tau1,tau2,result.time_stamp,to_verdict(result.verdict));
			//cout<<"G["<<tau1<<","<<tau2<<"] "<<s<<":"<<pc<<" = ("<<result.verdict<<","<<result.time_stamp<<")"<<endl;
		}
	}
	void dprint2(FILE* pFile,string s){if(!hasPrint) fprintf(pFile,"G[%d,%d] %s:%d = (-,-)\n",tau1,tau2,s.c_str(),pc);}
	//cout<<"G["<<tau1<<","<<tau2<<"] "<<s<<":"<<pc<<" = (-,-)"<<endl;

	void run(FILE* pFile,string s, int time_stamp){
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
		// dprint2(pFile,s);
	}
private:
	int tau1,tau2,counter=0,pc=0;
};

class UNTIL : public Observer{
public:
	~UNTIL(){}
	UNTIL(Observer *cob1, Observer *cob2, int tau1, int tau2, int pc):Observer(cob1,cob2),tau1(tau1), tau2(tau2), pc(pc){}
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
	void dprint1(FILE* pFile,string s){
		if(result.time_stamp!=-1){
			hasPrint=true;
			fprintf(pFile,"%s:%d U[%d,%d] = [%d,%s]\n",s.c_str(),pc,tau1,tau2,result.time_stamp,to_verdict(result.verdict));
			//cout<<"G["<<tau1<<","<<tau2<<"] "<<s<<":"<<pc<<" = ("<<result.verdict<<","<<result.time_stamp<<")"<<endl;
		}
	}

	void run(FILE* pFile,string s, int time_stamp){
		bool has_data = read_buffer();
		bool has_data2 = read_buffer2();
		int pre_time_stamp_2 = pre.time_stamp;
		int pre_verdict_2 = pre.verdict;
		while(has_data or has_data2) {
			result = {0,-1};
			tau = min(read_data.time_stamp,read_data2.time_stamp);
			last_tau = tau + 1;
			// cout<<"ODIOJEOD"<<endl;
			if(pre_verdict_2 && !read_data2.verdict) m_down = pre_time_stamp_2+1;
			if(read_data2.verdict) result = {1,tau-tau1};
			else if(!read_data.verdict) result = {0,tau-tau1};
			else if(tau>=tau2-tau1+m_down) result = {0,tau-tau2};
			if(result.time_stamp>=preResult) {
				cb->write(result);
				dprint1(pFile,s);
			}
			pre = {read_data2.verdict,read_data2.time_stamp};
			if(child_observer_1->cb->recedPtr(rdPtr)) rdPtr--;
			if(child_observer_2->cb->recedPtr(rdPtr2)) rdPtr2--;
			has_data = read_buffer();
			has_data2 = read_buffer2();
		}
	}
private:
	en pre = {1,-1};
	int m_down = 0;
	int preResult = 0;//time stamp of previous result
	int tau1,tau2;
	int tau;
	int pc=0;
	en read_data2={0,0};


};


#endif
