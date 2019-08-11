/*
 * Assembly.cpp
 *
 *  Created on: Jul 18, 2017
 *      Author: PEI
 */

#include <fstream>
#include <sstream>
#include <iostream>
#include <string>
#include <vector>
#include "Assembly.h"
#include "Observer.h"

using namespace std;
Assembly::Assembly(string filename): num_of_observer(0),subformula_tag(0),top_ob(0),filename(filename) {
	ifstream infile(filename.c_str());
	if(!infile){cout<<"Cannot find file: "<<filename<<endl;}
	else{
		string line;
		while (getline(infile, line)) ++num_of_observer;
	}
}

void Assembly::Construct(Loader* sensor_loader, Observer** observer){
	ifstream infile(filename.c_str());
	string line;
	string partial;
	vector<std::string> tokens;
	while (getline(infile, line)&&line.compare("")!=0){
		line.erase(line.find_last_not_of(" \n\r\t")+1); //remove ending space etc
		line.erase(0,line.find_first_of(":")+1);
		line = line.substr(line.find_first_not_of(" \n\r\t")); //remove front space etc
		istringstream iss(line);
		string token;
		string tinyToken;
		while(getline(iss, token, ' ')){   // split by space
			stringstream isss(token);
			while(getline(isss, tinyToken, '\t')){
		        if(tinyToken.compare("")!=0) tokens.push_back(tinyToken);
			}
		}
		if(tokens.at(0).compare("load")==0 || tokens.at(0).compare("load_ft")==0) {
			string src=tokens.at(1);
			string name = src;
			// int obNum=stoi(src.substr(1,src.length()),nullptr);
			observer[subformula_tag]=new ATOM(name,sensor_loader,subformula_tag);
		} else if(tokens.at(0).compare("not")==0) {
			string src=tokens.at(1);
			int obNum=stoi(src.substr(1,src.length()),nullptr);
			observer[subformula_tag]=new NEG(observer[obNum],subformula_tag);
		} else if(tokens.at(0).compare("boxbox")==0) {
			string src=tokens.at(1);
			int obNum=stoi(src.substr(1,src.length()),nullptr);
			int intNum=stoi(tokens.at(2),nullptr);
			observer[subformula_tag]=new GLOBAL(observer[obNum],intNum,subformula_tag);
		} else if(tokens.at(0).compare("and")==0) {
			string src_1=tokens.at(1);
			int obNum_1=stoi(src_1.substr(1,src_1.length()),nullptr);
			string src_2=tokens.at(2);
			int obNum_2=stoi(src_2.substr(1,src_2.length()),nullptr);
			observer[subformula_tag]=new AND(observer[obNum_1],observer[obNum_2],subformula_tag);
		} else if(tokens.at(0).compare("boxdot")==0) {
			string src=tokens.at(1);
			int obNum=stoi(src.substr(1,src.length()),nullptr);
			int intNum_1=stoi(tokens.at(2),nullptr);
			int intNum_2=stoi(tokens.at(3),nullptr);
			observer[subformula_tag]=new GLOBAL(observer[obNum],intNum_1,intNum_2,subformula_tag);
			
		} else if(tokens.at(0).compare("end")==0) {
			string obNum=tokens.at(1);
			top_ob=stoi(obNum.substr(1,obNum.length()),nullptr);
			observer[subformula_tag]=new END(observer[top_ob],subformula_tag);
		} else if(tokens.at(0).compare("until")==0) {
			string src_1=tokens.at(1);
			int obNum_1=stoi(src_1.substr(1,src_1.length()),nullptr);
			string src_2=tokens.at(2);
			int obNum_2=stoi(src_2.substr(1,src_2.length()),nullptr);
			int intNum_1=stoi(tokens.at(3),nullptr);
			int intNum_2=stoi(tokens.at(4),nullptr);
			observer[subformula_tag]=new UNTIL(observer[obNum_1],observer[obNum_2],intNum_1,intNum_2,subformula_tag);
		} else{
			cout<<"Undefined Symbol"<<endl;
		}
		subformula_tag++;
		tokens.clear();

	}

}

Assembly::~Assembly() {
	// TODO Auto-generated destructor stub
}

