#include <iterator>
#include <iostream>
#include <fstream>
#include <sstream>
#include <vector>
#include <string>
#include <unordered_map>
#include "Loader.h"

#define SENSOR(x) data_row[sen2pos[x]] //x is the sensor name in sensor log file

using namespace std;

// user specified atomic conversion function
bool Loader::get(string atom_name) {
	if(atom_name.compare("a0")==0) {
		return SENSOR("a0")>0.5;
	} else if(atom_name.compare("a1")==0) {
		return SENSOR("a1")>0.5;
	} else if(atom_name.compare("a2")==0) {
		return SENSOR("a2")>0.5;
	} else {
		throw "Sensor conversion function unspecified.";
	}

}


Loader::Loader(std::string filename) {
	file = new ifstream(filename.c_str());
	csv_row = new CSVRow;
	csv_row->readNextRow(*file);//collect sensor names in the first line
	for(int i=0;i<csv_row->m_data.size();i++) {
		sen2pos.insert(pair<string,int>(csv_row->m_data[i],i));
	}
}

Loader::~Loader() {
	delete file;
	delete csv_row;
}



bool Loader::has_next() {
	if(csv_row->readNextRow(*file)) {
		convert();
		return true;
	}
	return false;
}

void Loader::convert() {
	data_row.clear();
	for(string s:csv_row->m_data) {
		data_row.push_back(stod(s,nullptr));
	}
}

// std::vector<std::string> Loader::load_next() {
// 	return csv_row->m_data;
// }




