#ifndef SRC_LOADER_H_
#define SRC_LOADER_H_

#include <iterator>
#include <iostream>
#include <fstream>
#include <sstream>
#include <vector>
#include <string>
#include <unordered_map>

using namespace std;

class CSVRow {
public:
	string const& operator[](size_t index) const {
		return m_data[index];
	}
	size_t size() const {
		return m_data.size();
	}

	~CSVRow(){};

	vector<string> m_data;
	

	bool is_empty(ifstream& pFile) {
		return pFile.peek() == ifstream::traits_type::eof();
	}

	bool readNextRow(ifstream& str){
		if(is_empty(str)) return false;
		string line;
		std::getline(str, line);

		stringstream lineStream(line);
		string cell;

		m_data.clear();
		while(getline(lineStream, cell, ',')) {
			m_data.push_back(cell);
		}
		// This checks for a trailing comma with no data after it.
		if (!lineStream && cell.empty()) { 
		    // If there was a trailing comma then add an empty element.
			m_data.push_back("");
		}
		return true;

	}

};



class Loader {
public:
	Loader(string);
	bool has_next();
	// vector<string> load_next();
	void convert();
	bool get(string atom_name);
	~Loader();
	

private:
	CSVRow* csv_row;
	ifstream* file;
	unordered_map<string,int> sen2pos;
	vector<double> data_row;
};

#endif