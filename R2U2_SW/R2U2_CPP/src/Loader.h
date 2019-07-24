#ifndef SRC_LOADER_H_
#define SRC_LOADER_H_

#include <iterator>
#include <iostream>
#include <fstream>
#include <sstream>
#include <vector>
#include <string>

using namespace std;

class CSVRow {
public:
	std::string const& operator[](std::size_t index) const {
		return m_data[index];
	}
	std::size_t size() const {
		return m_data.size();
	}
	// operator overload
	// std::istream& operator>>(std::istream& str) {
	// 	readNextRow(str);
	// 	return str;
	// }
	~CSVRow(){};

	std::vector<std::string> m_data;

	bool is_empty(std::ifstream& pFile) {
		return pFile.peek() == std::ifstream::traits_type::eof();
	}

	bool readNextRow(std::ifstream& str){
		if(is_empty(str)) return false;
		std::string line;
		std::getline(str, line);

		std::stringstream lineStream(line);
		std::string cell;

		m_data.clear();
		while(std::getline(lineStream, cell, ',')) {
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
	vector<string> load_next();
	int get(int atom_num);
	~Loader();
	

private:
	CSVRow* csv_row;
	ifstream* file;
};

#endif