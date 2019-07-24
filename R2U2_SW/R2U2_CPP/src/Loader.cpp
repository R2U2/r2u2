#include <iterator>
#include <iostream>
#include <fstream>
#include <sstream>
#include <vector>
#include <string>
#include "Loader.h"

Loader::Loader(std::string filename) {
	file = new ifstream(filename.c_str());
	csv_row = new CSVRow;
}

Loader::~Loader() {
	delete file;
	delete csv_row;
}

bool Loader::has_next() {
	//return true;
	return csv_row->readNextRow(*file);
}

std::vector<std::string> Loader::load_next() {
	return csv_row->m_data;
}

int Loader::get(int atom_num) {
	return std::stoi(csv_row->m_data[atom_num],nullptr);
}


