/*
 * Assembly.h
 *
 *  Created on: Jul 18, 2017
 *      Author: PEI
 */

#ifndef SRC_ASSEMBLY_H_
#define SRC_ASSEMBLY_H_
#include <string>
#include "Observer.h"

using namespace std;
class Assembly {
public:
	Assembly(string);
	void Construct(Observer** sensor,Observer** observer);

	virtual ~Assembly();

public:
	int num_of_observer;
	int subformula_tag;
	int top_ob;

private:
	string filename;
};

#endif /* SRC_ASSEMBLY_H_ */
