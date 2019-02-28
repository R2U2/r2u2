/*
This software has been determined to be outside the scope of NASA NPG 2210 and
therefore is not considered as controlled software.

This program may be freely redistributed and/or modified under the terms of
this software agreement.

NASA is neither liable nor responsible for maintenance, updating, or
correction of any errors in the software provided.

Use of this software shall not be construed to constitute the grant of a
license to the user under any NASA patent, patent application or other
intellectual property.

THE SOFTWARE IS PROVIDED 'AS IS' WITHOUT ANY WARRANTY OF ANY KIND, EITHER
EXPRESSED, IMPLIED, OR STATUTORY, INCLUDING, BUT NOT LIMITED TO, ANY WARRANTY
THAT THE SOFTWARE WILL CONFORM TO SPECIFICATIONS, ANY IMPLIED WARRANTIES OF
MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE, AND FREEDOM FROM
INFRINGEMENT, AND ANY WARRANTY THAT THE DOCUMENTATION WILL CONFORM TO THE
SOFTWARE, OR ANY WARRANTY THAT THE SOFTWARE WILL BE ERROR FREE.  IN NO EVENT
SHALL NASA BE LIABLE FOR ANY DAMAGES, INCLUDING, BUT NOT LIMITED TO, DIRECT,
INDIRECT, SPECIAL OR CONSEQUENTIAL DAMAGES, ARISING OUT OF, RESULTING FROM, OR
IN ANY WAY CONNECTED WITH THIS SOFTWARE, WHETHER OR NOT BASED UPON WARRANTY,
CONTRACT, TORT , OR OTHERWISE, WHETHER OR NOT INJURY WAS SUSTAINED BY PERSONS
OR PROPERTY OR OTHERWISE, AND WHETHER OR NOT LOSS WAS SUSTAINED FROM, OR AROSE
OUT OF THE RESULTS OF, OR USE OF, THE SOFTWARE OR SERVICES PROVIDED
HEREUNDER.

RECIPIENT AGREES TO WAIVE ANY AND ALL CLAIMS AGAINST THE U.S. GOVERNMENT, THE
U.S. GOVERNMENT'S CONTRACTORS AND SUBCONTRACTORS, AND SHALL INDEMNIFY AND HOLD
HARMLESS THE U.S. GOVERNMENT AND THE U.S. GOVERNMENT'S CONTRACTORS AND
SUBCONTRACTORS FOR ANY DAMAGE THAT MAY BE INCURRED FROM RECIPIENT'S PRIOR OR
FUTURE USE OF THE PROVIDED SOFTWARE, INCLUDING ANY DAMAGES FROM PRODUCTS BASED
ON, OR RESULTING FROM, THE USE THEREOF.  RECIPIENT AGREES TO OBTAIN THIS
IDENTICAL WAIVER OF CLAIMS, INDEMNIFICATION AND HOLD HARMLESS AGREEMENT WITH
ANY ENTITIES THAT ARE PROVIDED WITH TECHNICAL DATA DERIVED FROM USE OF THE
SOFTWARE.

K.Y.Rozier
June, 2011
*/


#include <stdio.h>
#include <string>
#include "KItem.h"
#include "KList.h"

using std::ostream;
using std::string;

// Constructor
KItem::KItem() {
  name = "";
  info = -1;
  outMapping = 0;
} //end constructor

// Parameterized Constructor
KItem::KItem(string myName, int myInfo, int myOutMapping) {
  name = myName;
  info = myInfo;
  outMapping = myOutMapping;
} //end parameterized constructor

// Parameterized Constructor
KItem::KItem(string myName) {
  name = myName;
  info = -1;
  outMapping = 0;
} //end parameterized constructor

// Copy constructor
KItem::KItem(const KItem &copyin) {
  name = copyin.name;
  info = copyin.info;
  outMapping = copyin.outMapping;
} //end copy constructor

// Destructor
KItem::~KItem() {
  // Empty
} //end destructor

// set everything
void KItem::setAll(string myName, int myInfo, int myOutMapping) {
  name = myName;
  info = myInfo;
  outMapping = myOutMapping;
} //end setAll

// set the name of the KItem
void KItem::setName(string myName) {
  name = myName;
} //end setName

// get the name of the KItem
string KItem::getName() {
  return(name);
} //end getName

// set the info of the KItem
void KItem::setInfo(int myInfo) {
  info = myInfo;
} //end setInfo

// get the info of the KItem
int KItem::getInfo() {
  return(info);
} //end getInfo

// set the out degree of the KItem (if it's in a graph)
void KItem::setOutMapping(int myOutMapping) {
  outMapping = myOutMapping;
} //end setOutMapping

// get the out degree of the KItem (if it's in a graph)
int KItem::getOutMapping() {
  return(outMapping);
} //end getOutMapping




//*******************************************************************
// For lists
//*******************************************************************

// =
KItem& KItem::operator=(const KItem &rhs) {
  this->name = rhs.name;
  this->info = rhs.info;
  this->outMapping = rhs.outMapping;
  return *this;
} //end operator=

// ==
int KItem::operator==(const KItem &rhs) const {
  if (this->name == rhs.name) return 1;
  return 0;
} //end operator==

// <
int KItem::operator<(const KItem &rhs) const {
  if (this->name < rhs.name) return 1;
  return 0;
} //end operator<

// print
void KItem::print(ostream &out) {
  out << name << "\t" << info << endl;
} //end print
