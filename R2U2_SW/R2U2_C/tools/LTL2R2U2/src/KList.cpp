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


#include <string>
#include <math.h>
#include "KList.h"
#include "KItem.h"

using std::ostream;
using std::string;
using std::list;


// Constructor
KList::KList() {
  listname = "";
  items.clear();
  uniqueId = 0;
} //end constructor

// Parameterized constructor
KList::KList(string myName, list<KItem> myItems) {
  listname = myName;
  items = myItems;  
  cacheDirty = 1;
  uniqueId = 0;
} //end parameterized constructor

// Copy constructor
KList::KList(const KList &copyin) {
  listname = copyin.listname;
  items = copyin.items;
  cacheDirty = 1;
  uniqueId = 0;
} //end copy constructor

// Destructor
KList::~KList() {
  items.clear();
} //end destructor

// clear the list
void KList::clear() {
  items.clear();
  cacheDirty = 1;
  uniqueId = 0;
} //end clear

// set all the parameters
void KList::setAll(string myName, list<KItem> myItems) {
  listname = myName;
  items = myItems;
  cacheDirty = 1;
} //end setAll

// set the name of the list
void KList::setName(string myName) {
  listname = myName;
} //end setName

// get the name of the list
string KList::getName() {
  return(listname);
} //end getName

// return the size
int KList::size() {
    return(items.size());
} //end size

// add/replace an item
int KList::addItem(KItem k) {
  int idx;
  if (!query(k)) { 
    idx = uniqueId;
    uniqueId++;
	// JSC
    if (k.getInfo()<=0)
        k.setInfo(idx);
    items.remove(k);
    items.push_back(k);
    items.sort();
    cacheDirty = 1;	
    /*DEBUG: fprintf(stderr, "Adding item %s as var #%d -- %d\n", k.getName().c_str(), idx, (int)this);*/
  } //end if 
  else { // already there
    KItem val = find(k);
    idx = val.getInfo();
  } //end else
  return(idx);
} //end addItem

// save an item
int KList::saveItem(KItem k) {
  int result = 0;
  if (query(k)) { 
    items.remove(k);
    items.push_back(k);
    items.sort();
    cacheDirty = 1;	
    result = 1;
  } //end if
  else { // already there
    result = 0;
  } //end else
  return(result);
} //end saveItem

// remove an item from the list
void KList::removeItem(KItem k) {
  items.remove(k);
  cacheDirty = 1;
} //end removeItem

// get items
list<KItem> KList::getItems() {
  list<KItem> dummy = items;
  return(dummy);
} //end getItems

// retrieve an item
KItem KList::find(KItem k) {
  list<KItem> dummy = items;
  int success = 0;
  KItem val;  

  if (!cacheDirty) { // We have a cached result which might work
    if ( k == cached) { // searches match!
      val = cachedResult;
      success = 1;
    } //end if
  } //end if

  // Loop until found
  while((dummy.empty() != 1) && (success == 0)) {
    val = dummy.front();
    dummy.pop_front();
    if (val == k) { // found it!
      success = 1;
    } //end if
  } //end while
  if (success == 0) { // return error
    val.setName("ERR-UNFOUND-KITEM");
  } //end if

  cacheDirty = 0;
  cachedResult = val;
  cached = k;

  return(val);
} //end find

// retrieve an item
string KList::findName(int myIdx) {
  list<KItem> dummy = items;
  int success = 0;
  string retVal;
  KItem val;

  // Loop until found
  while((dummy.empty() != 1) && (success == 0)) {
    val = dummy.front();
    dummy.pop_front();
    if (val.getInfo() == myIdx) { // found it!
      success = 1;
    } //end if
  } //end while
  if (success == 0) { // return error
    val.setName("ERR-UNFOUND-IDX");
  } //end if

  retVal = val.getName();

  return(retVal);
} //end findName

// retrieve an item
KItem KList::findItemByNumber(int myIdx) {
  list<KItem> dummy = items;
  int success = 0;
  KItem val;

  // Loop until found
  while((dummy.empty() != 1) && (success == 0)) {
    val = dummy.front();
    dummy.pop_front();
    if (val.getInfo() == myIdx) { // found it!
      success = 1;
    } //end if
  } //end while
  if (success == 0) { // return error
    val.setName("ERR-UNFOUND-IDX");
  } //end if

  return(val);
} //end findItemByNumber

// query if item exists
int KList::query(KItem k) {
  KItem q;
  KItem dummy;
  dummy.setName("ERR-UNFOUND-KITEM");  

  if (!cacheDirty && (cached == k)) { // cached result which works
    q = cachedResult;
  } //end if
  else { // no cached result which works
    q = find(k);
  } //end else

  cacheDirty = 0;
  cachedResult = q;
  cached = k;

  if (q == dummy) {
    return(0);
  } //end if
  return(1);
} //end query

//print
void KList::print(ostream &out) {
  out << "LIST " << listname << endl << endl;
  
  list<KItem> dummy = items;
  dummy.sort();

  // while not empty
  while (dummy.empty() != 1) {
    KItem k = dummy.front();
    dummy.pop_front();
    out << "\t" << k.getName() << " " << k.getInfo() << endl;
  } //end while
} //end print
