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


#ifdef __cplusplus
#include <string>
#include <iostream>
#include <list>
#endif

#ifndef __KList_h_
#define __KList_h_
#include "KItem.h"

#ifdef __cplusplus
using std::ostream;
using std::string;
using std::list;
#endif

class KList {
 public:
  // Constructor
  KList();  

  // Parameterized constructor
  KList(string myName, list<KItem> myItems);

  // Copy constructor
  KList(const KList &copyin);

  // Destructor
  ~KList();

  void clear();
  void setAll(string myName, list<KItem> myItems);
  void setName(string myName);  // set the name of the list
  string getName();             // get the name of the list
  int addItem(KItem k);         // add/replace an item
  int saveItem(KItem k);        // save an item
  void removeItem(KItem k);     // remove an item from the list
  list<KItem> getItems();       // get items
  KItem find(KItem k);          // retrieve an item
  string findName(int idx);     // retrieve an item
  KItem findItemByNumber(int myIdx); // retrieve an item
  int query(KItem k);           // query if item exists
  int size();                   // return size of the list

  // For diagnostics
  void print(ostream &out);

 private:
  string listname;
  list<KItem> items;

  int cacheDirty;
  KItem cached;
  KItem cachedResult;
  int uniqueId;

}; //end KList

#endif
