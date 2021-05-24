
# MTL/LTL C++ Implementation
#### (Require C++11)
---
## Structure Example
![Alt text](https://github.com/LTL-AERO/SystemHealthManagement/tree/master/R2U2/R2U2-SW/MTL/README/structure.bmp?raw=true "Object Connection Structure")

---
## Description :
###You can specify using either assembly code or high level MTL formula.
### 1) Assembly Mode Configuration: 
#### In main file [**MTL.cpp**](https://github.com/LTL-AERO/SystemHealthManagement/tree/master/R2U2/R2U2-SW/MTL/src/MTL.cpp):
#### 1. Assign the sensor number, simulation time stamps;
#### 2. Link the sensor to the [.log](https://github.com/LTL-AERO/SystemHealthManagement/tree/master/R2U2/R2U2-SW/MTL/src/alt.log) file;
```c
//e.g.
sensor[0]=new Event("./src/alt.log");
sensor[1]=new Event("./src/pitch.log");
```
#### In assembly code file [**test.ftasm**](https://github.com/LTL-AERO/SystemHealthManagement/tree/master/R2U2/R2U2-SW/MTL/src/test.ftasm)
#### 1. Write the assembly code in test.ftasm
#### 2. Specify the assembly code file
```c
string asm_file="./src/test.ftasm";
```

### 2) MTL Mode Configuration: 
#### In main file [**MTL.cpp**](https://github.com/LTL-AERO/SystemHealthManagement/tree/master/R2U2/R2U2-SW/MTL/src/MTL.cpp):
#### 1. Assign the sensor number, simulation time stamps;
#### 2. Link the sensor to the [.log](https://github.com/LTL-AERO/SystemHealthManagement/tree/master/R2U2/R2U2-SW/MTL/src/alt.log) file;
#### 3. Write your MTL formula as a string in **MTL.cpp**. For MTL format, see [Notes](#notes);
```c
string formula="AND{AND{S[0],S[1]},ALW[3,5]{S[0]}}";
```
---
### How to run:
#### In terminal:
#### 1. run setup.sh to compile the project
#### 2. type ./Debug/MTL to running MTL
```bash
make
./build/app/main
```
---
## Notes
### Meaning the MTL String:
### Relationship with TACAS14--->
#### Algorithm 1: "!" = "NOT{}"
#### Algorithm 2: "G[2]" = "KEP[2]{}"
#### Algorithm 3: "&" = "AND{,}"
#### Algorithm 4: "G[2,5]" = "ALW[2,5]{}"
#### Algorithm 5: "F[1,2]" = "UNT[1,2]{,}"
```c
//e.g.
string formula="NOT{S[0]}";
string formula="NOT{NOT{S[0]}}";
string formula="KEP[5]{S[1]}";
string formula="NOT{KEP[2]{NOT{S[1]}}}";
string formula="AND{KEP[2]{S[0]},S[1]}";
string formula="ALW[5,10]{S[1]}";
string formula="NOT{AND{ALW[5,10]{S[0]},KEP[2]{S[1]}}}";
string formula="AND{KEP[2]{NOT{NOT{S[0]}}},S[0]}";
string formula="AND{S[1],ALW[0,8]{S[0]}}";
string formula="AND{S[1],KEP[8]{S[0]}}";
string formula="AND{ALW[5,10]{S[0]},KEP[2]{S[1]}}";
string formula="KEP[2]{S[1]}";
string formula="AND{AND{S[0],S[1]},ALW[3,5]{S[0]}}";
```