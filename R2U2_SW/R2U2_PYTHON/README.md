# ACOW
#### Metric Linear Temporal Logic Model Checking Tool written in Python 3.X
---
#### What this tool can do:
#### 1) Verication of safety/liveness property
- [ ] Safety: certain (bad) states reachable?
- [x] Liveness: certain (good) states bound to be reached?
#### 2) Bounded and unbounded model checking
- [x] Bounded methods: Only consider traces of up to a maximum length.
- [ ] Unbounded methods: Consider an unlimited number of steps.
---
#### Steps:
1) Create python Environment:
```bash
conda env create -f environment.yml
```
2) Activate the Environment:
```bash
source activate ACOW
```
3) Modefiy the state space model and MTL formula in MTL_main.py. Then run:
```bash
python MTL_main.py
```