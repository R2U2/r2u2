from MLTL_Compiler import *
formula = "a0;"
pred_length = 0
pg = Postgraph(MLTL=formula,Hp=int(pred_length),optimize_cse=True)
formula2 = "a2 & a3;\n a1;"
pg = Postgraph(MLTL=formula2,Hp=int(pred_length),optimize_cse=True)
compile_status = "Compile status: "+ pg.status.upper()
# print(pg.asm)