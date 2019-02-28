
function make_r2u2_octave(FN)

cur_dir = pwd;
cd(FN);
r2u2prepare='../../../tools/LTL2R2U2/src/r2u2prepare';
unix(sprintf('%s %s.txt',r2u2prepare,FN));

AT='../../at_matlab_none.c';
formula_pt=[FN '_pt.c'];
intervals_pt=[FN '_pti.c'];
formula_ft=[FN '_ft.c'];
intervals_ft=[FN '_fti.c'];

mkoctfile('-v','-DR2U2_STANDALONE','-I.','-I../../../../R2U2_SW/R2U2_C/TL','-I../../../../R2U2_SW/R2U2_C/AT','-I../../../../R2U2_SW/R2U2_C/AT/prognostics',
          './r2u2.cc',
          '../../../../R2U2_SW/R2U2_C/TL/TL_globals.c','../../../../R2U2_SW/R2U2_C/TL/TL_init.c','../../../../R2U2_SW/R2U2_C/TL/TL_update.c','../../../../R2U2_SW/R2U2_C/TL/TL_update_pt.c','../../../../R2U2_SW/R2U2_C/TL/TL_update_ft.c','../../../../R2U2_SW/R2U2_C/TL/TL_queue_pt.c', '../../../../R2U2_SW/R2U2_C/TL/TL_queue_ft.c',
          '../../../../R2U2_SW/R2U2_C/AT/circbuffer.c','../../../../R2U2_SW/R2U2_C/AT/filter_filt.c','../../../../R2U2_SW/R2U2_C/AT/filter_movavg.c','../../../../R2U2_SW/R2U2_C/AT/filter_rate.c','../../../../R2U2_SW/R2U2_C/AT/filter_regex.c',
          AT, formula_pt, intervals_pt, formula_ft, intervals_ft)
cd(cur_dir)