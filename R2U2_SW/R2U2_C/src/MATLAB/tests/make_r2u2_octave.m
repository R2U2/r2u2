
function make_r2u2_octave(FN)

cur_dir = pwd;
cd(FN);
r2u2prepare='../../../../tools/bin/r2u2prepare';
unix(sprintf('%s %s.txt',r2u2prepare,FN));

AT='../../at_matlab_none.c';
formula_pt=[FN '_pt.c'];
intervals_pt=[FN '_pti.c'];
formula_ft=[FN '_ft.c'];
intervals_ft=[FN '_fti.c'];

mkoctfile('-v','-DR2U2_STANDALONE','-I.','-I../../../TL','-I../../../AT','-I../../../AT/prognostics','../../r2u2.cc','../../../TL/TL_globals.c','../../../TL/TL_init.c','../../../TL/TL_update.c','../../../TL/TL_update_pt.c','../../../TL/TL_update_ft.c','../../../TL/TL_queue_pt.c', '../../../TL/TL_queue_ft.c','../../../AT/circbuffer.c','../../../AT/filter_filt.c','../../../AT/filter_movavg.c','../../../AT/filter_rate.c','../../../AT/filter_regex.c',AT, formula_pt, intervals_pt, formula_ft, intervals_ft)
cd(cur_dir)