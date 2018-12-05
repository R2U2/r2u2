This is the software-only version of R2U2.

Updated 11.04.17 from the NASA AOS Repository (Standalone Version)

R2U2 matlab/octave standalone:

1. install tools:
      cd tools/LTL*/src
      make
      make install

2. compile/run formula 
     cd src/MATLAB
     << formula in t1.txt >>

     octave

     in octave:
     >> more off

       % compiles formula and builds R2U2
     >> make_r2u2_octave('t1');

       % run r2u2 on some small data and plot
     >> run_t1   

2A. for matlab: similar wrapper
        
3. NOTES:
* The octave/matlab R2U2 only accepts *binary* input values (width=128)
* NO signal preprocessing here

* make_r2u2_octave:  errors during compilation of formulas are shown,
but the build-process continues (must be fixed)

* there are several run*.m scripts, which plot results. Some of them
are also suitable for future time (sync observers). Only output signals
are plotted if they are labeled in the input specification.

* FT: some future time temporal operators are not implemented in this
  version (sync). Async observers haven't been implemented at all.