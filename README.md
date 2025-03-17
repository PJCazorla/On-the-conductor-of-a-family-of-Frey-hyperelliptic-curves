This repository contains functions to check the validity of the main result (Theorem 0.1) in the article
  Cazorla-García, P.J. and Villagra-Torcomian, L., "ON THE CONDUCTOR OF A FAMILY OF FREY HYPERELLIPTIC
  CURVES". Please report any issues with the code to the authors!

All programs are written in MAGMA (see https://magma.maths.usyd.edu.au/magma/handbook/ for a MAGMA
handbook)

As of right now, the repository contains two files:
  - randomTest-rationals.m : By changing the parameters, the code allows for numerical verification
                             of the conductor of several curves C(z,s) over the rationals.
    
  - randomTest-numberField.m : By changing the parameters, the code allows for numerical verification
                             of the conductor of several curves C(z,s) over the number field K, which
                             is the maximal totally real subextension of the cyclotomic field.
