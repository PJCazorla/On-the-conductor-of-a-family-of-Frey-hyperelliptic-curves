# Code for the article: On the conductor of a family of Frey hyperelliptic curves.


This repository contains functions to check the validity of the main result in the article
Cazorla-García, P.J. and Villagra Torcomian, L., "On the conductor of a family of Frey hyperelliptic curves", available at https://arxiv.org/abs/2503.21568

Please report any issues with the code to the authors!

All programs are written in MAGMA (see https://magma.maths.usyd.edu.au/magma/handbook/ for a MAGMA
handbook)

# Content:

**• randomTest-rationals.m**: By changing the parameters, the code allows for numerical verification
                             of the conductor of several curves C(z,s) over the rationals.
    
**• randomTest-numberField.m**: By changing the parameters, the code allows for numerical verification
                             of the conductor of several curves C(z,s) over the number field K, which
                             is the maximal totally real subextension of the cyclotomic field.

**• examples.m**: We run some examples for each row of Tables 1 and 2

