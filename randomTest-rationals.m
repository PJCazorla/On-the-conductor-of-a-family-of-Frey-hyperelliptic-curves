/*************************************************
** MODULE NAME: randomTest-rationals
**
** Authors: Pedro-Jose Cazorla Garcia and 
**          Lucas Villagra Torcomian
**
** Affiliations: Universidad Pontificia Comillas, Spain
**               Simon Fraser University, Canada
**
** Description: This module includes the functions allowing 
**              to numerically confirm the validity of the 
**              the main result of the article over the rationals,
**              thereby computing the conductor of the curve
**                  C : y^2 = F(x),
**              over Q, for several parameters of z and s.
**              
** Article: Cazorla-Garcia, P.J. and Villagra Torcomian, L.
**          "On the conductor of a family of Frey hyperellip-
**          tic curves", available online in arxiv.
**
**************************************************/

/********************************************************
** AUXILIARY FUNCTIONS 
*********************************************************

/******************************************************
** Name: Minpolw
** Description: Given a prime number r >= 5, this function
**              returns the minimal polynomial of 
**              K = Q(zeta_r + zeta_r^{-1}).
**
** Arguments: r -> Prime number r >= 5.
**            
** Output: The minimal polynomial of K.
******************************************************/
function Minpolw(r); 
    Cycl<zeta> := CyclotomicField(r);
    K<w> := sub<Cycl | zeta + 1/zeta>;
    return MinimalPolynomial(w);
end function;

/********************************************************
** INPUT PARAMETERS
*********************************************************

/* Change these parameters to run a different batch of 
   random tests. */

/* Number of random cases to be tested. */
nCases := 2;

/* Maximum size, in absolute value of s and z. In other 
   words, s and z will be random integers with |s| <= maxSize
   and |z| <= maxSize. */
maxSize := 100;

/* List with the possible values of r, which will be randomly
   chosen. This list should only contain prime numbers >= 5. */
rValues := [5,7];

/* Parameter determining whether the correct results will be printed 
   or not. Incorrect results will always be printed, as well as the 
   beginning and end of the program.*/
verbose := true;

/******************************/

P<x> := PolynomialRing(Integers());
nIncorrect := 0;

print "Beginning of the execution.";

/* Main loop: the program does not stop until nCases have been considered */
for i in [1..nCases] do
	
	/* The value of r is randomly chosen from the possible ones. This value
	   will not be reshuffled. */
	r := Random(rValues);	
	Q<y> := PolynomialRing(pAdicField(r, 30));
	
	
	/* We generate a pair of valid elements (s,z) and keep looping until we find them.
       We recall that an element is valid if v_q(z^r) > v_q(s) for all primes q dividing s and Delta=s^2-z^{2r},
	   and such that the associated hyperelliptic curve is indeed a hyperelliptic curve.
    */
	valid := false;
	
	while not valid do 
	   
		s := Random(-maxSize, maxSize);
		z := Random(-maxSize, maxSize);
		
		/* If s = 0, it is impossible for v_q(s) to be less than v_q(z^r), and 
		   so the pair is automatically invalid, and so we look for a new one. */
		if s ne 0
			/* Condition 1: We check that the divisibility condition is 
			   satisfied. */
			primesDividingS := [q: q in PrimeDivisors(s) | IsOdd(q)];
			
			valid := true;
			for q in primesDividingS do
				if Valuation(s, q) ge r*Valuation(z, q) then 
					valid := false;
					break;
				end if;
			end for;	
			
			/* Condition 2: We check that the polynomial defining the 
			   hyperelliptic curve is non-singular. */
			
			if valid then 
				/* We build the polynomial f(x) */
				f := x^r;
				fadic := y^r;
				for k in [1..(r-1)/2] do  
					ck:=Integers()!(r*Binomial(r-k,k)/(r-k));
					
					/* For some of the conditions, it will be relevant to consider 
					   the polynomial over Qr, and we do so by defining an AUXILIARY
					   polynomial fadic. */
					f := f + ck*(-1)^k*z^(k)*x^(r-2*k);
					fadic := fadic + ck*(-1)^k*z^(k)*y^(r-2*k);
				end for;
				
				f := f + s;
				fadic := fadic + s;

				/* We check if f has repeated roots by computing its discriminant */
				if Discriminant(f) eq 0 then 
					valid := false;
				end if;

			end if;
		end if;
	end while;
	
	/* At this point, we know that the pair is valid, and we may begin the computation  
	   of the conductor. */
	   
	if verbose then 
		print "------------------";
		print "Test case ", i;
		print "f=", f, "s=", s, ", z=", z;
	end if;
	
	/* Computation of the conductor of the curve. */	
	C := HyperellipticCurve(f);
   	cond := Conductor(C);
    
	/* We define the quantity Delta. */
	Delta := s^2-4*z^(r);
	
	/* Firstly, we check that the primes of bad reductions are precisely
	   2, r and those primes dividing delta. */
	badRed := PrimeDivisors(cond);
	if not(Set(badRed) eq Set([2, r] cat PrimeDivisors(Delta))) then 
		print "Problematic case (s = ", s, ", z= ", z, ", r = ", r, ") - the set of bad reduction is ", badRed, ", but it should be", [2, r] cat PrimeDivisors(Delta);
	end if;

	/* If the set of primes of bad reductions coincide, we check the exponent at odd places. */
    for q in [q : q in badRed | q gt 2] do 

    	/* Now we run each case/row of Table 1 */

		/* ROW 1 : q not equal to r and q does not divide s. */
		if (q ne r) and (s mod q) ne 0 then 
			if Valuation(cond, q) ne (r-1)/2 then
				nIncorrect +:= 1;
				print "CASE Q1: prime q=", q, ", expected=", (r-1)/2, ", actual=", Valuation(cond, q);
			elif verbose then 
				print "CASE Q1: prime q=", q, ", expected=", (r-1)/2, ", actual=", Valuation(cond, q);
			end if;
	
		/* ROW 2 : q not equal to r and q divides s */ 
        elif q ne r then 
			if Valuation(cond, q) ne (r-1) then
				nIncorrect +:= 1;
				print "CASE Q2: prime q=", q, ", expected=", r-1, ", actual=", Valuation(cond, q);
			elif verbose then 
				print "CASE Q2: prime q=", q, ", expected=", r-1, ", actual=", Valuation(cond, q);
			end if;
		
		/* ROW 3: q equal to r and q does not divide Delta, with f reducible. */
		elif (Delta mod r) ne 0 and not IsIrreducible(fadic) then 
			if Valuation(cond, q) ne r-1 then 
				nIncorrect +:= 1;
				print "CASE R1: prime q=r=", r, ", not dividing delta with f reducible, expected=", (r-1), ", actual=", Valuation(cond, q);
			elif verbose then 
				print "CASE R1: prime q=r=", r, ", not dividing delta with f reducible, expected=", (r-1), ", actual=", Valuation(cond, q);
			end if;
			
		/* ROW 4: q equal to r and q does not divide Delta, with f irreducible. */
		elif (Delta mod r) ne 0 and IsIrreducible(fadic) then 
			if Valuation(cond, q) ne r then 
				nIncorrect +:= 1;
				print "CASE R2: prime q=r=", r, ", not dividing delta with f irreducible, expected=", r, ", actual=", Valuation(cond, q);
			elif verbose then 
				print "CASE R2: prime q=r=", r, ", not dividing delta with f irreducible, expected=", r, ", actual=", Valuation(cond, q);
			end if;
			
		/* ROW 5: q equal to r and q divides Delta and s */
		elif (s mod r) eq 0 then 
			if Valuation(cond, q) ne 2*r-1 then 
				nIncorrect +:= 1;
				print "CASE R3: prime q=r=", r, ", dividing delta and s, expected=", (2*r-1), ", actual=", Valuation(cond, q);
			elif verbose then 
				print "CASE R3: prime q=r=", r, ", dividing delta and s, expected=", (2*r-1), ", actual=", Valuation(cond, q);
			end if;
			
		/* ROW 6: q equal to r and q divides Delta with v(Delta) = 1 and does not divide s. */
		elif Valuation(Delta, r) eq 1 then 
			if Valuation(cond, q) ne (3*r-1)/2 then 
				nIncorrect +:= 1;
				print "CASE R4: prime q=r=", r, ", with r not dividing s and v(Delta) = 1, expected=", (3*r-1)/2, ", actual=", Valuation(cond, q);
			elif verbose then 
				print "CASE R4: prime q=r=", r, ", with r not dividing s and v(Delta) = 1, expected=", (3*r-1)/2, ", actual=", Valuation(cond, q);
			end if;
		
		/* ROW 7: q equal to r and q divides Delta with v(Delta) = 2 and does not divide s. */
		elif Valuation(Delta, r) eq 2 then 
			if Valuation(cond, q) ne r then 
				nIncorrect +:= 1;
				print "CASE R5: prime q=r=", r, ", with r not dividing s and v(Delta) = 2, expected=", (r), ", actual=", Valuation(cond, q);
			elif verbose then 
				print "CASE R5: prime q=r=", r, ", with r not dividing s and v(Delta) = 2, expected=", (r), ", actual=", Valuation(cond, q);
			end if;
		
		/* ROW 8: q equal to r and q divides Delta with v(Delta) >= 2 and does not divide s. */
		else 
			if Valuation(cond, q) ne r-1 then
				nIncorrect +:= 1;
				print "CASE R6: prime q=r=", r, ", with r not dividing s and v(Delta)>=3, expected=", r-1, ", actual=", Valuation(cond, q);
			elif verbose then 
				print "CASE R6: prime q=r=", r, ", with r not dividing s and v(Delta)>=3, expected=", r-1, ", actual=", Valuation(cond, q);
			end if;
		end if;

    end for;  

end for;

print "End of the execution. Total cases=", nCases, ", correct cases=", nCases-nIncorrect, ", incorrect cases=", nIncorrect;
