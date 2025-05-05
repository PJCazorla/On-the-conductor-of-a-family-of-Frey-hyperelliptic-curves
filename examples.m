/*************************************************
** MODULE NAME: examples.m
**
** Authors: Pedro-Jose Cazorla Garcia and 
**          Lucas Villagra Torcomian
**
** Affiliations: Universidad Pontificia Comillas, Spain
**               Simon Fraser University, Canada
**
** Description: This module includes examples for each of 
**              the rows in Tables 1 and 2 in the article
**              cited below, and confirms numerically that 
**              the results proved therein are true.
**
**              
** Article: Cazorla-Garcia, P.J. and Villagra Torcomian, L.
**          "On the conductor of a family of Frey hyperellip-
**          tic curves", available online in arxiv.
**
**************************************************/

/******************************************************
** Name: Minpolw
** Description: Given a prime number r >= 3, this function
**              returns the minimal polynomial of 
**              K = Q(zeta_r + zeta_r^{-1}).
**
** Arguments: r -> Prime number r >= 3.
**            
** Output: The minimal polynomial of K.
******************************************************/
function Minpolw(r); 
    Cycl<zeta> := CyclotomicField(r);
    K<w> := sub<Cycl | zeta + 1/zeta>;
    return MinimalPolynomial(w);
end function;

/******************************************************
** Name: pol_C
** Description: Given a prime number r >= 3, as well as 
**              the integers s and z, this function
**              returns the defining polynomial of C, 
**              as a polynomial over K. For convenience,
**              it also returns the same polynomial over
**              the r-adic integers.
**
** Arguments: s -> Integer parameter.
**            z  -> Integer parameter, corresponding to z.
**            r -> Prime number r >= 3.
**            
** Output: The defining polynomial of C, both over K 
**         and over Qr.
******************************************************/
function pol_C(s, z, r); 

	/* Definition of the number fields and polynomial rings. */
    Kreal :=  NumberField(Minpolw(r));
	S<x> := PolynomialRing(Kreal);
	Q<y> := PolynomialRing(pAdicField(r, 30));
	
	pol := x^r;
	poladic := y^r;
	for k in [1..(r-1)/2] do  
		ck:=Integers()!(r*Binomial(r-k,k)/(r-k));
		pol := pol + ck*(-1)^k*z^(k)*x^(r-2*k);
		poladic := poladic + ck*(-1)^k*z^(k)*y^(r-2*k);
	end for;
	
	pol := pol + s;
	poladic := poladic + s;
	
	return pol, poladic;
end function;

/******************************************************
** Name: checkConductorQ
** Description: Given the parameters z and s of the curve
**              C(z,s) and a prime q, this function checks 
**              if the conductor exponent of the curve over 
**              Q agrees with its theoretical value. If 
**              verbose is true, it prints the row it 
**              corresponds to and displays additional 
**              information.
**
** Arguments: z,s -> Parameters of the curve whose conductor
**                   we wish to 
**            q -> Prime for which we want to compute the 
**                 conductor exponent.
**            r -> Degree of the polynomial defining C.
**
** Parameters: verbose -> If set to true, additional infor-
**                        mation is displayed.
**            
** Output: true if the value corresponds to the proved value.
**         false if not.
******************************************************/
function checkConductorQ(z, s, q, r : verbose := false)

	/* We first check that the parameters are valid, i.e.
       that for any prime number dividing s and z, the valuation
       of z^r is greater than that of s.	   */
	assert s ne 0;
	
	primesDividingS := [q: q in PrimeDivisors(s) | IsOdd(q)];
	
	for prime in primesDividingS do
		assert Valuation(z,prime) eq 0 or Valuation(s, prime) lt r*Valuation(z, prime);
	end for;
	
	/* We build the polynomial and check that it defines a 
	   hyperelliptic curve. */
	f, fadic := pol_C(s, z, r);
	assert Discriminant(f) ne 0;
	
	/* We compute the conductor exponent of the curve. */
	C := HyperellipticCurve(PolynomialRing(Integers())!f);
	cond := Conductor(C);

	/* Main loop: we check that it corresponds to its theo-
	   retical value (see Table 1). */
	   
	Delta := s^2-4*z^r;

	/* ROW 1 : q not equal to r and q does not divide s. */
	if q ne r and (s mod q) ne 0 then 
		if verbose then 
			print "ROW 1/Q: prime q=", q, ", expected=", (r-1)/2, ", actual=", Valuation(cond, q);
		end if;
		
		if Valuation(cond, q) ne (r-1)/2 then
			return false;
		end if;
	
	/* ROW 2 : q not equal to r and q divides s */ 
    elif q ne r then 
		if verbose then 
			print "ROW 2/Q: prime q=", q, ", expected=", r-1, ", actual=", Valuation(cond, q);
		end if;
			
		if Valuation(cond, q) ne (r-1) then
			return false;
		end if;
		
	/* ROW 3: q equal to r and q does not divide Delta, with f reducible. */
	elif (Delta mod r) ne 0 and not IsIrreducible(fadic) then 
		if verbose then 
			print "ROW 3/Q: prime q=r=", r, ", not dividing delta with f reducible, expected=", (r-1), ", actual=", Valuation(cond, q);
		end if;	
			
		if Valuation(cond, q) ne (r-1) then 
			return false;
		end if;
			
	/* ROW 4: q equal to r and q does not divide Delta, with f irreducible. */
	elif (Delta mod r) ne 0 and IsIrreducible(fadic) then 
		if verbose then 
			print "ROW 4/Q: prime q=r=", r, ", not dividing delta with f irreducible, expected=", r, ", actual=", Valuation(cond, q);
		end if;
		
		if Valuation(cond, q) ne r then 
			return false;
		end if;
		
	/* ROW 5: q equal to r and q divides Delta and s */
	elif (s mod r) eq 0 then 
		if verbose then 
			print "ROW 5/Q: prime q=r=", r, ", dividing delta and s, expected=", (2*r-1), ", actual=", Valuation(cond, q);
		end if;
	
		if Valuation(cond, q) ne (2*r-1) then 
			return false;
		end if;
			
	/* ROW 6: q equal to r and q divides Delta with v(Delta) = 1 and does not divide s. */
	elif Valuation(Delta, r) eq 1 then 
		if verbose then 
			print "ROW 6/Q: prime q=r=", r, ", with r not dividing s and v(Delta) = 1, expected=", (3*r-1)/2, ", actual=", Valuation(cond, q);
		end if;
		
		if Valuation(cond, q) ne (3*r-1)/2 then 
			return false;
		end if;
		
	/* ROW 7: q equal to r and q divides Delta with v(Delta) = 2 and does not divide s. */
	elif Valuation(Delta, r) eq 2 then 
		if verbose then 
			print "ROW 7/Q: prime q=r=", r, ", with r not dividing s and v(Delta) = 2, expected=", (r), ", actual=", Valuation(cond, q);
		end if;
			
		if Valuation(cond, q) ne r then 
			return false;
		end if;
		
	/* ROW 8: q equal to r and q divides Delta with v(Delta) >= 2 and does not divide s. */
	else 
		if verbose then 
			print "ROW 8/Q: prime q=r=", r, ", with r not dividing s and v(Delta)>=3, expected=", r-1, ", actual=", Valuation(cond, q);
		end if;
		
		if Valuation(cond, q) ne r-1 then
			return false;
		end if;
		
	end if;
	
	return true;

end function;

/******************************************************
** Name: checkConductorK
** Description: Given the parameters z and s of the curve
**              C(z,s) and a prime q, this function checks 
**              if the conductor exponent of the curve over 
**              a prime over q of the ring of integers of 
** 				the field K = Q(zeta_r + zeta_r^{-1}
**              agrees with its theoretical value. If 
**              verbose is true, it prints the row it 
**              corresponds to and displays additional 
**              information.
**
** Arguments: z,s -> Parameters of the curve whose conductor
**                   we wish to 
**            q -> Integer prime. We will compute the conductor
**                 exponent for a prime ideal \id{q} above q.
**            r -> Degree of the polynomial defining C.
**
** Parameters: verbose -> If set to true, additional infor-
**                        mation is displayed.
**            
** Output: true if the value corresponds to the proved value.
**         false if not.
******************************************************/
function checkConductorK(z, s, q, r : verbose := false)

	/* We first check that the parameters are valid, i.e.
       that for any prime number dividing s, the valuation
       of z^r is greater than that of s.	   */
	assert s ne 0;
	
	primesDividingS := [q: q in PrimeDivisors(s) | IsOdd(q)];
	
	for prime in primesDividingS do
		assert Valuation(z,prime) eq 0 or Valuation(s, prime) lt r*Valuation(z, prime);
	end for;
	
	/* We build the polynomial and check that it defines a 
	   hyperelliptic curve. */
	f, fadic := pol_C(s, z, r);
	assert Discriminant(f) ne 0;
	
	/* We compute the conductor exponent of the curve. */
	C := HyperellipticCurve(f);
	cond := Conductor(C);

	/* Since we are interested in the conductor exponent 
	   above the prime q, we pick the correct ideal. */
	for id in Factorisation(cond) do 
		if Norm(id[1]) mod q eq 0 then 
			condExp := id[2];
			break;
		end if;
	end for;

	/* Main loop: we check that it corresponds to its theo-
	   retical value. */
	Delta := s^2-4*z^r;
	
	/* ROW 1 : q not equal to r and q does not divide s. */
	if q ne r and (s mod q) ne 0 then 
		if verbose then 
			print "ROW 1/K: prime q=", q, ", expected=", (r-1)/2, ", actual=", condExp;
		end if;
		
		if condExp ne (r-1)/2 then
			return false;
		end if;
	
	/* ROW 2 : q not equal to r and q divides s */ 
    elif q ne r then 
		if verbose then 
			print "ROW 2/K: prime q=", q, ", expected=", r-1, ", actual=", condExp;
		end if;
			
		if condExp ne (r-1) then
			return false;
		end if;
		
	/* ROW 3: q equal to r and q does not divide Delta, with f reducible. */
	elif (Delta mod r) ne 0 and not IsIrreducible(fadic) then 
		if verbose then 
			print "ROW 3/K: prime q=r=", r, ", not dividing delta with f reducible, expected=", (r-1), ", actual=", condExp;
		end if;	
			
		if condExp ne (r-1) then 
			return false;
		end if;
			
	/* ROW 4: q equal to r and q does not divide Delta, with f irreducible. */
	elif (Delta mod r) ne 0 and IsIrreducible(fadic) then 
		if verbose then 
			print "ROW 4/K: prime q=r=", r, ", not dividing delta with f irreducible, expected=", 3*(r-1)/2, ", actual=", condExp;
		end if;
		
		if condExp ne 3*(r-1)/2 then 
			return false;
		end if;
		
	/* ROW 5: q equal to r and q divides Delta and s */
	elif (s mod r) eq 0 then 
		if verbose then 
			print "ROW 5/K: prime q=r=", r, ", dividing delta and s, expected=", (r-1)*(r+2)/2, ", actual=", condExp;
		end if;
	
		if condExp ne (r-1)*(r+2)/2 then 
			return false;
		end if;
			
	/* ROW 6: q equal to r and q divides Delta with v(Delta) = 1 and does not divide s. */
	elif Valuation(Delta, r) eq 1 then 
		if verbose then 
			print "ROW 6/K: prime q=r=", r, ", with r not dividing s and v(Delta) = 1, expected=", (r-1)*(r+5)/4, ", actual=", condExp;
		end if;
		
		if condExp ne (r-1)*(r+5)/4 then 
			return false;
		end if;
		
	/* ROW 7: q equal to r and q divides Delta with v(Delta) = 2 and does not divide s. */
	elif Valuation(Delta, r) eq 2 then 
		if verbose then 
			print "ROW 7/K: prime q=r=", r, ", with r not dividing s and v(Delta) = 2, expected=", 3*(r-1)/2, ", actual=", condExp;
		end if;
			
		if condExp ne 3*(r-1)/2 then 
			return false;
		end if;
		
	/* ROW 8: q equal to r and q divides Delta with v(Delta) >= 2 and does not divide s. */
	else 
		if verbose then 
			print "ROW 8/K: prime q=r=", r, ", with r not dividing s and v(Delta)>=3, expected=", r-1, ", actual=", condExp;
		end if;
		
		if condExp ne r-1 then
			return false;
		end if;
		
	end if;
	
	return true;

end function;

/*******************************************************************
************** MAIN EXAMPLES OF THE PROGRAM ************************
*******************************************************************/

// We run some examples for each row of Tables 1 and 2

		  
// ROW 1: Case q \neq r, q \nmid s

//Set of values [r,q,s,z]
Set:=[[5,7,4,9],[5,7,4,16],[5,7,6,4],[5,7,6,25],[5,7,6,81],\
	[5,7,12,64],[5,7,16,1]];

for x in Set do
	r:=x[1];
	q:=x[2];
	s:=x[3];
	z:=x[4];

print "r=", r, "q=", q, "s=", s, "z=", z, ":";
if not checkConductorQ(z,s,q,r : verbose := true) then
	print "ERROR IN ROW 1 (Q)";
end if;

if not checkConductorK(z,s,q,r : verbose := true) then
	print "ERROR IN ROW 1 (K)";
end if;

end for;

// ROW 2: Case q \neq r, q \mid s

//Set of values [r,q,s,z]
Set:=[[5,7,14,196],[5,7,14,441],[5,7,28,49]]; 

for x in Set do
	r:=x[1];
	q:=x[2];
	s:=x[3];
	z:=x[4];

print "r=", r, "q=", q, "s=", s, "z=", z, ":";
if not checkConductorQ(z,s,q,r : verbose := true) then
	print "ERROR IN ROW 2 (Q)";
end if;

if not checkConductorK(z,s,q,r : verbose := true) then
	print "ERROR IN ROW 2 (K)";
end if;

end for;

// ROW 3: Case q=r, r \nmid Delta, F reducible

//Set of values [r,q,s,z]
Set:=[[5,5,18,4],[5,5,18,49],[5,5,18,64]]; 

for x in Set do
	r:=x[1];
	q:=x[2];
	s:=x[3];
	z:=x[4];

print "r=", r, "q=", q, "s=", s, "z=", z, ":";
if not checkConductorQ(z,s,q,r : verbose := true) then
	print "ERROR IN ROW 3 (Q)";
end if;

if not checkConductorK(z,s,q,r : verbose := true) then
	print "ERROR IN ROW 3 (K)";
end if;

end for;

// ROW 4: Case q=r, r \nmid Delta, F irreducible

//Set of values [r,q,s,z]
Set:=[[5,5,2,4],[5,5,4,1],[5,5,4,16]]; 

for x in Set do
	r:=x[1];
	q:=x[2];
	s:=x[3];
	z:=x[4];

print "r=", r, "q=", q, "s=", s, "z=", z, ":";
if not checkConductorQ(z,s,q,r : verbose := true) then
	print "ERROR IN ROW 4 (Q)";
end if;

if not checkConductorK(z,s,q,r : verbose := true) then
	print "ERROR IN ROW 4 (K)";
end if;

end for;

// ROW 5: Case q=r, r \mid z, r \mid Delta, F irreducible

//Set of values [r,q,s,z]
Set:=[[5,5,20,25],[7,7,14,49]]; 

for x in Set do
	r:=x[1];
	q:=x[2];
	s:=x[3];
	z:=x[4];

print "r=", r, "q=", q, "s=", s, "z=", z, ":";
if not checkConductorQ(z,s,q,r : verbose := true) then
	print "ERROR IN ROW 5 (Q)";
end if;

if not checkConductorK(z,s,q,r : verbose := true) then
	print "ERROR IN ROW 5 (K)";
end if;

end for;

// ROW 6: Case q=r, r \nmid s, v(Delta)=1

//Set of values [r,q,s,z]
Set:=[[5,5,4,4],[5,5,4,49],[5,5,8,1],[5,5,6,4]]; 

for x in Set do
	r:=x[1];
	q:=x[2];
	s:=x[3];
	z:=x[4];

print "r=", r, "q=", q, "s=", s, "z=", z, ":";
if not checkConductorQ(z,s,q,r : verbose := true) then
	print "ERROR IN ROW 5 (Q)";
end if;

if not checkConductorK(z,s,q,r : verbose := true) then
	print "ERROR IN ROW 5 (K)";
end if;

end for;

// ROW 7: Case q=r, r \nmid s, v(Delta)=2

//Set of values [r,q,s,z]
Set:=[[5,5,2,16],[5,5,2,36],[5,5,14,4]]; 

for x in Set do
	r:=x[1];
	q:=x[2];
	s:=x[3];
	z:=x[4];

print "r=", r, "q=", q, "s=", s, "z=", z, ":";
if not checkConductorQ(z,s,q,r : verbose := true) then
	print "ERROR IN ROW 5 (Q)";
end if;

if not checkConductorK(z,s,q,r : verbose := true) then
	print "ERROR IN ROW 5 (K)";
end if;

end for;

// ROW 8: Case q=r, r \rnmid z, v(Delta) >= 3 (F reducible)

//Set of values [r,q,s,z]
Set:=[[5,5,14,9],[5,5,14,484],[5,5,14,784]]; 

for x in Set do
	r:=x[1];
	q:=x[2];
	s:=x[3];
	z:=x[4];

print "r=", r, "q=", q, "s=", s, "z=", z, ":";
if not checkConductorQ(z,s,q,r : verbose := true) then
	print "ERROR IN ROW 5 (Q)";
end if;

if not checkConductorK(z,s,q,r : verbose := true) then
	print "ERROR IN ROW 5 (K)";
end if;

end for;
