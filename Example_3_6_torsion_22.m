// ################################################################################################
// ################################### DEFINITION OF PARAMETERS ###################################
// ################################################################################################

// Field of definition F_q of the elliptic curve E:

p := 19;
r := 2;
q := p^r;
F_q<a> := GF(q);

// Elliptic curve E defined over F_q:

A<x> := PolynomialRing(F_q);
F := x^3 + a;
E := EllipticCurve(F); // E: y^2 = F(x)

// Trace of Frobenius:

N := #E;
t := q + 1 - N;

// Discriminant of Z[Forb_q]:

Delta_Frob := t^2 - 4*q;

// Printing parameters:

print "";
print "##################### ELLIPTIC CURVE PARAMETERS: ######################";
print "";
print E;
print "The number of points of E(F_q) is:", N;
print "The norm of Frobenius is:", q;
print "The trace of Frobenius is:", t;
print "The discriminant of Z[Frob_q] is:", Delta_Frob;

if t mod p eq 0 then
    print "E IS SUPERSINGULAR!!! Choose another elliptic curve";
    quit;
else
    "E is ordinary :)";
end if;

print "";
print "";


// ################################################################################################
// ############################ DETERMINING GOOD PRIMES FOR FROBENIUS #############################
// ################################################################################################

// We define m as the product of the first n primes l such that (Delta_Frob/l) = -1.

good_primes := [];
l := 2;
n := 2;
counter := 1;

while #good_primes lt n and counter lt 1000 do
    if l eq 2 then
        if (Delta_Frob mod 8 eq 5) or (Delta_Frob mod 8 eq 3) then // Check if (Delta_Frob/2) = -1.
            Append(~good_primes, l);
        end if;
    else
        if LegendreSymbol(Delta_Frob, l) eq -1 then  // Check if (Delta_Frob/2) = -1.
            Append(~good_primes, l);
        end if;
    end if;
    l := NextPrime(l);
    counter +:= 1;
end while;

if #good_primes eq 0 then
    print "Not good primes found :(";
    quit;
end if;

// Define m:

m := 1;
for i in [1..#good_primes] do
    m *:= good_primes[i];
end for;

print "################ CHOICE OF m AND DISTORTION PROPERTY: #################";
print "";
print "We fix m = ", m, ", for whcih Forb_q is a distortion map for E[m]";



// ################################################################################################
// ####################### FIELD OF DEFINITION OF THE FIRST m-TORSION POINT #######################
// ################################################################################################

// Compute the degree of the minimal extension of F_q with a rational point P of order m. By
// theorem 6 in Verheul's paper "Evidence that XTR Is More Secure than Supersingular Elliptic
// Curve Cryptosystems", this extension is also the minimal field of definition of E[m].

// Endomorphism algebra of E:
K<sqrtD> := QuadraticField(Delta_Frob);

// Define the Frobenius characteristic polynomial: x^2 - t*x + q over K

K_x<x> := PolynomialRing(K);
charpoly := x^2 - t*x + q;

// Factor the characteristic polynomial of Frobenius over K and extract its roots:

fac_charpoly := Factorization(charpoly);
root1 := -Coefficient(fac_charpoly[1][1], 0);
root2 := -Coefficient(fac_charpoly[2][1], 0);

// Use the Weil conjectures to find the smallest d such that  #E(F_q^{d}) is divisible by m:

d := 0;
not_divisible := true;
counter := 1;

while not_divisible and counter lt 100 do
d +:= 1; 
    N := q^d +1 - root1^d - root2^d;
    N := Integers()!N;
    if N mod m eq 0 then
        not_divisible := false;
    end if;
    counter +:= 1;
end while;

if counter lt 1000 then
    print "Degree of minimal extension of F_q where E[m] is defined:", d;
else
    print "Could not find a point of order m :(";
end if;


// ################################################################################################
// ######################### FIELD OF DEFINITION OF E[m] AND THEIR POINTS #########################
// ################################################################################################

// Define the field of definition of E[m]:

F_qq<b> := GF(q^d);
E_ext := BaseChange(E, F_qq);

// Define the m-division polynomial ψ_m(y) over F_qq:

R<X> := PolynomialRing(F_qq);
psi_m := DivisionPolynomial(E_ext, m); // Define the m-division polynomial ψ_m(y) over F_q.
factors := Factorization(psi_m); // Factor ψ_m(y).

// Extract the points of E[m] over F_qq:

E_m := [];

for g in factors do
    alpha := -Coefficient(g[1], 0);  // This gives the x-coordinate of an m-torsion point
    beta := SquareRoot(alpha^3 + a); // This gives the y-coordinate of an m-torsion point
    Append(~E_m, [alpha,beta]);
    if beta ne 0 then
        Append(~E_m, [alpha,-beta]);
    end if;
end for;



// ################################################################################################
// ######################### CHECKING THE DISTORTION PROPERTY FOR FROB_q ##########################
// ################################################################################################

// We chek that for every point P in E[m], ord(P) = ord(e_m(P,Frob_q(P)).

if #good_primes eq n then
    distortion := true;
    for P in E_m do
        Q := [P[1]^q,P[2]^q]; // Q = Frob_q(P)
        e_PQ := WeilPairing(E_ext!P, E_ext!Q, m);
        if Order(e_PQ) ne Order(E_ext!P) then
            distortion := false;
            print "The distortion property fails!!!!";
            quit;
        end if;
    end for;
    print "The modified Weil pairing verifies the distortion property";
end if;
quit;