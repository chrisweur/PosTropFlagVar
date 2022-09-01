-*---------------------------------------------------------------------------------------------
M2 code accompanynig section 8 of "Polyhedral and tropical geometry of flag positroids"
Author: Christopher Eur
Last update: 9/1/2022

Comments:
* Fl_5 data imported from [Bossinger-Lamboglia-Mincheva-Mohammadi], available at:
https://github.com/Saralamboglia/Toric-Degenerations/blob/master/Flag5.rtf
* Thanks Lara Bossinger for sharing a computer ready TrGr(3,6) data
* Thanks Jonathan Boretsky for identifying the Bruhat intervals in the coherent subdivisions
* Some long computations were done on the server germain.math.harvard.edu
---------------------------------------------------------------------------------------------*-

needsPackage "Matroids"
needsPackage "Polyhedra"
needsPackage "Tropical"

--given a list L that is a permutation of {0,..,n-1}, considered as a coordinate point,
--outputs the corresponding sequence of elements whose first consecutive sums give the coordinate
vecToChain = L -> reverse apply(#L, i -> position(L, j -> j == i))

--my regular subdivision that corrects for the random labelling when the lifted polyhedron is formed
myRegSubdiv = (M,w) -> (
    PR := convexHull(M||w,matrix (toList(numRows M:{0})|{{1}}));
    V := (vertices PR)^(apply(n, i -> i));
    R := (sort select(faces (1,PR), f -> #(f#1) ==0))/(f -> V_(f#0))/sort
    )

--the flag Dressian via the three-term incidence Plucker relations
flagDressian = n -> (
    p := symbol p;
    E := set toList(0..(n-1));
    R := QQ[apply(drop(drop(subsets elements E,-1),1), s -> p_s)];
    plucker := hashTable apply(gens R, i -> (set last baseName i,i));
    ijkSpairs := flatten apply(subsets(E,3), l -> apply(subsets(E - l), s -> (l,s)));
    apply(ijkSpairs, l -> (
	    (t,s) := (sort elements l_0, l_1);
	    plucker#(s + set t_{0}) * plucker#(s + set t_{1,2}) -
	    plucker#(s + set t_{1}) * plucker#(s + set t_{0,2}) +
	    plucker#(s + set t_{2}) * plucker#(s + set t_{0,1})
	    )
	)
    )


end

---------------------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------


------------<(iv) & (v): explicit parametrizations for Fl_5 and Fl_4  >----------


--Fl_4 parametrization
restart
load "Eur_PosTropFlagVar_upload.m2"

R = QQ[a,b,c,d,e,f, MonomialOrder=>Lex];
use R
--a pair (S,f) indicates that the plucker coordinate of S gets the parametrization f
H = hashTable {
    (set {1}, 1),
    (set {2}, a+d+f),
    (set {3}, a*b + a*e + d*e),
    (set {4}, a*b*c),
    (set {1,2}, 1),
    (set {1,3}, b+e),
    (set {1,4}, b*c),
    (set {2,3}, b*d+b*f+e*f),
    (set {2,4}, b*c*d + b*c*f),
    (set {3,4}, b*c*d*e),
    (set {1,2,3}, 1),
    (set {1,2,4}, c),
    (set {1,3,4}, c*e),
    (set {2,3,4}, c*e*f)
    }

select(delete(1,values H), i -> #(terms i)>1)
L = apply(oo, f -> transpose matrix flatten ((terms f)/exponents))

P = L/convexHull
time Q = sum P
time fVector Q
F = normalFan Q
linealitySpace F
faces F
rays F

--the extra cluster variable
f = H#(set{2})*H#(set{1,3,4})-H#(set{1})*H#(set{2,3,4})
P' = P | {convexHull transpose matrix flatten ((terms f)/exponents)}
Q' = sum P'
fVector Q'

--parametrization of the positive Fl_5
restart
load "Eur_PosTropFlagVar_upload.m2"

R = QQ[a,b,c,d,e,f,g,h,i,j, MonomialOrder=>Lex];
use R
H = hashTable {
    (set {1}, 1), 
    (set {2}, a+e+h+j),
    (set {3}, a*b+a*f+a*i+e*f+e*i+h*i),
    (set {4}, a*b*c+a*b*g+a*f*g+e*f*g),
    (set {5}, a*b*c*d),
    (set {1,2}, 1),
    (set {1,4}, b*c + b* g + f*g),
    (set {1,5}, b*c*d),
    (set {2,3}, b*e+b*h+b*j+f*h+f*j+i*j),
    (set {2,4}, b*c*e+b*c*h+b*c*j+b*g*e+b*g*h+b*g*j+f*g*h+f*g*j),
    (set {2,5}, b*c*d*e+b*c*d*h+b*c*d*j),
    (set {3,4}, b*c*e*f+b*c*e*i+b*c*h*i+b*g*e*i+b*g*h*i+f*g*h*i),
    (set {3,5}, b*c*d*e*f+b*c*d*e*i+b*c*d*h*i),
    (set {4,5}, b*c*d*e*f*g),
    (set {1,2,3}, 1),
    (set {1,2,4}, c+g),
    (set {1,2,5}, c*d),
    (set {1,3,4}, c*f+c*i+g*i),
    (set {1,3,5}, c*d*f+c*d*i),
    (set {1,4,5}, c*d*f*g),
    (set {2,3,4}, c*f*h+c*f*j+c*i*j+g*i*j),
    (set {2,3,5}, c*d*f*h+c*d*f*j+c*d*i*j),
    (set {2,4,5}, c*d*f*g*h + c*d*f*g*j),
    (set {3,4,5}, c*d*f*g*h*i),
    (set {1,2,3,4}, 1),
    (set {1,2,3,5}, d),
    (set {1,2,4,5}, d*g),
    (set {1,3,4,5}, d*g*i),
    (set {2,3,4,5}, d*g*i*j)
    }
    
select(delete(1,values H), i -> #(terms i)>1)
L = apply(oo, f -> transpose matrix flatten ((terms f)/exponents))

-*----computed germain.math.harvard.edu server, about 1 week
--output saved as the file "TrFl5pos_(iv).txt"
--DO NOT RUN ON LAPTOP: 
P = L/convexHull
Q1 = sum P_{0,1,2,3,4}
vertices Q1
Q2 = sum P_{5,6,7,8,9}
vertices Q2
Q3 = sum P_{10,11,12,13,14}
vertices Q3
Q13 = Q1+Q3
vertices Q13
Q123=Q13 + Q2
Q123
fVector Q123
f = openOut "TrFlpos_(iv).txt";
f << toString Q123 << endl;
close f
-------*-


----------------------------------------------------------------------------------------------
----------------< understanding TrFl_4^+ and coherent subdivisions from it>-------------------
restart
load "Eur_PosTropFlagVar_upload.m2"

n = 4
I = ideal flagDressian n

--the fan structure (i) for FlDr_4 ( = TrFl_4 by [BEZ21] )
F = tropicalPrevariety I_* 
fVector F
R = rays F
SQ = select(faces(0,F), f -> #f > 3) --the three "squares" that becomes subdivided in (ii) 

--the fan structure (ii) for FlDr_4 ( = TrFl_4 by [BEZ21] )
F = fan tropicalVariety I 
fVector F
SQ = select(faces(0,F), f -> #f > 3) -- no squares now


--book-keeping: going between variable named by a subset and its index
var = (gens ring I)/baseName/last;
var = hashTable apply(#var, i -> (var_i,i))
toVar = hashTable ((pairs var)/reverse);


--check three-term positive-tropical incidence relations
checkPosRels = v -> all(I_*, f -> (
	T := (terms f)/exponents/first/(i -> positions(i, j -> j ==1));
	min {sum(v_(T_0)), sum(v_(T_2))} == sum(v_(T_1))
	)
    )


--positive part of the TrFl_4, using Corollary 3.12
posRays = select(numcols R, i -> checkPosRels (flatten entries R_i))
posFacets = select(faces(0,F), f -> isSubset(f,posRays))

--given a vector v in 2^n - 2, corresponding to the var elements, outputs the weight that it gives
--to a coordiante p in the permutohedron
vecToWeight = (v,p) -> (
    c := (vecToChain p);
    sum(n-1, i -> v_(var#(sort c_(toList(0..i)))))
    )

--subdivisions from the simplicial faces of (i) of TrFl_4^+
P = permutations 4
M = transpose matrix P
SP = apply(posFacets, q -> (
	v := sum(q, i -> (i+1) * R_i);
	w := matrix {apply(P, i -> vecToWeight(v,i))};
	time (myRegSubdiv(M,w)/sort)
	)
    )

--check that ones subdividing into six parts are cubes
SP/(i -> #i)
sixes = select(SP, i -> #i == 6);
unique flatten apply(sixes, i -> i/convexHull/fVector)

-----------------------------------------------------------------------------------------------
-----------------------------< positive TrFl_5 computation >-----------------------------------

restart
load "Eur_PosTropFlagVar_upload.m2"

------------ recovering full TrFl_5 from the S5 x| Z2 orbits -------------------

--load the file from Bossinger, Lamboglia, Mincheva, Mohammadi (BLMM) github repo
f = openIn "TropOfFlag5_M2Input.txt"
L = value get f;
maxOrbitReps = last L_0;
raysF = -transpose sub(matrix (last L_1),QQ); --the minus converts from "max" convention to "min"
linSp = transpose sub(matrix (last L_2),QQ);


--simplify the rays using the lineality space
redRaysF = raysF % linSp;
redRaysF = transpose matrix apply(numcols redRaysF, i -> (
	l := entries redRaysF_i;
	c := min(select(l/abs, i -> i != 0));
	l/c
	)
    )

--ring manually entered
R = QQ[p_0, p_1, p_2, p_3, p_4,
       p_{0, 1}, p_{0, 2}, p_{1, 2}, p_{0, 3}, p_{1, 3}, p_{2, 3}, p_{0, 4},
       p_{1, 4}, p_{2, 4}, p_{3, 4}, p_{0, 1, 2}, p_{0, 1, 3}, p_{0, 2, 3},
       p_{1, 2, 3}, p_{0, 1, 4}, p_{0, 2, 4}, p_{1, 2, 4}, p_{0, 3, 4}, p_{1, 3,
       4}, p_{2, 3, 4}, p_{0, 1, 2, 3}, p_{0, 1, 2, 4}, p_{0, 1, 3, 4}, p_{0, 2,
       3, 4}, p_{1, 2, 3, 4}]

--the variable names
S = (gens R)/baseName/last/(i -> if class i === ZZ then {i} else i)/set

--vector in QQ^30 gets converted to a hash-table of pairs (Set,QQ)
vecToSet = v -> hashTable apply(#S, i -> (S_i,v_i))
vecToSet raysF_3
vecToSet redRaysF_3

--The S5 action on the coordinates of QQ^30
S5on30 = hashTable apply(permutations 5, p -> (
	(p,apply(S, s -> position(S, i -> i === set p_(elements s))))
	)
    )

--Given a permutation p on {0,..,4} and a ray v in TrFl_5, outputs index of the ray corresponding
--to the image of the action p*v
S5onARay = (p,v) -> (
    l := entries v;
    w := vector apply(S5on30#p, i -> l_i);
    j := select(numcols redRaysF, i -> matrix (redRaysF_i - w) % linSp == 0);
--    j := select(numcols redRaysF, i -> min first SVD sub(matrix (redRaysF_i - w) | linSp,RR) < 10^(-4));
    if #j != 1 then error "not one" else first j
    )

--sanity checks
S5onARay({0,1,2,3,4},redRaysF_35)== 35 --true
S5onARay({1,0,2,3,4},redRaysF_3)== 3 --true
S5onARay({1,0,2,4,3},redRaysF_3)== 3 --should be false
--apply(numcols redRaysF, i -> time S5onARay(p,redRaysF_i))

-*--- about 30 minutes to run; file saved to "S5OnRaysSave"
--hash table recording the action of S5 on the rays of TrFl_5
S5OnRays = hashTable apply(permutations 5, p -> (
	(p, apply(numcols redRaysF, i -> S5onARay(p,redRaysF_i))) 
	)
    )

f = openOut "S5OnRaysSave"
f << toString S5OnRays << endl
close f
---*-

f = openIn "S5OnRaysSave.txt"
S5OnRays = value get f; --hash table recording the action of S5 on the rays of TrFl_5

--action of Z2 on a vector v in QQ^30
Z2onARay = v -> (
    w := vector reverse entries v;
    j := select(numcols redRaysF, i -> matrix (redRaysF_i - w) % linSp == 0);
    if #j != 1 then error "not one" else first j
    )

--sanity check
m = Z2onARay redRaysF_200
m = Z2onARay redRaysF_m --back to 200

--the Z2 action on the rays of TrFl_5
Z2OnRays = apply(numcols redRaysF, i -> Z2onARay redRaysF_i) --12 sec

--maxCells by permuting the orbit representatives by S5 and then by Z2 actions
maxCellsAlmost = flatten apply(maxOrbitReps, r -> unique apply(keys S5OnRays, k -> sort apply(r, i -> (S5OnRays#k)_i)));
maxCells = unique flatten apply(maxCellsAlmost, i -> {i, Z2OnRays_i}/sort);
#maxCells == 69780 --in agreement with [Theorem 5, BLMM]

-------the positive part of TrFl_5---------
I = ideal flagDressian 5

--subsets appearing in the three-terms
toCheck = apply(I_*, f -> (
	T := (terms f);
	p := select(T, t -> sub(first flatten entries last coefficients t,QQ) > 0);
	m := select(T, t -> sub(first flatten entries last coefficients t,QQ) < 0);
	p = p/support/(l -> l/baseName/last/set);
	m = m/support/(l -> l/baseName/last/set);
	(p,m)
	)
    );

--given a hashTable of pairs (Set,ZZ), checks the three-term positive-tropical incidences
checkPosRels = H -> all(toCheck, (p,m) -> (
	min {sum(p_0, i -> H#i), sum(p_1, i -> H#i)} == sum(m_0, i -> H#i)
	)
    )

--given a hashTable of pairs (Set,ZZ), checks the three-terms tropical incidences
checkTropRels = H -> all(toCheck, (p,m) -> (
	L := {sum(p_0, i -> H#i), sum(p_1, i -> H#i), sum(m_0, i -> H#i)};
	c := min L;
	#select(L, i -> i == c) > 1
	)
    )

--sanity check
H = vecToSet redRaysF_3
checkPosRels H --shouldn't be in the pos
checkTropRels H --is in TrFl
time all(numcols redRaysF, i -> checkTropRels vecToSet redRaysF_i) --all the rays are in TrFl

--the rays in the positive TrFl_5
posRays = time select(numcols redRaysF, i -> checkPosRels vecToSet redRaysF_i)

--the maximal cells whose rays are in the positive part ( = TrFl_5^+ by Corollary 3.12)
posCells = select(maxCells, i -> all(i, j -> member(j,posRays)));
--check that the sum of the rays in the max cells are in the positive part
all(posCells, l -> checkPosRels vecToSet sum(l, i -> redRaysF_i))
tally posCells/(i -> #i)


----------------------------------------------------------------------------------------------
-----------------------------------< Grassmannian Gr(3,6) >-----------------------------------
restart
load "Eur_PosTropFlagVar_upload.m2"

--load data
raysF = sub(- transpose matrix value get openIn "rays_Gr36.txt",QQ); --minus to convert to "min" from "max"
linSp = sub(transpose matrix value get openIn "linSp_Gr36.txt",QQ);
maxCells = value get openIn "maxCones_Gr36.txt";


--simplify the rays using the lineality space
redRaysF = raysF % linSp;
redRaysF = transpose matrix apply(numcols redRaysF, i -> (
	l := entries redRaysF_i;
	c := min(select(l/abs, i -> i != 0));
	l/c
	)
    );

--the variable order
R = QQ[p_123,p_124,p_125,p_126,p_134,p_135,p_136,p_145,p_146,p_156,p_234,p_235,p_236,p_245,p_246,p_256,p_345,p_346,p_356,p_456]
S = (gens R)/baseName/last/toString/characters/(i -> i/(j -> (value j) -1))
R = QQ[S/(i -> p_i)]
varR = hashTable apply(gens R, r -> (set (last baseName r),r))
vecToSet = v -> hashTable apply(#S, i -> (set S_i,v_i))
redRaysF_2, vecToSet redRaysF_2 --sanity check

--Plucker ideal
I' = Grassmannian(2,5)
R' = (ring I') ** QQ;
I' = sub(I',R');
phi = map(R,R',apply(gens R', r -> r => varR#(set toList last baseName r)))
I = phi I'; --Plucker ideal in R


--three-terms
threeTerms = select(I_*, f -> #(terms f) == 3); --should be 30 of them
#threeTerms
toCheck = apply(threeTerms, f -> (
	T := (terms f);
	p := select(T, t -> sub(first flatten entries last coefficients t,QQ) > 0);
	m := select(T, t -> sub(first flatten entries last coefficients t,QQ) < 0);
	p = p/support/(l -> l/baseName/last/set);
	m = m/support/(l -> l/baseName/last/set);
	(p,m)
	)
    );

--given a hashTable of pairs (Set,ZZ), checks the three-term positive-tropical incidences
checkPosRels = H -> all(toCheck, (p,m) -> (
	min {sum(p_0, i -> H#i), sum(p_1, i -> H#i)} == sum(m_0, i -> H#i)
	)
    )

--given a hashTable of pairs (Set,ZZ), checks the three-terms tropical incidences
checkTropRels = H -> all(toCheck, (p,m) -> (
	L := {sum(p_0, i -> H#i), sum(p_1, i -> H#i), sum(m_0, i -> H#i)};
	c := min L;
	#select(L, i -> i == c) > 1
	)
    )

--sanity check: all rays indeed satisfy trop three-term rels
all(numcols redRaysF, i -> checkTropRels vecToSet redRaysF_i)

--sanity check2: sums of rays in every maximal cell satisfies trop three-terms
all(maxCells, c -> checkTropRels vecToSet sum(c, i -> (random(ZZ) + 1)*redRaysF_i))

--the rays in the positive trop
posRays = time select(numcols redRaysF, i -> checkPosRels vecToSet redRaysF_i)

--the maximal cells whose rays are in the positive part
posCells = select(maxCells, i -> all(i, j -> member(j,posRays)))

--sanity check that the sum of the rays in the max cells are in the positive part
all(posCells, l -> checkPosRels vecToSet sum(l, i -> redRaysF_i))

--bi-tetrahedras
midEdges = select(subsets(posRays,2), i -> #select(posCells, p -> isSubset(i,p)) == 3)
(e1,e2) = toSequence midEdges
bitetra1 = select(posCells, p -> isSubset(e1,p))
bitetra2 = select(posCells, p -> isSubset(e2,p))

--my version of leadTerm: initial ideal given a weight (with the "min" convention)
--I: the ideal, and w: weight, i.e. a list of numbers whose length equals #(gens ring I) 
leadTerm(Ideal,List) := (I,w) -> (
    if #(gens ring I) != #w then error "the weight list not right size";
    R := ring I;
    R' := (coefficientRing R)[gens R, MonomialOrder => {Weights => w/(i -> -sub(i,ZZ))}, Global => false];
    I' := sub(I,R');
    sub(leadTerm(1,I'),R)
    )

--sanity checks: initial ideals from trop have no monomials
ideal leadTerm(I,entries redRaysF_0);
apply(oo_*, i -> #terms i)
ideal leadTerm(I,entries sum(first random maxCells, i -> redRaysF_i));
all(oo_*, i -> #terms i > 1)

--sanity check that every posCell really gives initial ideal with no monomial
all(posCells, c -> all((ideal leadTerm(I,entries sum(c, i -> redRaysF_i)))_*, i -> #(terms i)>1))


--analyzing initial ideals of bi-tetrahedra 1
(x,y,a,b,c) = (1,22,11,12,39)
J1 = ideal leadTerm(I, entries (30* redRaysF_x + redRaysF_y + redRaysF_a + redRaysF_b));
J2 = ideal leadTerm(I, entries (redRaysF_x + 30* redRaysF_y + redRaysF_a + redRaysF_b));
J3 = ideal leadTerm(I, entries (30* redRaysF_x + redRaysF_y + redRaysF_a + redRaysF_c));
J4 = ideal leadTerm(I, entries (redRaysF_x + 30* redRaysF_y + redRaysF_a + redRaysF_c));
J1 == J2, J3 == J4 --should be true
J2 == J3 --should be false

--analyzing initial ideals of bi-tetrahedra 2
(x,y,a,b,c) = (9,34,14,16,43)
J1 = ideal leadTerm(I, entries (30* redRaysF_x + redRaysF_y + redRaysF_a + redRaysF_b));
J2 = ideal leadTerm(I, entries (redRaysF_x + 30* redRaysF_y + redRaysF_a + redRaysF_b));
J3 = ideal leadTerm(I, entries (30* redRaysF_x + redRaysF_y + redRaysF_a + redRaysF_c));
J4 = ideal leadTerm(I, entries (redRaysF_x + 30* redRaysF_y + redRaysF_a + redRaysF_c));
J1 == J2, J3 == J4 --should be true
J2 == J3 --should be false

