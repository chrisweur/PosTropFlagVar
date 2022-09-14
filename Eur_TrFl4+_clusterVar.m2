----------------------------< Fl_4 extra cluster var Groebner fan >------------------------------
restart
needsPackage "Tropical"

--the flag Dressian via the three-term incidence Plucker relations
--NOTE: saturate with respect to variables if the whole prime ideal is wanted
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

I = ideal flagDressian 4
R = ring I
varR = hashTable apply(gens R, r -> (set (last baseName r),r))
F = fan tropicalVariety I
--F = tropicalPrevariety I_*
S = (gens ring I)/baseName/last/(i -> if class i === ZZ then {i} else i)/set
vecToSet = v -> hashTable apply(#S, i -> (S_i,v_i))
fVector F

linSp = linealitySpace F
redRaysF = rays F % linSp
redRaysF = transpose matrix apply(numcols redRaysF, i -> (
	l := entries redRaysF_i;
	c := min(select(l/abs, i -> i != 0));
	l/c
	)
    )

--given a hashTable of pairs (Set,QQ), checks whether it satisfies the three-terms incidences
--either just tropical (checkTropRels) or the positive-tropical (checkPosRels)
toCheck = apply(I_*, f -> (
	T := (terms f);
	p := select(T, t -> sub(first flatten entries last coefficients t,QQ) > 0);
	m := select(T, t -> sub(first flatten entries last coefficients t,QQ) < 0);
	p = p/support/(l -> l/baseName/last/set);
	m = m/support/(l -> l/baseName/last/set);
	(p,m)
	)
    );

checkPosRels = H -> all(toCheck, (p,m) -> (
	min {sum(p_0, i -> H#i), sum(p_1, i -> H#i)} == sum(m_0, i -> H#i)
	)
    )

checkTropRels = H -> all(toCheck, (p,m) -> (
	L := {sum(p_0, i -> H#i), sum(p_1, i -> H#i), sum(m_0, i -> H#i)};
	c := min L;
	#select(L, i -> i == c) > 1
	)
    )

--sanity check
all(maxCones F, c -> checkTropRels vecToSet sum(c, i -> redRaysF_i))

--posRays and cells
posRays = select(numcols redRaysF, i -> checkPosRels vecToSet redRaysF_i)
posCells = select(maxCones F, c -> isSubset(c,posRays))

--the fan poset structure of (iii) is the associahedra
tally apply(posRays, i -> #select(posCells, c -> member(i,c)))





--extended ring
--from Lauren: extra cluster var is (p3*p12*p134+p1*p34*p123)/p13 = p2*p134-p1*p234, where the
--ground set is {1,2,3,4} instead of {0,1,2,3}
Rext = QQ[gens R,X]
varRE = hashTable apply(keys varR, i -> (i, sub(varR#i,Rext)))
extraX = -varRE#(set{0,2})*X + varRE#(set{2})*varRE#(set{0,1})*varRE#(set{0,2,3})+varRE#(set{0})*varRE#(set{2,3})*varRE#(set{0,1,2})
Iext = sub(I,Rext) + ideal(extraX); --the new extended ideal in extra cluster vars
primaryDecomposition Iext -- shouldn't be prime since not saturated
apply(gens Rext, r -> Iext = trim saturate(Iext,r)); --saturate
isPrime Iext --prime now, since saturated

--make Iext in alternate way to check: here X = non-positive polynomial in pluckers
Iext2 = trim (ideal(X - varRE#(set{1})*varRE#(set{0,2,3}) + varRE#(set{0})*varRE#(set{1,2,3}))+ sub(I,Rext))
apply(gens Rext, r -> Iext2 = trim saturate(Iext2,r));
Iext == Iext2 --the two ways agree

--sanity check
(varRE#(set{1})*varRE#(set{0,2,3}) - varRE#(set{0})*varRE#(set{1,2,3}))*varRE#(set{0,2}) - ( varRE#(set{2})*varRE#(set{0,1})*varRE#(set{0,2,3})+varRE#(set{0})*varRE#(set{2,3})*varRE#(set{0,1,2}))
oo % sub(I,Rext) --should be zero

--given a weight in trop(I) in the original 20 vars, output the weight in trop(Iext)
extW = w -> (
    H := vecToSet w;
    wX := -H#(set{0,2}) + min {H#(set{2})+H#(set{0,1})+H#(set{0,2,3}), H#(set{0})+H#(set{2,3})+H#(set{0,1,2})};
    (entries w) | {wX}
    )

--computes initial ideal
leadTerm(Ideal,List) := (I,w) -> (
    if #(gens ring I) != #w then error "the weight list not right size";
    R := ring I;
    R' := (coefficientRing R)[gens R, MonomialOrder => {Weights => w/(i -> -sub(i,ZZ))}, Global => false];
    I' := sub(I,R');
    sub(leadTerm(1,I'),R)
    )

--check all positive cells have initial ideal with no generator being a positive polynomial
all(posCells, C -> (
	W := extW sum(C, i -> (abs(random ZZ)+1)*redRaysF_i);
	J := ideal leadTerm(Iext, W);
	all(J_*, f -> (
		c := flatten entries last coefficients f;
		#select(c, i -> sub(i,QQ) > 0) > 0 and #select(c, i -> sub(i,QQ) < 0) > 0
		)
	    )
	)
    )


--weak-unique
weakUnique = L -> (
    L' = {};
    apply(L, i -> if all(L', j -> j != i) then L' = L' | {i});
    L'
    )


bad = select(posCells, c -> (
	time L := apply(50, i -> trim ideal leadTerm(Iext, extW sum(c, i -> random(1,50)*redRaysF_i)));
	#weakUnique L != 1
	)
    )
--the square {2,3,17,18}, in (iii) divides into {3,17,18} and {2,3,17}

C = bad_0
W = extW sum(C, i -> abs(random ZZ)*redRaysF_i)
J = trim ideal leadTerm(Iext, W);
all(J_*, i -> #(terms i)>1) --no monomials
L = apply(100, i -> trim ideal leadTerm(Iext, extW sum(C, i -> random(1,40)*redRaysF_i)));
(keys tally L)_{1,2}
L' = weakUnique L
L'_0 != L'_1
L'_1 != L'_2
L'_0 != L'_2

C = {2,3,18} --the other subdivision of square, different from (iii): should be good now
L = apply(100, i -> trim ideal leadTerm(Iext, extW sum(C, i -> random(1,40)*redRaysF_i)));
#weakUnique L ==1 
C = {2,17,18} --the other triangle of the different square
L = apply(100, i -> trim ideal leadTerm(Iext, extW sum(C, i -> random(1,40)*redRaysF_i)));
#weakUnique L ==1 


posCellsVISets = set(posCells/set) + set{set{2,3,18},set{2,17,18}}- set {set {2,3,17}, set {3,17,18}}
posCellsVI = elements(posCellsVISets/elements)
tally apply(posRays, i -> #select(posCellsVI, c -> member(i,c)))

--the two, (iii) and (vi), are isomorphic as simplicial complexes
--(visually, easier to see this on the associahedron)
t = symbol t;
T = QQ[posRays/(i -> t_i)]
varT = hashTable apply(gens T, i -> (last baseName i, i))
Cx1 = monomialIdeal apply(posCells, c -> product(c, i -> varT#i))
Cx2 = monomialIdeal apply(posCellsVI, c -> product(c, i -> varT#i))

L = {t_0 => t_0, t_9 => t_16, t_14 => t_14, t_16 => t_9, t_19 => t_19,
     t_2 => t_3, t_3 => t_2, t_17 => t_18, t_18 => t_17}
transf = map(T,T,L);
Cx2 == transf Cx1
Cx1 == transf Cx2

-*---
toPerm = select(gens T, i -> not member(last baseName i,{2,3,17,18}));
cands1 = apply(permutations 5, p -> apply(#p, i -> toPerm_i => toPerm_(p_i)));
cands2 = apply(permutations {2,3,17,18}, p -> apply(#p, i -> varT#({2,3,17,18}_i) => varT#(p_i)));
cands = (cands1 ** cands2)/flatten;
select(cands, L -> (
	transf := map(T,T,L);
	Cx1' := monomialIdeal apply(posCells, c -> transf product(c, i -> varT#i));
	Cx1' == Cx2
	)
    )
---*-

-----------------< the fan structure (v) >-----------------
A = QQ[a,b,c,d,e,f, MonomialOrder=>Lex];
--a pair (S,f) indicates that the plucker coordinate of S gets the parametrization f
H = hashTable {
    (set {0}, 1_A),
    (set {1}, a+d+f),
    (set {2}, a*b + a*e + d*e),
    (set {3}, a*b*c),
    (set {0,1}, 1_A),
    (set {0,2}, b+e),
    (set {0,3}, b*c),
    (set {1,2}, b*d+b*f+e*f),
    (set {1,3}, b*c*d + b*c*f),
    (set {2,3}, b*c*d*e),
    (set {0,1,2}, 1_A),
    (set {0,1,3}, c),
    (set {0,2,3}, c*e),
    (set {1,2,3}, c*e*f),
    (X, a*c*e + c*d*e)
    }

--compute normal fan of Minkowski sum of Newton polytopes
select(delete(1,values H), i -> #(terms i)>1)
L = apply(oo, f -> transpose matrix flatten ((terms f)/exponents))
Q = sum(L/convexHull)
Polyhedra$fVector Q
FV = normalFan Q
linealitySpace FV
faces FV
rays FV
fVector FV

--tropicalization of a polynomial
trop = f -> (
    R := ring f;
    v -> min apply(exponents f, l -> sum(#l, i -> l_i * v_i))
    )

--the trop map from R^6 to R^14
tropMap = v -> (
    sub(vector apply(S, s -> (trop H#s)(v)),QQ)
    )

--check that the fan structure (v) matches the modification of (iii)
--obtained by flipping the diagonal in "the square"
posRaysV = apply(numcols rays FV, i -> tropMap (rays FV)_i)
posRaysVtoIII = apply(posRaysV, v -> select(numcols redRaysF, i -> (matrix v) % (matrix redRaysF_i | sub(linSp,QQ)) == 0))
posRaysVtoIII = flatten oo
set posRaysVtoIII === set posRays --rays are the same
posCellsV = faces(0,FV)/(l -> apply(l, i -> posRaysVtoIII_i)) 
set(posCellsV/set) =!= set(posCells/set) --doesn't match (iii)
set(posCellsV/set) === set(posCellsVI/set) --but matches (vi) which is (iii) with a diagonal flip
