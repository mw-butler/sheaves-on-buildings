RootsUnderBasis:=function(G);
	B:=Matrix(Rationals(),SimpleRoots(G));
	return [r * (B^-1) : r in PositiveRoots(G)];
end function;

RootLevel:=function(G,J,r)
	vec:=RootsUnderBasis(G)[RootPosition(G,r)];
	if #J eq Rank(G) then 
		return 0;
	else
		return &+[vec[i] : i in {1..Rank(G)} diff J];
	end if;
end function;

RootShape:=function(G,J,r)
	vec:=RootsUnderBasis(G)[RootPosition(G,r)];
	for i in J do
		vec[i]:=0;
	end for;
	return RootPosition(G,vec*SimpleRoots(G));
end function;

//T. Selection of toral elements.
TorusSubgroup:=function(G, SimpleRootSubset)
	seq:=Sort(Setseq(SimpleRootSubset));
	return Generators(StandardMaximalTorus(G))[seq];
end function;

//B. Complete Borel (all positive roots plus T).
BorelSubgroup:=function(G)
	FF,phi:=AdditiveGroup(G`K);
	FieldGens:=[phi(f) : f in Generators(FF)];
	R:=Roots(G);
	return &cat[[elt<G|<k,f>> : k in {1..#R/2}] : f in FieldGens] cat
		   Generators(StandardMaximalTorus(G));
end function;

//P. Parabolic (Borel plus selected negative roots).
ParabolicSubgroup:=function(G, SimpleRootSubset)
	FF,phi:=AdditiveGroup(G`K);
	FieldGens:=[phi(f) : f in Generators(FF)];
	R:=Roots(G);
	N:={j + #R/2 : j in SimpleRootSubset};
	return &cat[[elt<G|<k,f>> : k in N] : f in FieldGens] cat BorelSubgroup(G);
end function;

//U. Unipotent radical of P (Positive roots not included in Levi).
USubgroup:=function(G, SimpleRootSubset)
	FF,phi:=AdditiveGroup(G`K);
	FieldGens:=[phi(f) : f in Generators(FF)];
	R:=Roots(G);
	pCoreRoots:={1..#R/2} diff RootClosure(RootDatum(G),SimpleRootSubset);
 	return &cat[[elt<G|<k,f>> : k in pCoreRoots] : f in FieldGens];
end function;

//Z(U). Center of Unipotent radical.
ZUSubgroup:=function(G, SimpleRootSubset)
	FF,phi:=AdditiveGroup(G`K);
	FieldGens:=[phi(f) : f in Generators(FF)];
	RootLevels:=[RootLevel(G,SimpleRootSubset,r) : r in PositiveRoots(G)];
	HighestLevel:=Max(RootLevels);
 	return &cat[[elt<G|<k,f>> : k in Indices(RootLevels,HighestLevel)] : f in FieldGens];
end function;

//M. Levi without any torus, except the bit given to us by the root subgroups.
MSubgroup:=function(G, SimpleRootSubset)
	FF,phi:=AdditiveGroup(G`K);
	FieldGens:=[phi(f) : f in Generators(FF)];
	R:=Roots(G);
	N:={IntegerRing() | j + #R/2 : j in SimpleRootSubset};
	RootsInLevi:=RootClosure(RootDatum(G), SimpleRootSubset join N);
 	return &cat[[elt<G|<k,f>> : k in RootsInLevi] : f in FieldGens];
end function;

//Levi. Full torus of G, plus A_n's as selected.
LSubgroup:=function(G, SimpleRootSubset)
 	return MSubgroup(G, SimpleRootSubset) cat Generators(StandardMaximalTorus(G));
end function;

RepresentationSubgroup:=function(V, gens)
	return sub<Codomain(V) | [g @ V : g in gens]>;
end function;

//Shorthand for above
RS:=function(V, gens)
	return RepresentationSubgroup(V, gens);
end function;

ProperRootSubsets:=function(G)
	d:=Rank(G);
	SimpleRootSubsets:=[J : J in Subsets({1..d}) diff {{1..d}}];
	return Sort(SimpleRootSubsets, func<x, y | #x - #y>);
end function;