// Construct the Cayley algebra over F, using the basis from
// Wilson "The Finite Simple Groups" (2009, Springer-Verlag
// London), p.123

CayleyAlgebra:=function(F)

	AlgMult:=Matrix(IntegerRing(), [[ 0, 0, 0, 0, 1, 2,-3,-4],
									[ 0, 0,-1, 2, 0, 0,-5, 6],
									[ 0, 1, 0, 3, 0,-5, 0,-7],
									[ 1, 0, 0, 4, 0, 6, 7, 0],
									[ 0, 2, 3, 0, 5, 0, 0, 8],
									[-2, 0,-4, 0, 6, 0, 8, 0],
									[ 3,-4, 0, 0, 7,-8, 0, 0],
									[-5,-6, 7, 8, 0, 0, 0, 0]]);

	Quo:=&cat[&cat[AlgMult[i,j] eq 0 select [0 : x in [1..8]] else 
		Eltseq(Rows(Sign(AlgMult[i,j]) * 
		IdentityMatrix(IntegerRing(),8))[Abs(AlgMult[i,j])])  
		: j in [1..8]] : i in [1..8]];
	CA:=Algebra<F, 8 | Quo>;

	return CA;

end function;


// Elements A(\lambda), ..., F(\lambda) from Wilson p.124, and 
// toral elements T_1(\lambda), T_2(\lambda)

Alam:=function(F, lam)
	mat:=IdentityMatrix(F,8);
	mat[7,1]:=-lam;
	mat[8,2]:=lam;
	return mat;
end function;

Blam:=function(F, lam)
	mat:=IdentityMatrix(F,8);
	mat[6,1]:=-lam;
	mat[8,3]:=lam;
	return mat;
end function;

Clam:=function(F, lam)
	mat:=IdentityMatrix(F,8);
	mat[4,1]:=-lam;
	mat[5,1]:=lam;
	mat[6,2]:=-lam;
	mat[7,3]:=lam;
	mat[8,5]:=lam;
	mat[8,4]:=-lam;
	mat[8,1]:=lam^2;
	return mat;
end function;

Dlam:=function(F, lam)
	mat:=IdentityMatrix(F,8);
	mat[3,1]:=-lam;
	mat[4,2]:=-lam;
	mat[5,2]:=lam;
	mat[7,4]:=-lam;
	mat[7,5]:=lam;
	mat[7,2]:=lam^2;
	mat[8,6]:=lam;
	return mat;
end function;

Elam:=function(F, lam)
	mat:=IdentityMatrix(F,8);
	mat[3,2]:=-lam;
	mat[7,6]:=lam;
	return mat;
end function;

Flam:=function(F, lam)
	mat:=IdentityMatrix(F,8);
	mat[2,1]:=-lam;
	mat[4,3]:=lam;
	mat[5,3]:=-lam;
	mat[6,4]:=lam;
	mat[6,5]:=-lam;
	mat[6,3]:=lam^2;
	mat[8,7]:=lam;
	return mat;
end function;

T1lam:=function(F, lam)
	return DiagonalMatrix(F,[lam,1,lam,1,1,lam^-1,1,lam^-1]);
end function;

T2lam:=function(F, lam)
	return DiagonalMatrix(F,[1,lam,lam^-1,1,1,lam,lam^-1,1]);
end function;


// Construct G=G_2(F), along with subgroups U, T, B, 
// Pp, and Pl

G2Subgroups:=function(F)

	FStar:={f : f in F | f ne 0};

	r:=ZeroMatrix(F,8,8);
	r[1,1]:=-1;
	r[2,3]:=-1;
	r[3,2]:=-1;
	r[4,4]:=1;
	r[5,5]:=1;
	r[6,7]:=-1;
	r[7,6]:=-1;
	r[8,8]:=-1;

	s:=ZeroMatrix(F,8,8);
	s[1,2]:=-1;
	s[2,1]:=-1;
	s[3,6]:=-1;
	s[4,5]:=1;
	s[5,4]:=1;
	s[6,3]:=-1;
	s[7,8]:=-1;
	s[8,7]:=-1;

	Ugens:=[Alam(F, l) : l in F] cat [Blam(F, l) : l in F] cat [Clam(F, l) : l in F]
		 cat [Dlam(F, l) : l in F] cat [Elam(F, l) : l in F] cat [Flam(F, l) : l in F];

	Tgens:=[T1lam(F, l) : l in FStar] cat [T2lam(F, l) : l in FStar];

	GL8:=GL(8,F);
	U:=sub<GL8 | Ugens>; 	// unipotent radical
	T:=sub<GL8 | Tgens>; 	// torus
	B:=sub<GL8 | U, T>; 	// Borel
	Pp:=sub<GL8 | B, r>; 	// stabiliser of space <x1> (in Wilson's basis)
	Pl:=sub<GL8 | B, s>; 	// stabiliser of space <x1,x2> (in Wilson's basis)
	G:=sub<GL8 | Pp, Pl>; 	// G_2(F)

	return G, Pp, Pl, B, U, T;

end function;


// Construct the generalised hexagon

ConstructHexagon:=function(A, G)
	AVS:=VectorSpace(A);

	Points:=SetToSequence(Orbit(G,sub<AVS | AVS.1>));
	Lines:=SetToSequence(Orbit(G,sub<AVS | A.1,A.2>));
	
	Gr:=Graph<#Points + #Lines | : SparseRep:=true >;

	for i in [1..#Points] do 
		if i mod 500 eq 0 then print Sprint(i) cat "......" cat Sprint(100*RealField(4)!(i/#Points)) cat "%"; end if;
		neighbours:={{i,#Points+x} : x in [1..#Lines] | Points[i].1 in Lines[x]};
		AddEdges(~Gr,neighbours);
	end for;
	V:=VertexSet(Gr);
	E:=EdgeSet(Gr);

	return Points, Lines, Gr, V, E;
end function;


// Alternative, sometimes quicker.

ConstructHexagonChambersOrbit:=function(A, G)
	AVS:=VectorSpace(A);

	Points:=SetToSequence(Orbit(G,sub<AVS | AVS.1>));
	Lines:=SetToSequence(Orbit(G,sub<AVS | AVS.1,AVS.2>));
	Chambers:=SetToSequence(Orbit(G,<sub<AVS | AVS.1>,sub<AVS | AVS.1,AVS.2>>));

	Gr:=Graph<#Points + #Lines | : SparseRep:=true >;

	for i in [1..#Chambers] do 
		if i mod 500 eq 0 then print Sprint(i) cat "......" cat Sprint(100*RealField(4)!(i/#Chambers)) cat "%"; end if;
		AddEdge(~Gr,Position(Points,Chambers[i,1]),#Points+Position(Lines,Chambers[i,2]));
	end for;
	V:=VertexSet(Gr);
	E:=EdgeSet(Gr);

	return Points, Lines, Gr, V, E;
end function;


// Construct a vector in VecSp whose entries are all 0,
// except that the sequence seq is inserted starting from
// index n.

PadVector:=function(VecSp, n, seq)
	v:=VecSp!0;
	for i in seq do;
		v[n]:=i;
		n:=n+1;
	end for;
	return v;
end function;

// The following function computes H_0 as a quotient of
// C_0, which can be useful. However, it has very high memory
// usage since the relations are stored as a standard Magma
// matrix object rather than a sparse matrix, and so (on my 
// laptop) it only works for GF(5) and smaller.

ComputeH0:=function(CA, Gr, Points, Lines)

	F:=BaseRing(CA);
	E:=EdgeSet(Gr);

	// The bottom chain space C0
	dim:=#Points+2*#Lines;
	C0:=VectorSpace(F,dim);

	// Each edge e in E represents a chamber (a point-line pair).
	// ChPtSpaces and ChLnSpaces are sequences containing the 
	// respective subspaces of the Cayley algebra associated with 
	// the point and line of each chamber.
	ChPtSpaces:=[Points[Index(Min(EndVertices(x)))] : x in E];
	ChLnSpaces:=[Lines[Index(Max(EndVertices(x)))-#Points] : x in E];
	// ChPtVec and ChLnVec contain the vectors in C0 associated 
	// with the point and line of each chamber.
	ChPtVec:=[PadVector(C0,Index(Min(EndVertices(x))), [1]) : x in E];
	ChLnVec:=[PadVector(C0,#Points+(2*(Index(Max(EndVertices(E.i)))-#Points))-1, 
		Eltseq(Morphism(sub<VectorSpace(CA)|ChPtSpaces[i]>,
		sub<VectorSpace(CA)|ChLnSpaces[i]>))) : i in [1..#E]];
	// Each edge in the graph gives us a relation in B0 as the 1-space
	// of the point is identified with a 1-subspce of the line
	Rels:=[ChPtVec[i] - ChLnVec[i] : i in [1..#E]];

	print "RelsComputed";

	B0 :=sub<C0 | Rels>;
	H0, H0map := C0/B0;

	return H0, H0map, C0;
end function;


// This version uses a SparseMatrix to store the B_0 relations,
// which allows us to compute with larger fields.

ComputeRelsMatSparse:=function(CA, Gr, Points, Lines)

	F:=BaseRing(CA);
	E:=EdgeSet(Gr);

	// The bottom chain space C0
	dim:=#Points+2*#Lines;
	C0:=VectorSpace(F,dim);
	AVS:=VectorSpace(CA);

	// Each edge e in E represents a chamber (a point-line pair).
	// PtSpace and LnSpace are the respective subspaces of the 
	// Cayley algebra associated with the point and line of each chamber.
	// The morphism is the embedding of the 1-space (point) into
	// the 2-space (line).
	Rels:=[];
	for i in [1..#E] do
		if i mod 500 eq 0 then print Sprint(i) cat "......" cat Sprint(100*RealField(4)!(i/#E)) cat "%"; end if;
		e:=E.i;
		Pt:=Index(Min(EndVertices(e)));
		Ln:=Index(Max(EndVertices(e)));
		PtSpace:=Points[Pt];
		LnSpace:=Lines[Ln-#Points];
		seq:=Eltseq(Morphism(sub<AVS|PtSpace>,sub<AVS|LnSpace>));
		Append(~Rels,<i,Pt,F!1>);
		Append(~Rels,<i,#Points+(2*(Ln-#Points))-1,F!(-seq[1])>);
		Append(~Rels,<i,#Points+(2*(Ln-#Points)),F!(-seq[2])>);
	end for;
	RelsMat:=SparseMatrix(F,#E,dim,Rels);

	return RelsMat, C0;
end function;


// Usage

F:=GF(7);
CA:=CayleyAlgebra(F);
print "- Cayley algebra constructed.";
G, Pp, Pl, B, U, T:=G2Subgroups(F);
print "- G_2(F) and subgroups constructed.";
Points, Lines, Gr, V, E:=ConstructHexagon(CA, G);
print "- Generalised hexagon constructed.";

// Either:

// H0, H0map, C0:=ComputeH0(CA, Gr, Points, Lines);
// print "- Dimension of H0:", Dimension(H0);

// Or:

RelsMat, C0:=ComputeRelsMatSparse(CA, Gr, Points, Lines);
print "- Dimension of H0:", Dimension(C0) - Rank(RelsMat);