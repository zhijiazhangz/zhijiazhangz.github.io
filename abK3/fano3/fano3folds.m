//////////////////////////////////////////////////////////////////////////////
//
//		Computing Fano 3-folds with index f
//
//  Gavin Brown, Kaori Suzuki, February 2006, August 2010.
//  Alexander Kasprzyk, April 2012.
//
// Computes all (or all Bogomolov--Kawamata stable) Fano 3-folds.
//

import "suzuki.m":
	fano_Ac,
	fano_hilbert_series,
	fano_hilbert_series_g,
	fano_degree_g;

//////////////////////////////////////////////////////////////////////////////
//  Housekeeping functions --- data types etc.
//////////////////////////////////////////////////////////////////////////////

forward base_genus;

// for P = 1/r(a,b,c) return 1/(rabc).
function proj_loss(P)
    return Rationals() ! (1 / (Index(P) * &*Polarisation(P)));
end function;

intrinsic Fano3fold(f::RngIntElt,B::GRBskt,g::RngIntElt) -> GRFano
{A Fano 3-fold of Fano index f = 1 or 2 and with basket of singularities B
and Fano genus g >= 0}
    require f in {1,2}: "Genus argument only needed when Fano index f = 1 or 2";
    require IsTerminalThreefold(B):
        "Basket must contain only terminal 3-fold singularities";
    require &and[ (f mod Index(p)) eq TerminalPolarisation(p)[1] :
        p in Points(B) ]: "Singularities are not properly polarised "
            * "for the given Fano index f =",f;
    g_min := base_genus(f,B);
    require g ge g_min: "Third argument g must be >=",g_min;
    // make the object X and attach all the Fano data.
    X := HackobjCreateRaw(GRFano);
    X`fanoindex := f;
    X`fanogenus := g;
    X`fanobasegenus := g_min;
    X`basket := B;
    X`dim := 3;
    h,d,a := fano_hilbert_series_g(g,f,B);
    require d gt 0 : "Data determines a degree <= 0";
    X`hilbert := h;
    X`degree := d;
    X`Ac := a;
    // Compute a first guess of the weights - this is slow
    // in the standard magma packages, so we use a better alg.
    S := PowerSeriesRing(Integers(),100);
    W := FanoFindFirstGenerators(S!h);
    // reduced_basket := SequenceToSet(Points(B));
    // has_projection := #reduced_basket ne 0 and
        // Minimum([ proj_loss(P) : P in reduced_basket ]) lt d;
    // if not has_projection then
        bool,W1 := CheckBasket(B,W);	// this is still slow
        if not bool then
            W := W1;
        end if;
    // end if;
    X`weights := Sort(W);
    return X;
end intrinsic;

intrinsic Fano3fold(f::RngIntElt,B::GRBskt) -> GRFano
{A Fano 3-fold of Fano index f >= 3 and with basket of singularities B}
    require f ge 3: "Genus argument needed when Fano index f >= 3";
    require IsTerminalThreefold(B):
        "Basket must contain only terminal 3-fold singularities";
    require &and[ (f mod Index(p)) eq TerminalPolarisation(p)[1] :
        p in Points(B) ]: "Singularities are not properly polarised "
            * "for the given Fano index f =",f;
    // make the object X and attach all the Fano data.
    X := HackobjCreateRaw(GRFano);
    X`fanoindex := f;
    X`basket := B;
    X`dim := 3;
    h,d,a := fano_hilbert_series(f,B);
    require d gt 0 : "Data determines a degree <= 0";
    X`hilbert := h;
    X`degree := d;
    X`Ac := a;
    // Compute a first guess of the weights - this is slow
    // in the standard magma packages, so we use a better alg.
    S := PowerSeriesRing(Integers(),100);
    W := FanoFindFirstGenerators(S!h);
    bool,W1 := CheckBasket(B,W);	// this is still slow
    if not bool then
    	W := W1;
    end if;
    X`weights := W;
    return X;
end intrinsic;

intrinsic AdjustWeights(~X::GRFano,W::SeqEnum)
{Set the ambient weights for the Fano X to be the integer sequence W
(and update other relevant data).}
    h := HilbertSeries(X);
    R := Parent(Numerator(h));
    t := R.1;
    newnum := h * &* [ 1 - t^w : w in W ];
    require Degree(Denominator(newnum)) eq 0:
    	"Not enough weights in W to cancel the Hilbert denominator";
    X`weights := W;
    // simply unassign anything that depends on this - it will
    // get recomputed correctly when required.
    delete X`num;
    delete X`numinfo;
    delete X`betti;
end intrinsic;


/////////////////////////////////////////////////////////////////////
//		Genus bounds when f = 1 or 2
/////////////////////////////////////////////////////////////////////

// The Bogomolov--Kawamata stability bound
// 'stable' is a boolean: true imposes the stronger bounds.
function bogomolov(f,g,B,stable)
    if stable then
	return f^2*fano_degree_g(g,f,B) - 3*12*fano_Ac(f,B);
    else
	return (4*f^2-3*f)*fano_degree_g(g,f,B) - 4*f*12*fano_Ac(f,B);
    end if;
end function;

function max_genus(f,B : Stable:=true)
    if not f in {1,2} then
        return 0;   // this value is irrelevant
    end if;
    g := 0;	// starting value - could be anything.
    if bogomolov(f,g,B,Stable) gt 0 then
      repeat
          g -:= 1;
      until bogomolov(f,g,B,Stable) le 0;
    else
      repeat
          glast := g;
          g +:= 1;
      until bogomolov(f,g,B,Stable) gt 0;
      g := glast;
    end if;
    return g;
end function;

// The minimum value of the Fano genus g for which the triple (f,B,g)
// determine a positive Fano degree.
function base_genus(f,B)
    if not f in {1,2} then
        return 0;   // this value is irrelevant
    end if;
    // I could be smarter about this since the degree is linear in g.
    g := 0;
    if fano_degree_g(g,f,B) le 0 then
      repeat
          g +:= 1;
      until fano_degree_g(g,f,B) gt 0;
    else
      repeat
          glast := g;
          g -:= 1;
      until fano_degree_g(g,f,B) le 0;
      g := glast;
    end if;
    return g;
end function;


//////////////////////////////////////////////////////////////////////
//	Local version of FindFirstGenerators
//////////////////////////////////////////////////////////////////////

intrinsic FanoFindFirstGenerators(g::RngSerPowElt) -> SeqEnum,BoolElt
{Return plausible weights of generators for the variety with Hilbert series g.
The second return value is false iff the search for first generators was
not completed within the precision of g.}
// no test that g = 1 + h.o.t.
// require that g has integer coeffs
    N := Precision(Parent(g));
    s := Parent(g).1;
    gens := [ Integers() | ];
    coeffs := Coefficients(g);
    coeffs cat:= ZeroSequence(Universe(coeffs),N-#coeffs); // pad up with zeros
    for i in [2..#coeffs] do	// considering the coeff of s^(i-1)
        if coeffs[i] lt 0 then
	    return gens,true;
	elif coeffs[i] gt 0 then
	    c := Integers() ! coeffs[i];
	    gens cat:= [ i-1 : j in [1..c] ];
	    g *:= (1 - s^(i-1))^c;
	    coeffs := Coefficients(g);
            coeffs cat:= ZeroSequence(Universe(coeffs),N-#coeffs);
	end if;
    end for;
    return gens,false;
end intrinsic;

