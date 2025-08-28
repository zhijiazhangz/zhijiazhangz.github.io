////////////////////////////////////////////////////////////////////////////////
// Making the baskets of Fano 3-folds of Fano index f with 'bound' n
//
// Idea: first make a big collection of baskets satisfying the weaker
// conditions: N <= 15 and sum(r-1) < 24, where N = #singular points.
// NB n == 24 here.
// Then test the real conditions
//	N <= 15 and (3/2)N <= sum(r - (1/r)) < 24
// on each of these.
// When f = 1 or 2 the parameter g also plays a role: it appears in formulas
// for A^3 and for the Hilbert coefficients.
//
// We refer to sum (r - 1/r) as the 'Kawamata sum'.
//
////////////////////////////////////////////////////////////////////////////////

import "suzuki.m":
	fano_Ac,
	fano_degree,
	fano_degree_g,
	contribution;

import "fano3folds.m":
	base_genus,
	max_genus,
	bogomolov;

////////////////////////////////////////////////////////////////////////////////
//		Knapsack help for baskets
// Q is a seq of > 0 rational numbers. n is a > 0 rational number.
// Returns the set of all indices of elements in Q s.t sum_i Q[i] < n.
procedure knapsack_recurse(~results, working, Q, n, idx )
    if idx gt #Q then
        Include(~results, working);
        return;
    end if;
    $$(~results, working, Q, n, idx+1);
    max := Ceiling(n/Q[idx]) - 1;
    for i in [1..max] do
        n -:= Q[idx];
        Append(~working, idx);
        $$(~results, working, Q, n, idx+1);
    end for;
end procedure;

function knapsack(Q,n)
    results := {PowerSequence(Integers())|};
    //maximums := [ Ceiling(n/q) - 1 : q in Q ];	// never used!
    knapsack_recurse(~results, [Integers()|], Q, n, 1);
    return results;
end function;

// Return all baskets of isolated quotient sings P = 1/r(f,a,r-a)
// that satisfy Sum r - 1/r < n.
function isolated_baskets(n,f)
    assert n ge 2;

    // Step 1: the knapsack for possible baskets
    sings := [];
    for r in [2..n] do
        for a in [1..Floor(r/2)] do
            if GCD(a*f,r) eq 1 then
                Append(~sings,[r,a]);
            end if;
        end for;
    end for;
    Q := [ P[1] - 1/P[1] : P in sings ];
    poss:=knapsack(Q,n);

    // Step 2: build and return
    points := [ Point(P[1],[P[2],P[1]-P[2],f]) : P in sings ];
    return [ Basket([points[i]:i in I]) : I in poss ];
end function;


/////////////////////////////////////////////////////////////////////
// This is the main intrinsic.
// Conditions are imposed separately by procedures written below.
/////////////////////////////////////////////////////////////////////

function coefficient(f,B,n)
    return 1 + (1/12) * fano_degree(f,B) * n*(n+f)*(2*n+f)
        + n * fano_Ac(f,B)
        + &+[Rationals()| contribution(f,p,n mod Index(p)) :
                                p in Points(B) ];
end function;


function coefficient_g(g,f,B,n) // the g in fano_degree is the only difference
    return 1 + (1/12) * fano_degree_g(g,f,B) * n*(n+f)*(2*n+f)
        + n * fano_Ac(f,B)
        + &+[Rationals()| contribution(f,p,(n mod Index(p))) :
                                p in Points(B) ];
end function;

intrinsic FanoBaskets(n::RngIntElt,f::RngIntElt :
		Order:="default",Stable:=true) -> SeqEnum, SeqEnum
{All baskets of singularities appearing on Fano 3-folds with Fano index f
and Kawamata index sum at most n. If f = 1 or 2, then a parallel sequence
of possible genus values g is also returned.}

	// Cook up all baskets with the Kawamata sum bounded by n.
	B := isolated_baskets(n,f);

	if f eq 1 or f eq 2 then
		// For each b in B find the values of g = g_min..g_kawamata
		// for which A^3 > 0 and Kawamata condition is satisfied.
		g_mins := [ base_genus(f,b) : b in B ];
		g_maxs := [ max_genus( f, B[i] : Stable:=Stable) :i in [1..#B]];
		// For each b,g pair, check the negative coefficients.
		newB := [];
		G := [ Parent([1,2,3]) | ];
		for i in [1..#B] do
			b := B[i];
			gg := [ Integers() | ];
			g_min := g_mins[i];
			g_max := g_maxs[i];
			// Impose vanishing of coeffs of t^-1, t^-2,...
			for g in [g_min..g_max] do
				if &and [ coefficient_g(g,f,b,n) eq 0 :
						n in [-Round(f-1)..-1] ] then
					Append(~gg, g);
				end if;
			end for;
			if #gg gt 0 then
				Append(~newB,b);
				Append(~G,gg);
			end if;
		end for;
		B := newB;
		require #B eq #G: "Something is badly wrong";
		return B,G;
	else
		// Impose A^3 > 0 on the baskets:
printf "Number of isolated baskets (f = %o): %o\n",f,#B;
		B := [ b : b in B | fano_degree(f,b) gt 0 ];
print "... after imposing A^3 > 0:",#B;
		// Impose vanishing of coeffs of t^-1, t^-2,...:
		B := [ b : b in B |
			&and[coefficient(f,b,n) eq 0 : n in [-Round(f-1)..-1]]];
print "... and several h^0(-iA) = 0:",#B;
		// Impose stability if requested:
		B := [ b : b in B | bogomolov(f,0,b,Stable) le 0 ];
print "... and Kawamata-Bogomolov bound:",#B;
		return B,_;
	end if;
end intrinsic;

