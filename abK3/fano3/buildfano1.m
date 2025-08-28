//////////////////////////////////////////////////////////////////////////////
//
//		Computing Fano 3-folds with index f
//
//  Gavin Brown, Kaori Suzuki, February 2006, August 2010.
//  Alexander Kasprzyk, April 2012.
//  Gavin Brown, Alexander Kasprzyk, April 2014.
//
// Computes all (or all Bogomolov--Kawamata stable) Fano 3-folds.
//
//////////////////////////////////////////////////////////////////////////////

AttachSpec("fano3.spec");

StableOnly := false;

//////////////////////////////////////////////////////////////////////
// Step 1: Calculate all possible basket-genus pairs for Fano index 1
//////////////////////////////////////////////////////////////////////

print "Step 1: finding basket-genus pairs, index 1 (~5s)";
t1 := Cputime();
Bus,Gus := FanoBaskets(24,1 : Stable:=StableOnly);	// about 37s
// assert #Bus eq 7683;
// assert #&cat Gus eq 52654;
printf "No. of baskets: %o\tNo. of pairs: %o\n",#Bus,#&cat Gus;
print "Time:",Cputime(t1);


//////////////////////////////////////////////////////////////////////
// Step 2: Compute first models for the corresponding Fano 3-folds.
//
// This won't get all codims right, but it does get those in codim <= 3.
// Higher codims are sorted out later using a projection calculus.
//
// Remove the 8 obviously false candidates as we see them.
// 
//////////////////////////////////////////////////////////////////////

function build_fanos(Bs,Gs)
    S := PowerSeriesRing(Rationals(),30);
    fanos := [];
    for i in [1..#Bs] do 
	for g in Gs[i] do
		X := Fano3fold(1,Bs[i],g);
                // Eliminate a known cases of error: 1 + s + s^2 + ... + 0*s^?
                // Removes 8 cases.
                hilbcoeffs := Coefficients(S!HilbertSeries(X));
                indzero := Index(hilbcoeffs,0);
                if indzero notin {0,1,2} then   // i.e. some zero 0*t^(>=2)
                    if &and [ hilbcoeffs[j] eq 1 : j in [2..indzero-1] ] then
                        continue g;
                    end if;
                end if;
		Append(~fanos, X);
	end for;
    end for;
    return fanos;
end function;

print "Step 2: finding first models of Hilbert series, index 1 (~40s)";
t1 := Cputime();
fanosus := build_fanos(Bus,Gus);	// 125s
print "Time:",Cputime(t1);

/*
Intermediate check:
	{* Codimension(X) : X in fanosus *};
	{* 1^^95, 2^^85, 3^^70, 4^^292, 5^^391, 6^^860, 7^^1612, 8^^3113, 9^^5285, 10^^6860, 11^^7139, 12^^6657, 13^^5540, 14^^4165, 15^^2777, 16^^1938, 17^^1455, 18^^1031, 19^^638, 20^^487, 21^^394, 22^^333, 23^^266, 24^^223, 25^^178, 26^^154, 27^^116, 28^^91, 29^^79, 30^^65, 31^^56, 32^^44, 33^^35, 34^^29, 35^^21, 36^^17, 37^^12, 38^^11, 39^^9, 40^^6, 41^^5, 42^^4, 43^^3, 44^^2, 45, 46, 47 *}
*/


//////////////////////////////////////////////////////////////////////
// Step 3: Sort the list according to Hilbert series.
//
// This means that where one Fano projects to another, the target
// of projection comes earlier in the list (so, inductively, can
// be considered to be correct).
//
//////////////////////////////////////////////////////////////////////

print "Step 3: sorting according to Hilbert series coefficients (no time)";
S := PowerSeriesRing(Integers(),30);
sortedus := [ <S!HilbertSeries(fanosus[i]), i> : i in [1..#fanosus] ];
Sort(~sortedus);
Fsorted := [ fanosus[sortedus[i][2]] : i in [1..#sortedus] ];


//////////////////////////////////////////////////////////////////////
// Step 4: Impose the projection calculus to improve the weights.
//
// Timing: 340s/650s for stable/unstable cases. 
//////////////////////////////////////////////////////////////////////

print "Step 4: imposing the projection calculus to improve weights (~150s)";
t1 := Cputime();
load "projections.m";
print "Time:",Cputime(t1);


// Both sequences begin
// [ 0, 95, 85, 70, 145, 164, 253, 303, 487, 568, 909, 1116, 1642, ...
// Results are in Fupdated.

fano1s := Fupdated;

fano1s_stab := [X:X in fano1s|BogomolovNumber(X) le 0];
fano1s_unstab := [X:X in fano1s|BogomolovNumber(X) gt 0];

print "Calculation complete.";
print "Result is two sequences: 'Fano3DB' and 'Fano3DBunstable', respectively";
print "  -- stable Fano 3-folds of index 1";
printf "       %o index 1 (stable)\n",#fano1s_stab;
print "  -- unstable Fano 3-folds of index 1";
printf "       %o index 1 (unstable)\n",#fano1s_unstab;

printf "Codimensions: %o\n",{* Codimension(X):X in fano1s_stab *};

Fano3DB := fano1s_stab;
Fano3DBunstable := fano1s_unstab;

