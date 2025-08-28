// Code to impose the projection calculus on the sequence of
// index 1 Fano 3-folds.

// W = [w1,w2,...,wn] a seq of weights.
// p = 1/r(1,a,r-a) as a sing type.
// B a basket (which includes the sing above).
// Return true iff can interpret this cleanly as a bir'l proj (of deg > 0).
// Then also return basket of projection and its type,subtype.
//
// We assume that the weights W are appropriate for 1/r(1,a,r-a) - i.e. the
// repeat..until loops do terminate.
//
// We assume that the singularities are isolated, i.e. hcf(r,a) = 1.
//
/* Test code

W := [1,2,3,4,5,6,7];
p := Point(3,[1,1,2]);
q := Point(4,[1,1,3]);
r := Point(5,[1,2,3]);
s := Point(2,[1,1,1]);
B := Basket([p,p,q,r,s]);
which_projection(W,p,B);	// 2_3
which_projection(W,q,B);	// 2_1
which_projection(W,r,B);	// 1
which_projection(W,s,B);	// 4
*/

// A,B seqs of ints.
// Go through x in A in turn, either finding x in B and deleting it, or not.
// Return those x in A that were not found in B (and also the remains of B).
function part_subseq(A,B)
    Arem := [ Universe(A) | ];
    for x in A do
        indx := Index(B,x);
	if indx eq 0 then
	    Append(~Arem,x);
	else
	    Remove(~B,indx);
	end if;
    end for;
    return Arem,B;
end function;

function which_projection(W,p,B)
    Worig := W;     // copy for comparison later
    r := Index(p);
    A := Reversion(Sort(Polarisation(p)));	// do biggest wt first (generic)
    
    // figure out the target basket; revert to simple baskets for speed (f=1)
    ptsB := [ [Index(p), Sort(Polarisation(p))[2]] : p in Points(B) ];
    indp := Index(ptsB,[Index(p), Sort(Polarisation(p))[2]]);
	    if indp eq 0 then
		print W,p,B;
		error "STOP AT BASKET";
		end if;
    Remove(~ptsB,indp);
    for a in A do
        if a ne 1 then
	    Append(~ptsB, [a, Minimum([r mod a, -r mod a])]);
	end if;
    end for;
    Sort(~ptsB);

    // work out the type; first remove the index r from the weights.
    if Index(W,r) ne 0 then
        Remove(~W,Index(W,r));
    end if;

    // second, find the polarising weights that really appear
    Arem,Wrem := part_subseq(A,W);
    if #Arem eq 0 then	// A subset W so type 1
	    return true, ptsB, 1, 0, 0;
    elif #Arem ge 2 then	// type 4
	    return true, ptsB, 4, 0, 0;
    else	// #Arem eq 1 so type 2 - now figure out the subtype
        a := Arem[1];
        if #[ w : w in Worig | w lt a ] ge 6 then
            // we assume it's Type I after all - we'd get an error later if not
            return true, ptsB, 1, 0, 0;
        end if;
        subtype := 0;
        repeat
            subtype +:= 1;
            inda := Index(Wrem, (subtype+1)*a);
	    if subtype ge 20 then	// doesn't happen?
                if #Worig eq 5 then
                    return true, ptsB, 2, 1, a;
                end if;
		return true, ptsB, -1, 0, 0;
            end if;
	    until inda ne 0;
        return true, ptsB, 2, subtype, a;
    end if;
end function;

//////////////////////////////////////////////////////////////////////
// Given seq Fsorted whose order defines fanoid.

function basket_string(X)
    return Sort([ [Index(p),
        Sort(Remove(Polarisation(p),
	    Index(Polarisation(p),FanoIndex(X) mod Index(p))))[1] ]
		: p in Points(Basket(X)) ]);
end function;

lookup:=[<FanoIndex(X), FanoGenus(X), basket_string(X) > : X in Fsorted ];
proj_data := [];

Fupdated := [];

function is_special(X)
    // The next Fano projects to Y in P[1,4,5,6,15] and projection keeps 15
    if Weights(X) eq [ 1, 4, 5, 6, 6, 7, 8, 9 ] then
	B := Basket([ Point(2,[1,1,1]), Point(2,[1,1,1]), Point(3,[1,1,2]),
		Point(4,[1,1,3]), Point(5,[1,1,4]), Point(6,[1,1,5]) ]);
	if Basket(X) eq B then
            return true;
	end if;
    end if;

    // The next Fano projects to Y in P[1,5,...20] and projection keeps 20
    if Weights(X) eq [ 1, 5, 7, 8, 8, 9, 10, 11, 12 ] then
	B := Basket([ Point(4,[1,1,3]), Point(5,[1,2,3]), Point(5,[1,2,3]),
		Point(8,[1,1,7]) ]);
	if Basket(X) eq B then
            return true;
	end if;
    end if;

    // The next Fano projects to Y in P[1,4,...15] and projection keeps 15
    if Weights(X) eq [ 1, 4, 5, 5, 6, 6, 7, 8, 9 ] then
	B := Basket([ Point(2,[1,1,1]), Point(2,[1,1,1]), Point(3,[1,1,2]),
		Point(5,[1,1,4]), Point(5,[1,1,4]), Point(5,[1,1,4]) ]);
	if Basket(X) eq B then
            return true;
	end if;
    end if;

    // The next Fano projects to Y in P[1,7,...25] and projection keeps 25
    if Weights(X) eq [ 1, 7, 8, 9, 10, 10, 11, 12, 13, 14, 15 ] then
	B := Basket([ Point(2,[1,1,1]), Point(5,[1,2,3]), Point(7,[1,3,4]),
		Point(9,[1,1,8]) ]);
	if Basket(X) eq B then
            return true;
	end if;
    end if;

    return false;
end function;

for i in [1..#Fsorted] do
    X := Fsorted[i];
    special := is_special(X); // true => don't change weights at end of calc.

    // Sort through the basket and compute the 'degree' of
    // the variety after projection from each point - only
    // positive degrees give genuine birational projections.

    // Store projections as
    //	< fanoid, singpoint [r,a], proj-degree, targetid or 0,
    //		primary type 1,2,4 or 0, secondary type or 0 >.

    B := Basket(X);
    Btext := [ [Index(p),Polarisation(p)[2]] : p in Points(B) ];
    Bred := Setseq(Seqset(Points(B)));
    deg := Degree(X);
    these_projs := [];
    for p in Bred do
        r := Index(p);
        A := Polarisation(p);	// of the form [1,a,r-a] after sorting
    	a := Sort(A)[2];
    	projdeg := deg - 1/(r*a*(r-a));
    	if projdeg gt 0 then
    	    bool,targB,type,subtype,b := which_projection(Weights(X),p,B);
    	    targetid := Index(lookup, <1, FanoGenus(X), targB>);
    	    if targetid eq 0 then
    	        print X;
    	        targB, type, subtype;
    	        error "STOP no target despite pos proj deg";
	    end if;
	    newproj := < i,[r,a],projdeg,targetid,type,subtype,b >;
        else
	    newproj := < i, [r,a], projdeg, 0, 0, 0, 0 >;
	end if;
	Append(~these_projs, newproj);
    end for;

    // OK, now we've seen all the projections we can try to get a consistent
    // better idea of the appropriate weights for X
    W := Weights(X);    // are we happy with these weights?
    if #W in {5,6,7} then
        afr := GetAFR(Remove(W,1),Btext);  // it works on the K3 section
        if afr ne 0 then  // OK, I like the weights, but still need work on projections?
            proj_data cat:= these_projs;
            Append(~Fupdated,X);
            continue i;
        end if;
    end if;
    
    working_projs := [ P : P in these_projs | P[3] gt 0 ];     // only use birl projs
    working_projs := [ P : P in working_projs | P[5] in {1,2} ]; // only use Types 1 and 2
    // if there are Type 1 or Type 2 subtype <= 1 projs, then ignore higher Type 2 projs.
    easier := [ P : P in working_projs |  P[5] eq 1 or (P[5] eq 2 and P[6] le 1) ];
    if #easier ne 0 then
        working_projs := easier;
    else    // OK, I'll try with only II_3 and II_4 projs if poss.
        easier := [ P : P in working_projs |  P[5] eq 2 and P[6] le 3 ];
        if #easier ne 0 then
            working_projs := easier;
        end if;
    end if;
    
    if #working_projs eq 0 then // no projections to help us - hope for the best?
        proj_data cat:= these_projs;
        Append(~Fupdated,X);
        continue i;
    end if;

    possible_wts := [ Parent([[7,2],[1,2,3]]) | ];
    for P in working_projs do
        Wproj := Weights(Fupdated[P[4]]);   // the (correct) weights of target
        type := P[5];
        r := P[2][1];
        if type eq 1 then
            Append(~possible_wts, [P[2],Sort(Wproj cat [r])]);
        elif type eq 2 then
            subtype := P[6];
            a := P[7];
            Append(~possible_wts, [P[2],Sort(Wproj cat [ r + k*a : k in [0..subtype]])]);
        elif type eq -1 then
        end if;
    end for;
    if #{ W[2] : W in possible_wts} eq 1 then
        // rebuild X and put the new one into Fupdated
        Wnew := Representative(possible_wts)[2];
        if #part_subseq(W,Wnew) ne 0 then   // W not a subseq of predicted wts Wnew
            print "i =",i,X, Wnew,these_projs;
            error "STOP wts not increased by study";
        end if;
	if not special then
            AdjustWeights(~X,Wnew);
	end if;
        Append(~Fupdated,X);
    else
            print "i =",i,X, these_projs, possible_wts;
            error "STOP bad weights";        
    end if;
    
    proj_data cat:= these_projs;
end for;

