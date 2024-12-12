/*
    This file computes the possibly isolated points on the modular curves X_0(n) with exceptional j-invariant,
    where n is a divisor of the level of the intersection of the adelic Galois image with SL(2, Zhat).
    Any point which does not appear in the output cannot be isolated.
*/

// Compute the genus of the modular curve X_H, for H a subgroup of some GL(2, Integers(n))
// Adapted from gl2.m (see code in Jeremy Rouse, Andrew V. Sutherland, David Zureick-Brown, "ell-adic images of Galois for elliptic curves over Q", 2021)
function GL2Genus(H)
    N := #BaseRing(H);
    SL2 := SL(2, Integers(N));
    H := SL2 meet H;
    if not -Identity(H) in H then H := sub<SL2 | H, -Identity(H)>; end if;
    pi := CosetAction(SL2, H);
    n2 := #Fix(pi(SL2![0,1,-1,0]));
    n3 := #Fix(pi(SL2![0,1,-1,-1]));
    c := #Orbits(pi(sub<SL2|[1,1,0,1]>));
    i := Index(SL2, H);
    g := Integers()!(1 + i/12 - n2/4  - n3/3 - c/2);
    return g;
end function;

// Import Galois image data from exceptional_images.dat (computed in David Zywina, "Explicit open images for elliptic curves over Q", 2024)
// Each entry of galois_images encodes the adelic Galois image of an elliptic curve E with exceptional j-invariant
// The format is as follows:
//  [ j-invariant,
//    model of E,
//    level n of adelic Galois image,
//    adelic Galois image (as subgroup of GL(2, Integers(n))),
//    index of adelic Galois image in GL(2, Zhat),
//    level m of intersection of adelic Galois image with SL(2, Zhat),
//    intersection of adelic Galois image with SL(2, Zhat) (as subgroup of SL(2, Integers(m))),
//    extra data... ]
galois_images := [];
file := Open("exceptional_images.dat", "r");
repeat
	bool, obj := ReadObjectCheck(file);
	if bool then
        Append(~galois_images, obj);
	end if;
until not bool;
"Number of exceptional j-invariants:", #galois_images;
"";

"Possibly isolated points:";
"    j-invariant       X_0(n)  Genus  Degree";
// Cache the subgroups B_0(n) and the genus of X_0(n), as it is quite costly to compute
B0 := AssociativeArray();
X0_genera := AssociativeArray();
for rec in galois_images do
    for n in Divisors(rec[6]) do
        // Ignore X_0(1), as we know it has genus 0, and MAGMA does not allow Integers(1)
        if n eq 1 then
            continue;
        end if;
        
        // Compute the subgroup B_0(n) and the genus of X_0(n), if it has not been already
        if not IsDefined(B0, n) then
            B0[n] := sub<GL(2, Integers(n)) | [[a,0,0,1] : a in Integers(n) | IsUnit(a)] cat [[1,b,0,1] : b in Integers(n)] cat [[1,0,0,c] : c in Integers(n) | IsUnit(c)]>;
            X0_genera[n] := GL2Genus(B0[n]);
        end if;
        
        // Genus 0 curves cannot contain isolated points
        if X0_genera[n] eq 0 then
            continue;
        end if;

        // Compute the degrees of the closed points on X_0(n) with the given j-invariant
        G := sub<GL(2, Integers(n)) | rec[4] cat [[-1,0,0,-1]]>;
        for H in Conjugates(GL(2, Integers(n)), G) do
            degree := Index(H, H meet B0[n]);
            // The closed point can only be isolated if the degree of the closed point is at most the genus of X_0(n)
            if degree le X0_genera[n] then
                printf "%19o     %o      %o      %o\n", rec[1], n, X0_genera[n], degree;
            end if;
        end for;
    end for;
end for;

quit;
