/*
    This file computes the isolation graph of closed points on modular curves of level 7 with j-invariant 2268945/128,
    as well as the points whose degree does not exceed the genus of the underlying curve (and hence are possibly isolated).
    This is much slower than computing the quotient graph, and solely serves to verify the computations in level_7_quotient_graph.m.
*/

// Compute the genus of the modular curve associated to a subgroup of SL(2, n)
// Adapted from gl2.m (see code in Jeremy Rouse, Andrew V. Sutherland, David Zureick-Brown, "ell-adic images of Galois for elliptic curves over Q", 2021)
function SL2Genus(SL2, H)
    pi := CosetAction(SL2, H);
    n2 := #Fix(pi(SL2![0,1,-1,0]));
    n3 := #Fix(pi(SL2![0,1,-1,-1]));
    c := #Orbits(pi(sub<SL2|[1,1,0,1]>));
    i := Index(SL2, H);
    g := Integers()!(1 + i/12 - n2/4  - n3/3 - c/2);
    return g;
end function;

// Create record format for curves, closed points and edges
curve_rec_format := recformat<id : Integers(), subgroup : GrpMat, index : Integers(), sl2_intersection : Integers(), components : Integers(), genus : Integers()>;
point_rec_format := recformat<id : Integers(), curve : Rec, generator : GrpMatElt, degree : Integers(), potentially_isolated : BoolElt>;
edge_rec_format := recformat<type : MonStgElt, degree : Integers()>;

// Create ambient group GL(2, 7) and Galois representation G
GL2 := GL(2, IntegerRing(7));
SL2 := SL(2, IntegerRing(7));
G := sub<GL2 | [[2,0,0,4], [0,2,1,0], [6,0,0,6]]>;

// Convert to GrpPerm, to allow use of DoubleCosetRepresentatives
// Can restrict to subgroups containing -I, so quotient by -I as well
minus_one := GL2![-1,0,0,-1];
GL2, quo_map := quo<GL2 | minus_one>;
SL2 := quo_map(SL2);
G := quo_map(G);

// Compute all subgroups of GL(2, 7)
subgroups := AllSubgroups(GL2);

// Compute the properties of the modular curve associated to each subgroup
curves := [];
for i -> H in subgroups do
    index := Index(GL2, H);
    sl2_intersection := Index(subgroups, H meet SL2);
    components := 6/Index(H, subgroups[sl2_intersection]);
    genus := SL2Genus(SL2@@quo_map, subgroups[sl2_intersection]@@quo_map);
    Append(~curves, rec<curve_rec_format | id := i, subgroup := H@@quo_map, index := index, sl2_intersection := sl2_intersection, components := components, genus := genus>);
end for;

// Find representatives for all closed points on modular curves of level 7
// double_coset_bases and double_coset_canonical_images contain data for identifying the representative of the double coset HgG, for any g in GL(2, Integer(7))
double_coset_reps := [DoubleCosetRepresentatives(GL2, H, G) : H in subgroups];
double_coset_bases := [];
double_coset_canonical_images := [];
for i -> H in subgroups do
    canonical_images := [];
    for j -> g in double_coset_reps[i] do
        if j eq 1 then
            image, base := DoubleCosetCanonical(GL2, H, g, G);
            Append(~double_coset_bases, base);
        else
            image := DoubleCosetCanonical(GL2, H, g, G : B := double_coset_bases[i]);
        end if;
        Append(~canonical_images, image);
    end for;
    Append(~double_coset_canonical_images, canonical_images);
end for;

// Compute properties of the closed points represented by the double cosets HgG calculated above
closed_points := [];
for i -> H in subgroups do
    points := [];
    for j -> g in double_coset_reps[i] do
        degree := Index(G^(g^-1), G^(g^-1) meet H);
        potentially_isolated := degree le curves[i]`genus*curves[i]`components;
        Append(~points, rec<point_rec_format | id := j, curve := curves[i], generator := g@@quo_map, degree := degree, potentially_isolated := potentially_isolated>);
    end for;
    Append(~closed_points, points);
end for;

// Construct vertices of isolationi graph
isolation_graph := Digraph<{@ [i, j] : j -> _ in row, i -> row in closed_points @} | : SparseRep := true>;
AssignVertexLabels(~isolation_graph, [label : label in row, row in closed_points]);

// Compute inclusion maps between closed points
for i -> H in subgroups do
    for K in MinimalOvergroups(GL2, H) do
        j := Index(subgroups, K);
        degree := curves[i]`index/curves[j]`index;
        for k -> g in double_coset_reps[i] do
            l := Index(double_coset_canonical_images[j], DoubleCosetCanonical(GL2, K, g, G: B := double_coset_bases[j]));
            // Add edge to isolation graph if the degree conditions are satisfied
            if closed_points[i, k]`degree/closed_points[j, l]`degree eq 1 then
                AddEdge(~isolation_graph, VertexSet(isolation_graph)![j, l], VertexSet(isolation_graph)![i, k], rec<edge_rec_format | type := "pushforward", degree := degree>);
            elif closed_points[i, k]`degree/closed_points[j, l]`degree eq degree then
                AddEdge(~isolation_graph, VertexSet(isolation_graph)![i, k], VertexSet(isolation_graph)![j, l], rec<edge_rec_format | type := "pullback", degree := degree>);
            end if;
        end for; 
    end for;
end for;

"Isolation graph properties:"; IndentPush();
"Curves:", #curves;
"Vertices:", #Vertices(isolation_graph);
"Edges:", #Edges(isolation_graph);
"Terminal vertices:", #[v : v in Vertices(isolation_graph) | OutDegree(v) eq 0];
"Potentially isolated vertices:", #[point : point in VertexLabels(isolation_graph) | point`potentially_isolated];
""; IndentPop();

isolated_subgraph := sub<isolation_graph | {v : v in Vertices(isolation_graph) | Label(v)`potentially_isolated}>;
"Potentially isolated subgraph proprties:"; IndentPush();
"Vertices:", #Vertices(isolated_subgraph);
"Edges:", #Edges(isolated_subgraph);
"Initial vertices:", #[v : v in Vertices(isolated_subgraph) | InDegree(v) eq 0];
IndentPop();

quit;
