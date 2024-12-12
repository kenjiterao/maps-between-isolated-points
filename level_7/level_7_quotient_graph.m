/*
    This file computes the quotient of the isolation graph for closed points on modular curves of level 7 with j-invariant 2268945/128,
    as well as the points whose degree does not exceed the genus of the underlying curve (and hence are potentially isolated).
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
curve_rec_format := recformat<id : Integers(), subgroup : GrpMat, index : Integers(), sl2_intersection : Integers(), components : Integers(), genus : Integers(), count : Integers()>;
point_rec_format := recformat<id : Integers(), curve : Rec, generator : GrpMatElt, degree : Integers(), count : Integers(), potentially_isolated : BoolElt>;
edge_rec_format := recformat<type : MonStgElt, degree : Integers(), count : Integers()>;

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

// Compute lattice of conjugacy classes subgroups of GL(2, 7), as well as normalizers of the representative of each conjugacy class
subgroup_lattice := SubgroupLattice(GL2);
normalizers := [Normalizer(GL2, Group(lat_elt)) : lat_elt in subgroup_lattice];

// Compute the properties of the modular curve associated to each conjugacy class of subgroups
curves := [];
for lat_elt in subgroup_lattice do
    index := Order(Top(subgroup_lattice))/Order(lat_elt);
    sl2_intersection := subgroup_lattice!(Group(lat_elt) meet SL2);
    components := 6/(Order(lat_elt)/Order(sl2_intersection));
    genus := SL2Genus(SL2@@quo_map, Group(sl2_intersection)@@quo_map);
    Append(~curves, rec<curve_rec_format | id := IntegerRing()!lat_elt, subgroup := Group(lat_elt)@@quo_map, index := index, sl2_intersection := IntegerRing()!sl2_intersection, components := components, genus := genus, count := Length(lat_elt)>);
end for;

// Find representatives for all conjugacy classes of closed points on modular curves of level 7
// double_coset_bases and double_coset_canonical_images contain data for identifying the representative of the double coset HgG, for any g in GL(2, Integer(7))
double_coset_reps := [DoubleCosetRepresentatives(GL2, H, G) : H in normalizers];
double_coset_bases := [];
double_coset_canonical_images := [];
for i in [1..#subgroup_lattice] do
    canonical_images := [];
    for j -> g in double_coset_reps[i] do
        if j eq 1 then
            image, base := DoubleCosetCanonical(GL2, normalizers[i], g, G);
            Append(~double_coset_bases, base);
        else
            image := DoubleCosetCanonical(GL2, normalizers[i], g, G : B := double_coset_bases[i]);
        end if;
        Append(~canonical_images, image);
    end for;
    Append(~double_coset_canonical_images, canonical_images);
end for;

// Compute properties of the closed points represented by the double cosets HgG calculated above
closed_points := [];
for lat_elt in subgroup_lattice do
    i := IntegerRing()!lat_elt;
    H := Group(lat_elt);
    points := [];
    for j -> g in double_coset_reps[i] do
        degree := Index(G^(g^-1), G^(g^-1) meet H);
        count := Index(normalizers[i], H)/Index(normalizers[i] meet G^(g^-1), H meet G^(g^-1))*curves[i]`count;
        potentially_isolated := degree le curves[i]`genus*curves[i]`components;
        Append(~points, rec<point_rec_format | id := j, curve := curves[i], generator := g@@quo_map, degree := degree, count := count, potentially_isolated := potentially_isolated>);
    end for;
    Append(~closed_points, points);
end for;

// Construct vertices of quotient graph
quotient_graph := Digraph<{@ [i, j] : j -> _ in row, i -> row in closed_points @} | : SparseRep := true>;
AssignVertexLabels(~quotient_graph, [label : label in row, row in closed_points]);

// Compute inclusion maps between closed points
for H_lat_elt in subgroup_lattice do
    i := IntegerRing()!H_lat_elt;
    H := Group(H_lat_elt);
    for K_lat_elt in MinimalOvergroups(H_lat_elt) do
        j := IntegerRing()!K_lat_elt;
        K := Group(K_lat_elt);
        degree := Order(K_lat_elt)/Order(H_lat_elt);
        for k -> g in double_coset_reps[i] do
            // Count number of duplicate edges
            edges := AssociativeArray();
            for m in Transversal(GL2, normalizers[j]) do
                if H subset K^m then
                    l := Index(double_coset_canonical_images[j], DoubleCosetCanonical(GL2, normalizers[j], m*g, G: B := double_coset_bases[j]));
                    if IsDefined(edges, l) then
                        edges[l] +:= 1;
                    else
                        edges[l] := 1;
                    end if;
                end if;
            end for;
            // Add edges to isolation graph if the degree conditions are satisfied
            for l -> count in edges do
                if closed_points[i, k]`degree/closed_points[j, l]`degree eq 1 then
                    AddEdge(~quotient_graph, VertexSet(quotient_graph)![j, l], VertexSet(quotient_graph)![i, k], rec<edge_rec_format | type := "pushforward", degree := degree, count := count*closed_points[i, k]`count>);
                elif closed_points[i, k]`degree/closed_points[j, l]`degree eq degree then
                    AddEdge(~quotient_graph, VertexSet(quotient_graph)![i, k], VertexSet(quotient_graph)![j, l], rec<edge_rec_format | type := "pullback", degree := degree, count := count*closed_points[i, k]`count>);
                end if;
            end for;
        end for; 
    end for;
end for;

"Quotient graph properties:"; IndentPush();
"Curves:", #curves;
"Vertices:", #Vertices(quotient_graph);
"Edges:", #Edges(quotient_graph);
"Terminal vertices:", #[v : v in Vertices(quotient_graph) | OutDegree(v) eq 0];
"Potentially isolated vertices:", #[point : point in VertexLabels(quotient_graph) | point`potentially_isolated];
""; IndentPop();

"Isolation graph properties: (determined from quotient graph)"; IndentPush();
"Curves:", &+[curve`count : curve in curves];
"Vertices:", &+[point`count : point in VertexLabels(quotient_graph)];
"Edges:", &+[Label(edge)`count : edge in Edges(quotient_graph)];
"Terminal vertices:", &+[Label(v)`count : v in Vertices(quotient_graph) | OutDegree(v) eq 0];
"Potentially isolated vertices:", &+[point`count : point in VertexLabels(quotient_graph) | point`potentially_isolated];
""; IndentPop();

isolated_subgraph := sub<quotient_graph | {v : v in Vertices(quotient_graph) | Label(v)`potentially_isolated}>;
"Potentially isolated subgraph proprties:"; IndentPush();
"Vertices:", #Vertices(isolated_subgraph);
"Edges:", #Edges(isolated_subgraph);
"Initial vertices:", [Label(v) : v in Vertices(isolated_subgraph) | InDegree(v) eq 0];
"Vertices:", [point : point in VertexLabels(isolated_subgraph)];
IndentPop();

quit;
