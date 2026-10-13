import HolomorphicAnosov.Topology.CairnsAnnulusBoundaryCorrection
import HolomorphicAnosov.Topology.CairnsPolygonalAnnulusCompact
import HolomorphicAnosov.Topology.CairnsPolygonalAnnulusFrontierSubset
import HolomorphicAnosov.Topology.CairnsPolygonalAnnulusRectangleCompact
import HolomorphicAnosov.Topology.CairnsPolygonalAnnulusFrontierDecomposition
import HolomorphicAnosov.Topology.CairnsPolygonalAnnulusFrontierDisjoint
import HolomorphicAnosov.Topology.CairnsPolygonalAnnulusOuterFrontierSubset
import HolomorphicAnosov.Topology.CairnsPolygonalAnnulusBase
import HolomorphicAnosov.Topology.AnnulusBoundaryExtension
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Affine.Isometry
import Mathlib.Geometry.Polygon.Basic
import Mathlib.Topology.Connected.PathConnected

/-!
# Prescribed inner boundary of a polygonal closed annulus

Source: Cairns, *An Elementary Proof of the Jordan-Schoenflies Theorem* (1951),
preliminary 2(B), p. 860, used in Theorem 2.1, p. 861. The exterior-annulus proof is
omitted there. The natural-language proof below is the current DAG's agent supplement
for that omission, conditional on its named Gallier–Xu source prerequisite.
-/

open Set

namespace HolomorphicAnosov.Topology

local notation "Plane" => EuclideanSpace ℝ (Fin 2)

/-- Parameterization of the closed region between a simple polygon and a surrounding rectangle.

Cairns, An Elementary Proof of the Jordan-Schoenflies Theorem (1951), printed p.860
preliminary2(B), used on p.861 in Theorem2.1; literature/cairns-jordan-schoenflies-1951.pdf
physical pp.2–3. This finite exterior-annulus argument is omitted there. Agent exception filling
that omission in topo.cairns_polygon_opposite_cells_ambient_amalgamation_g2, not a citation of an
already proved annulus theorem.

All geometric hypotheses are stated on the original Euclidean plane. Regular closedness is
`closure (interior D) = D`. Simplicity is expressed using Mathlib's finite polygon vertices
and edge sets: vertices are distinct and distinct edges meet only at endpoints incident to
both. Redundant collinear vertices are allowed. A nondegenerate rectangle is an affine
isometric image of a coordinate box with strictly positive side lengths, so arbitrary
translations, rotations and reflections are included.

The inner-boundary assertion includes its inclusion in the annular domain and equality to
the prescribed homeomorphism. The outer-boundary assertion specifies its image as a set;
no outer pointwise correspondence, orientation or isotopy is assumed.

Current proof origin: agent supplement to the omission in
`topo.cairns_polygon_opposite_cells_ambient_amalgamation_g2`. This is not credited to
Cairns as a written annulus proof. Complete current natural-language proof:

1. The annular region A is an explicit compact subset, not an assumed annulus. Since D is regular
closed with frontier p, its exterior has points arbitrarily near every p point, and A has boundary
p∪∂R. At a nonvertex p point, a small disk minus p has two half-disks; membership in interior D
and in its complement is locally constant, and both occur, hence exactly one half-disk belongs to
each. At a vertex, the two incident rays divide a small disk into two angular sectors and the same
argument assigns exactly one to each. A therefore has the corresponding exterior sector there. At
∂R it has the usual inward half-disk or corner. Connectivity of the exterior implies connectivity
inside R: replace each excursion of a polygonal exterior path beyond R by a path just inside ∂R,
possible because the compact D has positive distance from ∂R. Endpoint paths in the same collar
connect all boundary points to this connected open region. The corresponding interior sector is
the local chart for D; an angular sector with angle strictly between0 and2π is homeomorphic to a
half-disk by rescaling its angle. Collinear redundant polygon vertices give the same half-disk
chart. Regular closedness gives D=closure(interior D), so its connected interior has connected
closure, and its boundary is exactly p. Thus D is a connected compact 2-manifold with one boundary
cycle; A is one with two disjoint boundary cycles, p and ∂R. These conclusions use local finite
sectors and the given interior/exterior path connectivity, not polygon separation.

2. A finite embedded triangulation can be built without any Jordan or polygon theorem. Choose a
direction giving distinct abscissae to all vertices of p and R and no vertical edges. In every
open strip between consecutive vertex abscissae, the boundary segments present are affine graphs
with fixed order, since distinct boundary edges do not cross. Between successive graphs,
membership in D is constant: the band is connected and avoids frontier D. Retain precisely the
exterior bands lying in R. Their closures are bounded convex trapezoids or triangles. There are
finitely many, and they cover A, including p by exterior density and ∂R by D⊂interior R. Subdivide
their vertical sides at every endpoint from either adjacent strip, so intersections are complete
unions of shared edges. Triangulate each convex cell by a fan from an interior point through its
subdivided boundary edges. Degenerate zero-area cells are already faces of neighboring
positive-area cells. This gives an actual finite straight triangulation of A with boundary
subcomplex exactly p∪∂R and local vertex links intervals on that boundary and circles in the
interior. Keep also every band inside D, so that the same construction triangulates the whole R
and gives subcomplexes K_D and K_A with union K_R and intersection precisely the subdivided
polygon K_p. At every vertex the complete triangle fan in R is either a full circle, a half-plane,
or a rectangle corner. The sector argument restricts each fan in D and A to a single interval at
their respective boundary vertices. All triangles inherit the ambient counterclockwise
orientation, which induces opposite directions on shared edges. Both complexes therefore meet the
finite normal-form child hypotheses. D is nonempty by its interior hypothesis; A has nonempty
interior because of the positive outer margin.

3. Compute finite Euler counts without a planar Euler/Jordan premise. Write I for the number of
vertices of K_R in interior R and B for those on ∂R, including the four corners. If F is the
triangle count, summing triangle angles gives πF=2πI+π(B−4)+4(π/2), hence F=2I+B−2. If E_i and E_b
are the interior and boundary edge counts, then E_b=B and 3F=2E_i+B, by counting triangle-edge
incidences. Therefore χ(K_R)=I+B−(E_i+B)+F=1. The subdivided polygon has the same number of
vertices and edges and no triangles, so χ(K_p)=0. Finite inclusion-exclusion of the simplex sets
gives χ(K_D)+χ(K_A)=χ(K_R)+χ(K_p)=1. Neither a Jordan winding formula nor homological planar
duality is used.

4. Apply the named source finite orientable normal-form theorem separately to K_D with b=1 and K_A
with b=2. It gives integers g_D,g_A≥0 with χ(K_D)=1−2g_D and χ(K_A)=−2g_A. Substituting into the
explicitly proved count identity yields 1−2(g_D+g_A)=1, so g_D=g_A=0. The theorem also supplies
the actual finite cut-and-paste equivalence and its quotient homeomorphism, rather than assuming a
genus classification from the number of boundaries. For A the single face consequently has word c1
h1 c1⁻¹ c2 h2 c2⁻¹, with precisely the two hj loops as its boundary. The normal-form child remains
open, so this is a conditional complete parent proof, not a proved source theorem assumption.

5. Realize this last word by a rectangle: let h1 be its top edge and h2 its bottom edge, while the
right edge is divided into c1⁻¹ followed by c2 and the left edge into c2⁻¹ followed by c1, in
cyclic boundary order starting at the top-left corner. The two midpoint vertices represent the
inner normal-form vertex. Choose matching length/interval parameters on c1 and c2 so the
prescribed identifications pair left and right at equal heights. The resulting quotient is
explicitly ([0,1]×[1,2])/((0,r)∼(1,r)), since the two half-edge identifications concatenate to the
complete side identification. The map [(t,r)]↦r(cos(2πt),sin(2πt)) is a continuous bijection onto
the closed round annulus; its only fiber pairs are the identified sides. The quotient is compact
because its surjective quotient map is continuous and the rectangle [0,1]×[1,2] is compact, so it
is a continuous image of that compact rectangle. The round annulus is Hausdorff as a subspace of
R². Form the equivalence from this proved bijection and apply the named
Continuous.homeoOfEquivCompactToT2 constructor to its continuous forward map; this supplies
continuous inverse and hence a homeomorphism. It sends h1,h2 onto the two round boundary circles.
The source cut-and-paste homeomorphism sends p and ∂R bijectively to these two loops. If they have
the wrong assignment, compose with rz↦(3−r)z. This gives Ψ with p on radius1 and ∂R on radius2.
The rectangle is a parametrized model face, not an assertion that an arbitrary cut region is
already a disk.

6. Once one level-preserving annulus homeomorphism Ψ is constructed, impose the specified β
without an independent outer orientation condition. Set b=β∘(Ψ|p)⁻¹:S1→S1 and apply rz↦r b(z)
simultaneously on all radii 1≤r≤2. Its inverse is rz↦r b⁻¹(z); both are continuous, so the
corrected map agrees with β and maps the outer boundary onto the radius2 circle. This step needs
no isotopy between independently prescribed boundary maps.
-/
theorem cairns_polygonal_annulus_parameterization
    (D R : Set Plane)
    (hcompact : IsCompact D)
    (hregular : closure (interior D) = D)
    (hinterior_nonempty : (interior D).Nonempty)
    (hinterior_path : IsPathConnected (interior D))
    (hexterior_path : IsPathConnected Dᶜ)
    (hpolygon : ∃ n : ℕ, 3 ≤ n ∧ ∃ P : Polygon Plane n,
      Function.Injective P ∧
      (∀ i j : Fin n, i ≠ j →
        P.edgeSet ℝ i ∩ P.edgeSet ℝ j ⊆
          ({P i, P (finRotate n i)} ∩ {P j, P (finRotate n j)} : Set Plane)) ∧
      frontier D = P.boundary ℝ)
    (hrectangle : ∃ e : Plane ≃ᵃⁱ[ℝ] Plane, ∃ a b : Fin 2 → ℝ,
      (∀ i, a i < b i) ∧
      R = e '' {x : Plane | ∀ i, a i ≤ x i ∧ x i ≤ b i})
    (hcontain : D ⊆ interior R)
    (β : frontier D ≃ₜ Metric.sphere (0 : Plane) 1) :
    ∃ Φ : ↥(R \ interior D) ≃ₜ {x : Plane | 1 ≤ ‖x‖ ∧ ‖x‖ ≤ 2},
      (∀ x : frontier D, ∃ y : ↥(R \ interior D),
        (y : Plane) = (x : Plane) ∧ (Φ y : Plane) = (β x : Plane)) ∧
      (fun x : ↥(R \ interior D) ↦ (Φ x : Plane)) ''
        {x : ↥(R \ interior D) | (x : Plane) ∈ frontier R} = Metric.sphere (0 : Plane) 2 := by
  have hclosedD : IsClosed D := hcompact.isClosed
  have hcompactR := cairns_polygonal_annulus_rectangle_compact R hrectangle
  have hcompactA := cairns_polygonal_annulus_compact D R hcompactR
  have hinner_subset := cairns_polygonal_annulus_frontier_subset D R hcompact hcontain
  have houter_subset := cairns_polygonal_annulus_outer_frontier_subset D R hcompactR hcontain
  have hboundaries_disjoint := cairns_polygonal_annulus_frontier_disjoint D R hcompact hcontain
  have hfrontierA := cairns_polygonal_annulus_frontier_decomposition D R hcompact hcompactR
    hregular hcontain
  have hbase := cairns_polygonal_annulus_base D R hcompact hregular hinterior_nonempty
    hinterior_path hexterior_path hpolygon hrectangle hcontain
  obtain ⟨γ, Ψ, hinner, houter⟩ := hbase
  exact cairns_annulus_boundary_correction hinner houter β

end HolomorphicAnosov.Topology
