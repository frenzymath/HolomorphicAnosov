import HolomorphicAnosov.Topology.CairnsOppositeCellsRegularClosedUnion
import HolomorphicAnosov.Topology.CairnsOppositeCellsBoundarySeparation
import HolomorphicAnosov.Topology.CairnsPolygonAmbientExtension

/-!
# Ambient amalgamation of two polygonal cells on opposite sides of a segment

Source: Stewart S. Cairns, *An Elementary Proof of the Jordan-Schoenflies Theorem* (1951),
preliminaries 2(A,B), pp. 860–861. The exterior construction uses the source decomposition's
finite polygonal-annulus parameterization. The final pasting and its bounded-cell
input are proved through the named ambient-extension auxiliary.
-/

namespace HolomorphicAnosov

open Set

/-- Two known polygonal cells with a common segment and opposite local sides amalgamate
with every prescribed boundary homeomorphism extending over the entire plane.

Source: Cairns (1951), preliminary 2(A,B), pp. 860–861; DAG node
`topo.cairns_polygon_opposite_cells_ambient_amalgamation_g2`.

The real plane is `ℂ` with its canonical Euclidean metric. The two finite polygons use
Mathlib's `Polygon.boundary ℝ`; simplicity is expressed by injective vertices, nonzero
edges, and exact pairwise edge intersections. Collinear redundant vertices are allowed.
The assumed homeomorphisms of the ambient plane send the original two boundaries to the
unit circle. Each `Cᵢ` is the actual bounded complementary component through `uᵢ`, and its
closed cell is `closure Cᵢ`. The common nondegenerate segment, contained in both simple
boundaries, is their boundary arc; no separate arbitrary-arc or Jordan theorem is assumed.

The local side condition uses a unit normal `ν`: `((z-x)/ν).re` is the signed normal
coordinate, and `((b-a)/ν).re = 0` makes the segment's direction perpendicular to it.
The positive and negative half-disks are identified with the actual `C₁` and `C₂`.
All component, closure, frontier, and boundedness assertions below use the ambient plane.
The final quantifier ranges over EVERY homeomorphism of the actual remaining boundary
onto the unit circle; its equality with `H` is equality of the underlying plane points.

Complete natural-language proof from the current DAG node:

C1. Normalize each assumed ambient circle map by a similarity to the unit circle. Its bounded
complementary component maps to the open unit disk and its closure Di to the closed disk: the circle
has exactly its convex open disk and its path-connected unbounded exterior, and the compact image of
Di cannot contain the latter. A homeomorphism b:S1→S1 has radial extension B(0)=0, B(rz)=r b(z) for
r>0, with inverse defined by b⁻¹. Continuity away from0 follows from polar coordinates, and
continuity at0 follows from ∥B(x)∥=∥x∥. Thus any prescribed boundary map on either known Di can be
imposed independently. In particular the interiors of Di are path-connected, Di is regular closed
and its frontier is qi. These facts are only for the two curves assumed known, not for p.

C2. Write Ui=interior Di. Away from d, q1 and q2 have positive distance from the other closed cell
locally, and the finite incident polygon edges divide a sufficiently small disk into exactly two
half-disk sectors, or two angular sectors at a vertex; Ui occupies exactly one. At every point of d°
the stipulated opposite half-disks show that D contains a full neighborhood. At either endpoint of d
choose a disk meeting only the incident rays of q1 and q2. The two cell sectors are disjoint except
along the d ray, by D1∩D2=d; they join to one angular sector whose two outside rays are exactly the
incident edges of p. The complementary sector has positive angle, since those outside rays cannot
coincide without an extra common boundary segment. Thus each d endpoint is on the frontier, not in
the interior. Consequently U=interior D=U1∪U2∪d°, D=closure U, and frontier D=p. U is
path-connected: each Ui is, and a small disk around any one seam point joins both Ui through d°; any
other seam point joins Ui in its own such disk. D is compact. This also checks all local
inside/outside sectors at every p vertex without invoking Jordan for p.

C3. Construct a finite exterior collar, rather than assuming an exterior disk. Remove only redundant
collinear vertices of p. Orient its vertex cycle v0,…,v(n−1) so the just identified local interior
sectors lie left; the orientations of the known q1,q2 can be chosen this way and their common d
directions are opposite, so the resulting p cycle is consistent. Let ni be the unit right normal to
edge vi vi+1. At each vertex solve ni−1·wi=ni·wi=1; the two normals are independent after collinear
removal, since a simple polygon cannot reverse along an edge. For sufficiently small ε>0, form
Qi=[vi,vi+1,vi+1+εwi+1,vi+εwi]. Its outer edge is parallel to the original edge, at outward distance
ε. The oriented areas of its two diagonal triangles have the same nonzero sign as their first-order
terms −ε|vi+1−vi|, so Qi is a nondegenerate convex quadrilateral. Near a vertex, the shared radial
segment vi+[0,ε]wi divides exactly the exterior sector into the two incident strips: the dot-product
equations put it in the exterior sector and the two triangle wedges on opposite sides. Farther from
the vertices, each strip lies in the locally exterior half-plane. Choose ε small enough for these
finitely many sector checks and for separation of all nonincident edge strips and all vertex disks;
finite positive distances between compact disjoint nonincident edges ensure this. Thus Qi\p⊂R²\D,
consecutive Qi meet exactly in the shared radial segment, and nonconsecutive Qi are disjoint. The
two affine triangle maps in each strip paste with identical seam values to map the cyclic edge
parameter times [0,ε] bijectively onto their union. Inverse affine triangle maps paste on the same
finite closed cover, so this is a homeomorphism. In particular the positive-width exterior collar C,
obtained by omitting level0, is path-connected. At every edge and vertex its image contains all
exterior points in a sufficiently small neighborhood, by the explicit half-plane and sector wedges;
finiteness gives a neighborhood of p covered on its exterior side. The argument is valid at reflex
vertices as well: the radial segment cuts the smaller exterior sector there, while at convex
vertices the two wedges cover the larger exterior sector.

C4. The exterior E=R²\D is path-connected. Given x,y∈E, choose a polygonal path between them whose
segments avoid p vertices and are not parallel or coincident with any p edge. A small generic
perturbation of finitely many intermediate vertices achieves this while keeping small initial/final
segments in E. Each segment then meets the finite polygon p transversely in finitely many points;
hence the path has finitely many intervals in U. For each such interval, trim at exterior points
just before its entrance and after its exit; by the collar neighborhood property these trimming
points lie in C. Replace that part by a path inside the path-connected C. Choose disjoint small
trimming intervals for the finitely many crossings. All replacements lie in E and eliminate every
part in D, giving a path in E. Since D is compact, E contains all points outside a large disk and is
unbounded. Now R²\p is the disjoint union U∪E of two nonempty path-connected open sets. They are
therefore exactly its two connected components, with U bounded, closure U=D, and frontier U=p. Also
frontier E=p: E has no frontier off p by the open decomposition, and the exterior collar accumulates
at every p point. This proves all separation/frontier assertions before any annulus homeomorphism is
used.

C5. Construct the prescribed bounded-cell map f:D→closedBall(0,1). Parametrize d monotonically onto
the horizontal diameter. Parametrize the complementary outer arcs of q1,q2 onto the upper and lower
semicircles, with the same diameter endpoint values. These are homeomorphisms of qi onto the
boundaries of the respective closed half-disks. Each closed half-disk is a compact bounded convex
body with nonempty interior, so the convex-body ambient homeomorphism, composed with the independent
radial boundary adjustment in step1, extends this boundary map over Di. Paste these two maps on
D1,D2 and their inverses on the two half-disks. They agree on d, and the exact intersection
hypotheses show that points from different cells can have equal images only along this diameter.
Thus f is a homeomorphism, taking p onto S1. Postcompose by the radial circle extension of β∘(f|p)⁻¹
so f|p=β exactly.

C6. Choose a closed rectangle R with D⊂interior R. The explicit D from steps2–4 is compact regular
closed, has nonempty path-connected interior and path-connected complement, and frontier the simple
polygon p, so the polygonal-annulus theorem applies to A=R\interior D and β. It gives Φ:A→{1≤∥x∥≤2}
with Φ|p=β and Φ(∂R) the radius2 circle. This is precisely the exterior input that cannot be
supplied by the abstract disk map. No Jordan/crosscut theorem or generic invariance-of-domain
statement is substituted for this dependency, and its own finite annulus straightening proof remains
an open lower mathematical gap.

C7. Use the convex-body theorem again for R and rescale its ambient map G so G(R) is the radius2
closed disk and G(∂R) its circle. Define b:S1→S1 by b(z)=Φ(G⁻¹(2z))/2. On the closed exterior
X=R²\interior R set F(x)=∥G(x)∥ b(G(x)/∥G(x)∥). There ∥G(x)∥≥2, so the formula is continuous, agrees
with Φ on ∂R, and is a homeomorphism onto {∥x∥≥2}, with inverse obtained using b⁻¹ and G⁻¹. Paste f,
Φ, F on the finite closed cover D,A,X of the plane. The overlaps are respectively p, ∂R, and empty;
formulas agree there. Their image regions are the closed radius1 disk, the closed radii1–2 annulus,
and the closed exterior radius2 region, intersecting in precisely the matching circles. Thus the
pasted function H is a bijection, and its inverse is the corresponding closed-cover pasting of the
three inverse maps. Both are continuous by two applications of closed-pair pasting. H is the
required ambient plane homeomorphism, H(D)=closedBall(0,1), and H|p=β.

-/

theorem cairns_polygon_opposite_cells_ambient_amalgamation_remaining
    {n₁ n₂ : ℕ} (q₁ : Polygon ℂ (n₁ + 3)) (q₂ : Polygon ℂ (n₂ + 3))
    (hq₁_vertices : Function.Injective q₁.vertices)
    (hq₁_edges : q₁.HasNondegenerateEdges)
    (hq₁_simple : ∀ i j : Fin (n₁ + 3), i ≠ j →
      q₁.edgeSet ℝ i ∩ q₁.edgeSet ℝ j =
        ({q₁ i, q₁ (finRotate (n₁ + 3) i)} : Set ℂ) ∩
        {q₁ j, q₁ (finRotate (n₁ + 3) j)})
    (hq₂_vertices : Function.Injective q₂.vertices)
    (hq₂_edges : q₂.HasNondegenerateEdges)
    (hq₂_simple : ∀ i j : Fin (n₂ + 3), i ≠ j →
      q₂.edgeSet ℝ i ∩ q₂.edgeSet ℝ j =
        ({q₂ i, q₂ (finRotate (n₂ + 3) i)} : Set ℂ) ∩
        {q₂ j, q₂ (finRotate (n₂ + 3) j)})
    (hq₁_ambient : ∃ F : ℂ ≃ₜ ℂ, F '' q₁.boundary ℝ = Metric.sphere (0 : ℂ) 1)
    (hq₂_ambient : ∃ F : ℂ ≃ₜ ℂ, F '' q₂.boundary ℝ = Metric.sphere (0 : ℂ) 1)
    (u₁ u₂ : ℂ) (hu₁ : u₁ ∉ q₁.boundary ℝ) (hu₂ : u₂ ∉ q₂.boundary ℝ)
    (C₁ C₂ : Set ℂ)
    (hC₁ : C₁ = connectedComponentIn (q₁.boundary ℝ)ᶜ u₁)
    (hC₂ : C₂ = connectedComponentIn (q₂.boundary ℝ)ᶜ u₂)
    (hC₁_bounded : Bornology.IsBounded C₁) (hC₂_bounded : Bornology.IsBounded C₂)
    (a b : ℂ) (hab : a ≠ b)
    (hq_inter : q₁.boundary ℝ ∩ q₂.boundary ℝ = segment ℝ a b)
    (hD_inter : closure C₁ ∩ closure C₂ = segment ℝ a b)
    (h_opposite : ∀ x ∈ openSegment ℝ a b, ∃ ε : ℝ, 0 < ε ∧
      ∃ ν : ℂ, ‖ν‖ = 1 ∧ ((b - a) / ν).re = 0 ∧
        Metric.ball x ε ∩ C₁ = {z : ℂ | z ∈ Metric.ball x ε ∧ 0 < ((z - x) / ν).re} ∧
        Metric.ball x ε ∩ C₂ = {z : ℂ | z ∈ Metric.ball x ε ∧ ((z - x) / ν).re < 0})
    (hlocal : IsOpen C₁ ∧ IsOpen C₂ ∧
      IsCompact (closure C₁ ∪ closure C₂) ∧
      IsConnected (closure C₁ ∪ closure C₂) ∧
      closure (interior (closure C₁ ∪ closure C₂)) = closure C₁ ∪ closure C₂ ∧
      (interior (closure C₁ ∪ closure C₂)).Nonempty ∧
      openSegment ℝ a b ⊆ interior (closure C₁ ∪ closure C₂)) :
    let p : Set ℂ := (q₁.boundary ℝ ∪ q₂.boundary ℝ) \ openSegment ℝ a b
    let D : Set ℂ := closure C₁ ∪ closure C₂
    (∃ (n : ℕ) (q : Polygon ℂ (n + 3)),
      Function.Injective q.vertices ∧ q.HasNondegenerateEdges ∧
      (∀ i j : Fin (n + 3), i ≠ j →
        q.edgeSet ℝ i ∩ q.edgeSet ℝ j =
          ({q i, q (finRotate (n + 3) i)} : Set ℂ) ∩
          {q j, q (finRotate (n + 3) j)}) ∧ q.boundary ℝ = p) ∧
    (∃ B E : Set ℂ,
      (fun z : ℂ ↦ connectedComponentIn pᶜ z) '' pᶜ = {B, E} ∧
      IsConnected B ∧ IsConnected E ∧ IsOpen B ∧ IsOpen E ∧
      Bornology.IsBounded B ∧ ¬ Bornology.IsBounded E ∧
      closure B = D ∧ frontier B = p ∧ frontier E = p) ∧
    (∀ β : p ≃ₜ Metric.sphere (0 : ℂ) 1, ∃ H : ℂ ≃ₜ ℂ,
      H '' D = Metric.closedBall (0 : ℂ) 1 ∧ ∀ z : p, H z = (β z : ℂ)) := by
  obtain ⟨hpoly, hregions⟩ := cairns_opposite_cells_boundary_separation q₁ q₂
    hq₁_vertices hq₁_edges hq₁_simple hq₂_vertices hq₂_edges hq₂_simple hq₁_ambient
    hq₂_ambient u₁ u₂ hu₁ hu₂ C₁ C₂ hC₁ hC₂ hC₁_bounded hC₂_bounded a b hab hq_inter
    hD_inter h_opposite hlocal
  refine ⟨hpoly, hregions, ?_⟩
  intro β
  obtain ⟨H₁, hH₁⟩ := hq₁_ambient
  obtain ⟨H₂, hH₂⟩ := hq₂_ambient
  have hcell := opposite_ambient_cells_disk_chart (q₁.boundary ℝ) (q₂.boundary ℝ)
    C₁ C₂ H₁ H₂ hH₁ hH₂ u₁ u₂ hu₁ hu₂ hC₁ hC₂ hC₁_bounded hC₂_bounded a b hab
    hq_inter hD_inter
  exact cairns_polygon_ambient_extension hpoly hregions hcell β

theorem cairns_polygon_opposite_cells_ambient_amalgamation
    {n₁ n₂ : ℕ} (q₁ : Polygon ℂ (n₁ + 3)) (q₂ : Polygon ℂ (n₂ + 3))
    (hq₁_vertices : Function.Injective q₁.vertices)
    (hq₁_edges : q₁.HasNondegenerateEdges)
    (hq₁_simple : ∀ i j : Fin (n₁ + 3), i ≠ j →
      q₁.edgeSet ℝ i ∩ q₁.edgeSet ℝ j =
        ({q₁ i, q₁ (finRotate (n₁ + 3) i)} : Set ℂ) ∩
        {q₁ j, q₁ (finRotate (n₁ + 3) j)})
    (hq₂_vertices : Function.Injective q₂.vertices)
    (hq₂_edges : q₂.HasNondegenerateEdges)
    (hq₂_simple : ∀ i j : Fin (n₂ + 3), i ≠ j →
      q₂.edgeSet ℝ i ∩ q₂.edgeSet ℝ j =
        ({q₂ i, q₂ (finRotate (n₂ + 3) i)} : Set ℂ) ∩
        {q₂ j, q₂ (finRotate (n₂ + 3) j)})
    (hq₁_ambient : ∃ F : ℂ ≃ₜ ℂ, F '' q₁.boundary ℝ = Metric.sphere (0 : ℂ) 1)
    (hq₂_ambient : ∃ F : ℂ ≃ₜ ℂ, F '' q₂.boundary ℝ = Metric.sphere (0 : ℂ) 1)
    (u₁ u₂ : ℂ) (hu₁ : u₁ ∉ q₁.boundary ℝ) (hu₂ : u₂ ∉ q₂.boundary ℝ)
    (C₁ C₂ : Set ℂ)
    (hC₁ : C₁ = connectedComponentIn (q₁.boundary ℝ)ᶜ u₁)
    (hC₂ : C₂ = connectedComponentIn (q₂.boundary ℝ)ᶜ u₂)
    (hC₁_bounded : Bornology.IsBounded C₁) (hC₂_bounded : Bornology.IsBounded C₂)
    (a b : ℂ) (hab : a ≠ b)
    (hq_inter : q₁.boundary ℝ ∩ q₂.boundary ℝ = segment ℝ a b)
    (hD_inter : closure C₁ ∩ closure C₂ = segment ℝ a b)
    (h_opposite : ∀ x ∈ openSegment ℝ a b, ∃ ε : ℝ, 0 < ε ∧
      ∃ ν : ℂ, ‖ν‖ = 1 ∧ ((b - a) / ν).re = 0 ∧
        Metric.ball x ε ∩ C₁ = {z : ℂ | z ∈ Metric.ball x ε ∧ 0 < ((z - x) / ν).re} ∧
        Metric.ball x ε ∩ C₂ = {z : ℂ | z ∈ Metric.ball x ε ∧ ((z - x) / ν).re < 0}) :
    let p : Set ℂ := (q₁.boundary ℝ ∪ q₂.boundary ℝ) \ openSegment ℝ a b
    let D : Set ℂ := closure C₁ ∪ closure C₂
    (∃ (n : ℕ) (q : Polygon ℂ (n + 3)),
      Function.Injective q.vertices ∧ q.HasNondegenerateEdges ∧
      (∀ i j : Fin (n + 3), i ≠ j →
        q.edgeSet ℝ i ∩ q.edgeSet ℝ j =
          ({q i, q (finRotate (n + 3) i)} : Set ℂ) ∩
          {q j, q (finRotate (n + 3) j)}) ∧ q.boundary ℝ = p) ∧
    (∃ B E : Set ℂ,
      (fun z : ℂ ↦ connectedComponentIn pᶜ z) '' pᶜ = {B, E} ∧
      IsConnected B ∧ IsConnected E ∧ IsOpen B ∧ IsOpen E ∧
      Bornology.IsBounded B ∧ ¬ Bornology.IsBounded E ∧
      closure B = D ∧ frontier B = p ∧ frontier E = p) ∧
    (∀ β : p ≃ₜ Metric.sphere (0 : ℂ) 1, ∃ H : ℂ ≃ₜ ℂ,
      H '' D = Metric.closedBall (0 : ℂ) 1 ∧ ∀ z : p, H z = (β z : ℂ)) := by
  have hlocal := cairns_opposite_cells_regular_closed_union q₁ q₂ hq₁_ambient hq₂_ambient
    u₁ u₂ hu₁ hu₂ C₁ C₂ hC₁ hC₂ hC₁_bounded hC₂_bounded a b hab hD_inter h_opposite
  exact cairns_polygon_opposite_cells_ambient_amalgamation_remaining q₁ q₂ hq₁_vertices
    hq₁_edges hq₁_simple hq₂_vertices hq₂_edges hq₂_simple hq₁_ambient hq₂_ambient
    u₁ u₂ hu₁ hu₂ C₁ C₂ hC₁ hC₂ hC₁_bounded hC₂_bounded a b hab hq_inter hD_inter
    h_opposite hlocal
