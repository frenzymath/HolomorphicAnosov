import HolomorphicAnosov.Topology.CairnsRadialPatchConvexControl
import HolomorphicAnosov.Topology.CairnsResidualStarRecurrenceProperties
import HolomorphicAnosov.Topology.CairnsStarSectorBoundaryContact
import HolomorphicAnosov.Topology.CairnsShrinkingResidualExhaustion
import HolomorphicAnosov.Topology.AccumulatingChordContinuity
import HolomorphicAnosov.Topology.CairnsNormalizedCircleGap
import HolomorphicAnosov.Topology.Plane.CairnsChordSectorSeparation
import HolomorphicAnosov.Topology.Plane.CairnsConvexStarSectorExtension
import HolomorphicAnosov.Topology.CairnsResidualStarRefinement
import HolomorphicAnosov.Topology.CairnsGapMeshEmpty
import HolomorphicAnosov.Topology.CairnsResidualChordRefinementData

/-!
# Cairns's residual-chord refinement and uniform shrinking

Source: Cairns (1951), §4(B,C), pp.864–865, recurrent Hypothesis (1)–(5),
equations (4.3),(4.4), Lemma 4.1 and its corollary. The actual star recurrence
is defined by the imported concrete data, not supplied as a shrinking or cell
hypothesis. The prescribed boundary homeomorphism may reverse orientation.
Printed Lemma 4.1's literal existence of a residual sector in every small
boundary neighborhood is stronger than its stated uniform-smallness meaning;
this statement quantifies existing sectors and allows an empty residual family.
-/


namespace HolomorphicAnosov.Topology.Plane

open Set CairnsStar CairnsRefinement

/--
Starting with any chord of the original bounded complementary component,
construct Cairns's two initial stars and the full simultaneous outside-star
recurrence. All cells, homeomorphisms, frontiers, exact component partitions,
convex-disk bounds, normalized source-parameter mesh shrinking and both
exhaustions are conclusions. A stage indexed by zero is source stage one.
Angular representatives label actual component sets and never duplicate them.
The target region is the image under the same constructed stage map.

Natural-language proof (the full current source-backed node proof):

1. Fix the embedding σ and its inverse on c, and give the parameter circle 𝕋=S¹ normalized arc
length. The bounded complementary component a is open and polygonally connected: the points
reachable from one point by finite chains of balls in a form a relatively open and relatively
closed class. Its frontier is contained in c, since a ball disjoint from c meeting a belongs
wholly to that complementary component. A chord exists without Jordan existence or Schoenflies:
choose x∈a and any line through x, and in each direction take the first exit from a. Boundedness
makes both exit distances finite, openness makes them positive, and the exit points D1,D2 lie on
frontier(a)⊂c. Their full intervening open segment lies in a. The statement permits starting
with any such chord, not just this choice.

2. Record the geometric collar consequences of the named star construction, which will be used
instead of arbitrary-arc amalgamation. A closed star has base d, front μ*, and continuous
positive radial radius about its midpoint M on the closed angular interval. At M the positive
minimum radius supplies a small half-disk on the star side of d. At any other point z∈d° its
radial distance along the corresponding endpoint direction is strictly less than the endpoint
radius |D_i−M|; continuity gives the same strict inequality for all sufficiently nearby
directions into that side. Thus every z∈d° has a half-disk lying in the open star. For z in an
open front chord e°, choose a small disk in a meeting μ* only in e: the rest of the compact
simple front is separated from z by taking a short parameter subarc inside e°. Its base d misses
z. The star radial inequality occupies the M-side of the straight line through e locally, and
its opposite side is outside its closure. Equivalently the continuous angle/radius coordinates
show that z is on the boundary and that the inside side has positive strict margin. These are
strict one-sided half-disk collars at every interior base/front chord point. They use the
existing star's actual radial/frontier assertions, not an arbitrary Jordan or invariance-of-
domain theorem.

3. Prove the residual-gap rule for a single star in a sector β with original arc μ. Its compact
contact set C*=μ*∩c contains both base endpoints and the selected first perpendicular contact P.
The ordered replacement assertion of the star theorem associates each component I of μ\C* with
exactly one noncontact front chord e, with endpoints ∂I and e°⊂a. Apply the chord-sector theorem
to e in the original bounded component a and call B_e the sector whose allowed frontier lies in
e∪closure(I). The connected star avoids e°, hence is wholly on one chord side. It cannot be
inside B_e: then its original base d° would, by approaching from the star and using that d°
misses frontier(B_e), also lie in B_e. Approaching the original base endpoint outside closure(I)
would violate frontier(B_e)⊂e∪closure(I). Such an endpoint exists because I is a proper subarc
of μ omitting P. Therefore B_e is on the opposite side from the star. The local front collar
shows a half-disk of B_e inside β near e°. Since B_e avoids d° and is connected, it lies
entirely in β. For two disjoint replacement arcs I,J, the interior of the J chord cannot enter
B_e: it is connected and disjoint from e, and one of its endpoints lies outside e∪closure(I),
contradicting the frontier containment if it did enter. If the two outer sectors met,
connectedness and chord separation would force one to contain the other; taking limits to the
contained sector's chord would then put that chord in the other sector, the same contradiction.
Thus these B_e are pairwise disjoint.

4. The preceding sectors exhaust β\closure(β*). For a point x in this set, choose a polygonal path
inside β to a point of the open star. The first contact with its compact closure occurs in β, so
is neither on c nor on the original base d. It lies on one open front chord e°. A final small
path piece approaches that point from the outer half-disk of the front collar, hence lies in
B_e. The precontact path has not met e°; its points therefore remain in that same component of
a\e°, so x∈B_e. Conversely B_e avoids the open star by its side label; it also misses the
original base, all c contacts and every other front chord by the preceding nonentry argument,
while e itself is its boundary. Thus B_e avoids the entire closed star. This proves exactly the
star's residual-sector partition; no residual component is invented from an unspecified picture.
The same argument applies to its target circle star. A residual sector's frontier is contained
in its chord and the associated closed curve arc by the named chord theorem.

5. For later countable additions establish a uniform size bound that needs no disk theorem. If a
bounded open sector has frontier in a closed convex disk B and x were outside B, the ray from
the center through x going outward would stay outside B. It could not leave the sector without
crossing its frontier; boundedness forces it to leave, a contradiction. Thus the sector and its
closure lie in B whenever its associated arc lies in B, because its chord also lies in B. If
that arc has image diameter δ, the closed disk of radius δ about either endpoint contains it, so
the sector diameter is at most2δ. The corresponding circle sector has the same bound. For
disjoint proper parameter gap arcs, only finitely many have length≥η for every η>0, as their
total normalized length is at most1. Uniform continuity of σ and h∘σ makes the source and target
arc diameters, hence the source and target sector diameters, tend to0 along every sequence of
distinct gaps. Their stars inherit this bound. Such sectors/stars form null families, and only
finitely many meet any compact set away from c (respectively away from S1): every small sector
lies in a small endpoint-centered disk, and its endpoint is on that boundary.

6. Define the recurrence exactly. The first chord divides a into β+,β−. Let B+,B− be their named
open stars and G+,G− their circle-image stars. Put a1=B+∪d°∪B− and K1=G+∪h_aff(d°)∪G−. Set
S₁=(front(B+)∩c)∪(front(B−)∩c), including the base endpoints. For j≥1 let T_j=σ⁻¹(S_j); its
components I of 𝕋\T_j are the residual parameter gaps, and let d_I be their corresponding
frontier chord. Let β_I be the outside sector from the residual partition. Put B_I=Star(β_I) and
G_I its image under the star extension of the originally prescribed h. Define
a_(j+1)=a_j∪⋃_I(B_I∪d_I°), K_(j+1)=K_j∪⋃_I(G_I∪e_I°), e_I the affine h-image chord, and
S_(j+1)=S_j∪⋃_I(front(B_I)∩c). Define H_(j+1) to be H_j on closure(a_j), h on c, and the
prescribed radial star map on each closure(B_I). All agreements on common bases are literal
affine maps with the same endpoint values. In the first step use the two such maps on the two
stars. The two first perpendicular contacts P+,P− are distinct from the base endpoints and from
each other because they lie in the interiors of the two disjoint curve arcs. Thus every S_j
contains at least four distinct points. If there are no gaps, the recurrence adds nothing; it
does not try to choose a nonexistent star.

7. Verify the simultaneous planar seams and compact closure. In the first step the base collars of
the two stars fill opposite half-disks about each point of d°, so a1 is plane-open and
connected. At stage j an old frontier chord d_I° is locally isolated from all other frontier
pieces: the chord nullness just proved gives local finiteness away from c, and the compact
simple curve parametrization isolates its own chord interior. A small disk in a therefore has
frontier(a_j) exactly its diameter. Each half-disk has constant membership in a_j, since it is
connected and misses the frontier. Frontier membership of the diameter forces at least one half
to be in a_j; the residual chord-side labeling forces it to be the half opposite β_I. The new
star's base collar supplies the other half. Thus the enlarged region is open at every added old
chord. It is connected because every added star connects through its base to a_j. Nullness makes
all other additions locally finite off c, so no unexamined countable seam occurs there. The
closure of the enlarged region is precisely closure(a_j)∪⋃closure(B_I): this union is closed
because limits on distinct stars have an endpoint limit in the old closed S_j⊂closure(a_j),
while limits in finitely many stars or the old closure stay there. It is bounded, hence compact.
Its c-intersection is exactly S_(j+1), which is closed by the same null-family argument. The
first step has the finite analogous closure and closed contact set. These arguments also prove
target plane-openness and compact closure.

8. Verify the new frontier before making any cell claim. Off c, the old frontier chord interiors
have become open seam points. In each old outer sector β_I the remaining complement is, by the
single-star residual rule, the disjoint union of the new B_e sectors; every new front chord has
one local half-disk in its star and one in its residual sector. Therefore its entire open chord
is in the new frontier, and no other finite point is. On c the frontier is exactly the closed
contact set S_(j+1), since the filled region misses c, its closure meets c there, and each
contact is approached by its star or old filled region. Hence frontier(a_(j+1)) is exactly
S_(j+1) and the new gap chords. The single-star residual partition inside the old pairwise
disjoint sectors proves that a\closure(a_(j+1)) is exactly the disjoint union of these new chord
sectors, with their associated new parameter gaps. This establishes the gap correspondence and
frontier by induction, not by presuming the enlarged region already is a disk. To see the
frontier is a simple circle, replace each closed parameter gap of T_(j+1) by the affine
traversal of its assigned chord and leave σ unchanged on T_(j+1). The selected chords avoid c
and one another; shared endpoints have exactly their original cyclic order. Continuity at
distinct-gap accumulations follows from the null bound, and otherwise from a fixed chord or σ.
The map is injective and surjective onto the displayed frontier; compactness of 𝕋 and
Hausdorffness give a homeomorphism. The target frontier has the identical construction with h∘σ.
No arbitrary-curve separation theorem is used.

9. Prove H_j and simultaneous H_(j+1) are homeomorphisms on closure(a_j)∪c and the corresponding
target unions. Apply the accumulating-chord provider to this stage’s frontier-gap family and c.
Its hypotheses hold by the exact disjoint gap correspondence and genuine noncrossing chord
construction; it gives the continuous affine boundary homeomorphism onto the target circle plus
its corresponding chords. The individual star maps agree with this map on every new front and
base chord because they have exactly those affine endpoint values. Each single-star map is a
homeomorphism, equals h on its contacts and is affine on its base. The pairwise disjoint
residual sectors keep star interiors/images disjoint from one another and from the old filled
region; overlaps of closed domains are exactly common bases or contacts where the formulas
agree. Thus the glued map is bijective. Continuity on the old compact domain together with
finitely many new compact stars follows from closed-set pasting. For a convergent sequence in
distinct new stars, source nullness makes both the chosen base endpoint and the sequence points
converge to the same x∈c. Target nullness puts their images within a diameter tending to0 of
h(that endpoint), so they converge to h(x). Every sequence reduces to a fixed-piece subsequence
or this distinct-star case; hence the whole map is continuous, including all countable
accumulations. Its domain closure(a_(j+1))∪c is compact: the old domain contains c and the same
null-family argument proves it closed and bounded. Its target is Hausdorff, so the continuous
bijection has continuous inverse by the named compact closed-map/equivalence leaves. This also
proves H_(j+1)|closure(a_j)=H_j and H_j|c=h. Thus the initial accumulating-chord boundary
homeomorphism is exactly the restriction of the filled map, with continuity at its accumulating
contacts already verified as well as compatibility with each radial extension.

10. Supply the cell argument explicitly using the target circle geometry, instead of invoking
arbitrary Jordan/Schoenflies or the downstream source4(D). For any closed contact set A⊂S1 with
at least three distinct points, associate to every complementary circle arc its chord e and the
closed half-plane P_e containing A. Put Ω(A)=closedBall(0,1)∩⋂P_e. Disjoint gap arcs have
nonalternating endpoints; the elementary chord-line/circle intersection calculation therefore
gives pairwise disjoint open circular caps cut off on their gap sides. Their cap diameters tend
to0 along distinct gaps, by the endpoint disk bound. Thus only finitely many such caps meet any
compact subset of the open disk. Ω(A) is closed, bounded and convex and contains the
nondegenerate triangle on any three points of A, so its interior is nonempty. A circle point
belongs to Ω(A) exactly when it belongs to A. In the open disk its frontier consists exactly of
the open gap chords: local finiteness of the caps reduces each finite point to finitely many
half-plane inequalities, while their disjointness leaves both sides of each gap chord visible.
Accordingly frontierΩ(A) is A together with exactly those chords. For A=h(S_j), this is the
target frontier already proved above. The target filled set K_j is open, connected, nonempty and
has that frontier. It intersects interiorΩ(A): at the first stage the old base is an interior
diagonal because there are retained contacts on both sides; at later stages K1 is contained in
K_j and in interiorΩ(A), because contact sets only increase and each new gap lies in an old gap:
its circular cap is contained in that old gap cap (both are convex hulls of their respective
closed circle arcs), so the half-plane intersections Ω increase. The open interior of Ω(h(S₁))
is therefore contained in the interior of every later Ω. The sets interiorΩ(A) and
complementΩ(A) partition the plane outside their common frontier, so connectedness gives
K_j⊂interiorΩ(A). Since the frontier of K_j misses this connected convex interior, K_j is
relatively closed as well as open there, hence K_j=interiorΩ(A). The convex-body gauge leaf
makes K_j an open 2-cell, its closure a closed disk, and its frontier the displayed circle. H_j
restricts to a homeomorphism a_j→K_j, because it carries interiors to interiors and their
established frontiers correspond; therefore a_j is an open 2-cell as required. This is a
concrete proof of the 'easy to verify' cell clause in source4(C), not an added hypothesis about
the arbitrary source curve.

11. Prove density by Cairns Lemma4.1's perpendicular-bisector contradiction, now with the exact gap
recurrence established. If closure(⋃S_j) is not c, take one maximal open arc I of its
complement; its endpoints are distinct because all the retained sets contain the four initial
contacts. The decreasing stage gaps I_j containing I have endpoints tending to I's endpoints:
their intersection has interior disjoint from every S_j, and maximality of I rules out any
additional limiting open subarc. Denote the endpoint images P0,P0′. Take the two closed disks of
radius |P0−P0′|/3. For large j the endpoints D1,D2 of I_j are sufficiently close to P0,P0′, and
the extra portions of σ(I_j) outside σ(I) lie in these disks, by uniform continuity at the
limiting endpoints. The perpendicular bisector of D1D2 misses both disks: its limit bisector has
distance |P0−P0′|/2 from either center, leaving a positive margin. The next outer star retains
its first perpendicular contact P on σ(I_j). Since P lies on that bisector, it is outside the
endpoint disks, hence in σ(I). But it belongs to S_(j+1), a contradiction. Thus ⋃S_j is dense in
c.

12. Density implies uniform parameter mesh shrink, using the closed nested sets T_j. If gaps had
lengths≥δ>0 along j_k→∞, choose their arc-length midpoints and a convergent subsequence on the
compact parameter circle 𝕋. A fixed small interval about the limiting midpoint, of length less
thanδ/2, lies in all sufficiently late selected gaps. By nestedness T_j⊂T_(j+1), this interval
misses every T_j, contradicting density. The maximum gap length exists when there are gaps:
their positive lengths sum to at most1, and only finitely many exceed half of their positive
supremum, so the supremum is a maximum among those finitely many. With no gaps set it to0.
Uniform continuity of σ and h∘σ and the earlier convex-disk sector bound now make the source and
target residual-sector diameters tend uniformly to0. In particular the proof handles the finite-
termination case and asserts uniform smallness of existing sectors, not the false literal
existence quantifier of printed Lemma4.1.

13. Finally prove both exhaustions. If Q∈a missed every a_j, it cannot belong to any boundary chord
interior, because that old chord is included in a_(j+1). It also does not lie on c. The exact
complement partition therefore places Q in a residual sector at every stage. Such a sector has a
boundary endpoint on c, so dist(Q,c) is at most its closure diameter. Uniform shrinking would
give dist(Q,c)=0, impossible for Q∈a and closed c. Therefore ⋃a_j=a. The target argument is
identical, with S1 closed and every target old chord adjoined in the next stage: ⋃K_j=ball(0,1).
If the residual family becomes empty, the exact partition already gives a_j=a and K_j=ball(0,1),
and the stable recurrence satisfies all claims.

14. The target circular cap assigned to each residual gap contains the image of its full closed
parameter arc. Nested gap labels and convexity keep every descendant target star and chord inside
that cap. Induction on later stages therefore sends each old source residual sector's filled
points into the closure of its matching target sector; the induction starts vacuously from the
stage residual partition and uses the literal radial and affine formulas at each successor. This
is the source's §4(C) transport invariant and is exported as the two additional per-sector
conclusions below.
-/
theorem cairns_residual_chord_refinement_shrinking
    (σ : Circle → ℂ) (hσ : Topology.IsEmbedding σ)
    (a : Set ℂ) (ha : a.Nonempty) (haBounded : Bornology.IsBounded a)
    (haComponent : ∃ x ∈ a, connectedComponentIn (range σ)ᶜ x = a)
    (h : (range σ) ≃ₜ Circle) (p q : Circle) (hpq : p ≠ q)
    (hChord : openSegment ℝ (σ p) (σ q) ⊆ a) :
    let k := range (fun z : Circle ↦ (z : ℂ))
    let targetBoundary := fun t : Circle ↦ (h ⟨σ t, ⟨t, rfl⟩⟩ : ℂ)
    ∃ d : Data σ a p q h,
      let A := fun j ↦ (d.stages j).region
      let K := fun j ↦ (d.stages j).target
      let T := fun j ↦ (d.stages j).contacts σ
      let I := fun j ↦ ResidualComponent (T j)
      let gap := fun j (i : I j) ↦ (d.steps j).gap i
      let β := fun j (i : I j) ↦ ((d.steps j).star i).sector
    have _hmeshEmpty : ∀ j, (¬ ∃ g : CairnsCircleGap, g.IsGapOf (T j)) →
        CairnsCircleGap.mesh (T j) = 0 :=
      fun _j hj ↦ cairns_gap_mesh_eq_zero_of_no_gap hj
      ∃ βt : ∀ j, I j → Set ℂ,
        (∀ j, (A j).Nonempty ∧ IsOpen (A j) ∧ A j ⊆ a ∧
          Nonempty ((A j) ≃ₜ Metric.ball (0 : ℂ) 1) ∧
          (K j).Nonempty ∧ IsOpen (K j) ∧ K j ⊆ Metric.ball (0 : ℂ) 1) ∧
        Monotone A ∧ Monotone K ∧ Monotone T ∧
        (∀ j, IsClosed (T j) ∧
          ∃ t₁ t₂ t₃ t₄ : Circle, t₁ ∈ T j ∧ t₂ ∈ T j ∧ t₃ ∈ T j ∧ t₄ ∈ T j ∧
            t₁ ≠ t₂ ∧ t₁ ≠ t₃ ∧ t₁ ≠ t₄ ∧ t₂ ≠ t₃ ∧ t₂ ≠ t₄ ∧ t₃ ≠ t₄) ∧
        Dense (⋃ j, T j) ∧ closure (⋃ j, σ '' T j) = range σ ∧
        (∀ j, Set.Countable {U : Set Circle |
          ∃ x ∈ (T j)ᶜ, connectedComponentIn (T j)ᶜ x = U}) ∧
        (∀ j, Nonempty (Circle ≃ₜ frontier (A j)) ∧
          frontier (A j) = σ '' T j ∪
            ⋃ i : I j, openSegment ℝ (σ (gap j i).first) (σ (gap j i).last) ∧
          frontier (K j) = targetBoundary '' T j ∪
            ⋃ i : I j, openSegment ℝ (targetBoundary (gap j i).first)
              (targetBoundary (gap j i).last)) ∧
        (∀ j, ∃ H : ↥(closure (A j) ∪ range σ) ≃ₜ ↥(closure (K j) ∪ k),
          (∀ x, (H x : ℂ) = (d.stages j).map x) ∧
          (∀ (x : ↥(closure (A j) ∪ range σ)) (hx : (x : ℂ) ∈ range σ),
            (H x : ℂ) = (h ⟨x, hx⟩ : ℂ))) ∧
        (∀ j z, z ∈ closure (A j) ∪ range σ →
          (d.stages (j + 1)).map z = (d.stages j).map z) ∧
        (∀ j (i : I j) (t : CairnsStar.I),
          (d.stages j).map ((1 - (t : ℝ)) • σ (gap j i).first +
            (t : ℝ) • σ (gap j i).last) =
          (1 - (t : ℝ)) • targetBoundary (gap j i).first +
            (t : ℝ) • targetBoundary (gap j i).last) ∧
        (∀ j, T (j + 1) = T j ∪
          ⋃ i : I j, σ ⁻¹' (((d.steps j).star i).front ∩ range σ)) ∧
        (∀ j, K (j + 1) = K j ∪
          ⋃ i : I j, (((d.steps j).star i).targetStar h ∪
            openSegment ℝ (targetBoundary (gap j i).first)
              (targetBoundary (gap j i).last))) ∧
        (∀ j, a \ closure (A j) = ⋃ i : I j, β j i) ∧
        (∀ j, Metric.ball (0 : ℂ) 1 \ closure (K j) = ⋃ i : I j, βt j i) ∧
        (∀ j, Pairwise (fun i i' : I j ↦ Disjoint (β j i) (β j i')) ∧
          Pairwise (fun i i' : I j ↦ Disjoint (βt j i) (βt j i'))) ∧
        (∀ j (i : I j),
          (β j i).Nonempty ∧ IsOpen (β j i) ∧ IsConnected (β j i) ∧
          (∃ x ∈ a \ closure (A j),
            connectedComponentIn (a \ closure (A j)) x = β j i) ∧
          frontier (β j i) ⊆ segment ℝ (σ (gap j i).first) (σ (gap j i).last) ∪
            σ '' (gap j i).closedArc ∧
          (∀ z r, σ '' (gap j i).closedArc ⊆ Metric.closedBall z r →
            closure (β j i) ⊆ Metric.closedBall z r) ∧
          (βt j i).Nonempty ∧ IsOpen (βt j i) ∧ IsConnected (βt j i) ∧
          (∃ x ∈ Metric.ball (0 : ℂ) 1 \ closure (K j),
            connectedComponentIn (Metric.ball (0 : ℂ) 1 \ closure (K j)) x = βt j i) ∧
          frontier (βt j i) ⊆
            segment ℝ (targetBoundary (gap j i).first) (targetBoundary (gap j i).last) ∪
              targetBoundary '' (gap j i).closedArc ∧
          (∀ z r, targetBoundary '' (gap j i).closedArc ⊆ Metric.closedBall z r →
            closure (βt j i) ⊆ Metric.closedBall z r) ∧
          targetBoundary '' (gap j i).closedArc ⊆ closure (βt j i) ∧
          (∀ n : ℕ, j ≤ n →
            MapsTo (d.stages n).map (A n ∩ β j i) (closure (βt j i)))) ∧
        (∀ j, (¬ ∃ g : CairnsCircleGap, g.IsGapOf (T j)) →
          CairnsCircleGap.mesh (T j) = 0) ∧
        (∀ j, (∃ g : CairnsCircleGap, g.IsGapOf (T j)) →
          ∃ g : CairnsCircleGap, g.IsGapOf (T j) ∧
            g.normalizedLength = CairnsCircleGap.mesh (T j)) ∧
        Filter.Tendsto (fun j ↦ CairnsCircleGap.mesh (T j)) Filter.atTop (nhds 0) ∧
        (∀ ε > 0, ∃ J : ℕ, ∀ j ≥ J, ∀ i : I j,
          Metric.diam (closure (β j i)) < ε ∧ Metric.diam (closure (βt j i)) < ε) ∧
        (⋃ j, A j) = a ∧ (⋃ j, K j) = Metric.ball (0 : ℂ) 1 := by
  classical
  let k := range (fun z : Circle ↦ (z : ℂ))
  let targetBoundary := fun t : Circle ↦ (h ⟨σ t, ⟨t, rfl⟩⟩ : ℂ)
  suffices hgeometry :
    let k := range (fun z : Circle ↦ (z : ℂ))
    let targetBoundary := fun t : Circle ↦ (h ⟨σ t, ⟨t, rfl⟩⟩ : ℂ)
    ∃ d : Data σ a p q h,
      let A := fun j ↦ (d.stages j).region
      let K := fun j ↦ (d.stages j).target
      let T := fun j ↦ (d.stages j).contacts σ
      let I := fun j ↦ ResidualComponent (T j)
      let gap := fun j (i : I j) ↦ (d.steps j).gap i
      let β := fun j (i : I j) ↦ ((d.steps j).star i).sector
      ∃ βt : ∀ j, I j → Set ℂ,
        (∀ j, (A j).Nonempty ∧ IsOpen (A j) ∧ A j ⊆ a ∧
          Nonempty ((A j) ≃ₜ Metric.ball (0 : ℂ) 1) ∧
          (K j).Nonempty ∧ IsOpen (K j) ∧ K j ⊆ Metric.ball (0 : ℂ) 1) ∧
        Monotone A ∧ Monotone K ∧ Monotone T ∧
        (∀ j, IsClosed (T j) ∧
          ∃ t₁ t₂ t₃ t₄ : Circle, t₁ ∈ T j ∧ t₂ ∈ T j ∧ t₃ ∈ T j ∧ t₄ ∈ T j ∧
            t₁ ≠ t₂ ∧ t₁ ≠ t₃ ∧ t₁ ≠ t₄ ∧ t₂ ≠ t₃ ∧ t₂ ≠ t₄ ∧ t₃ ≠ t₄) ∧
        Dense (⋃ j, T j) ∧ closure (⋃ j, σ '' T j) = range σ ∧
        (∀ j, Set.Countable {U : Set Circle |
          ∃ x ∈ (T j)ᶜ, connectedComponentIn (T j)ᶜ x = U}) ∧
        (∀ j, Nonempty (Circle ≃ₜ frontier (A j)) ∧
          frontier (A j) = σ '' T j ∪
            ⋃ i : I j, openSegment ℝ (σ (gap j i).first) (σ (gap j i).last) ∧
          frontier (K j) = targetBoundary '' T j ∪
            ⋃ i : I j, openSegment ℝ (targetBoundary (gap j i).first)
              (targetBoundary (gap j i).last)) ∧
        (∀ j, ∃ H : ↥(closure (A j) ∪ range σ) ≃ₜ ↥(closure (K j) ∪ k),
          (∀ x, (H x : ℂ) = (d.stages j).map x) ∧
          (∀ (x : ↥(closure (A j) ∪ range σ)) (hx : (x : ℂ) ∈ range σ),
            (H x : ℂ) = (h ⟨x, hx⟩ : ℂ))) ∧
        (∀ j z, z ∈ closure (A j) ∪ range σ →
          (d.stages (j + 1)).map z = (d.stages j).map z) ∧
        (∀ j (i : I j) (t : CairnsStar.I),
          (d.stages j).map ((1 - (t : ℝ)) • σ (gap j i).first +
            (t : ℝ) • σ (gap j i).last) =
          (1 - (t : ℝ)) • targetBoundary (gap j i).first +
            (t : ℝ) • targetBoundary (gap j i).last) ∧
        (∀ j, T (j + 1) = T j ∪
          ⋃ i : I j, σ ⁻¹' (((d.steps j).star i).front ∩ range σ)) ∧
        (∀ j, K (j + 1) = K j ∪
          ⋃ i : I j, (((d.steps j).star i).targetStar h ∪
            openSegment ℝ (targetBoundary (gap j i).first)
              (targetBoundary (gap j i).last))) ∧
        (∀ j, a \ closure (A j) = ⋃ i : I j, β j i) ∧
        (∀ j, Metric.ball (0 : ℂ) 1 \ closure (K j) = ⋃ i : I j, βt j i) ∧
        (∀ j, Pairwise (fun i i' : I j ↦ Disjoint (β j i) (β j i')) ∧
          Pairwise (fun i i' : I j ↦ Disjoint (βt j i) (βt j i'))) ∧
        (∀ j (i : I j),
          (β j i).Nonempty ∧ IsOpen (β j i) ∧ IsConnected (β j i) ∧
          (∃ x ∈ a \ closure (A j),
            connectedComponentIn (a \ closure (A j)) x = β j i) ∧
          frontier (β j i) ⊆ segment ℝ (σ (gap j i).first) (σ (gap j i).last) ∪
            σ '' (gap j i).closedArc ∧
          (∀ z r, σ '' (gap j i).closedArc ⊆ Metric.closedBall z r →
            closure (β j i) ⊆ Metric.closedBall z r) ∧
          (βt j i).Nonempty ∧ IsOpen (βt j i) ∧ IsConnected (βt j i) ∧
          (∃ x ∈ Metric.ball (0 : ℂ) 1 \ closure (K j),
            connectedComponentIn (Metric.ball (0 : ℂ) 1 \ closure (K j)) x = βt j i) ∧
          frontier (βt j i) ⊆
            segment ℝ (targetBoundary (gap j i).first) (targetBoundary (gap j i).last) ∪
              targetBoundary '' (gap j i).closedArc ∧
          (∀ z r, targetBoundary '' (gap j i).closedArc ⊆ Metric.closedBall z r →
            closure (βt j i) ⊆ Metric.closedBall z r) ∧
          targetBoundary '' (gap j i).closedArc ⊆ closure (βt j i) ∧
          (∀ n : ℕ, j ≤ n →
            MapsTo (d.stages n).map (A n ∩ β j i) (closure (βt j i)))) ∧
        (∀ j, (¬ ∃ g : CairnsCircleGap, g.IsGapOf (T j)) →
          CairnsCircleGap.mesh (T j) = 0) ∧
        (∀ j, (∃ g : CairnsCircleGap, g.IsGapOf (T j)) →
          ∃ g : CairnsCircleGap, g.IsGapOf (T j) ∧
            g.normalizedLength = CairnsCircleGap.mesh (T j)) ∧
        Filter.Tendsto (fun j ↦ CairnsCircleGap.mesh (T j)) Filter.atTop (nhds 0) ∧
        (∀ ε > 0, ∃ J : ℕ, ∀ j ≥ J, ∀ i : I j,
          Metric.diam (closure (β j i)) < ε ∧ Metric.diam (closure (βt j i)) < ε) ∧
        (∀ j (i : I j), (closure (β j i) ∩ range σ).Nonempty ∧
          (closure (βt j i) ∩ k).Nonempty) by
    rcases hgeometry with ⟨d, βt, hs, hA, hK, hT, hc, hd, hcl, hcount, hfront,
      hhomeo, hcompat, haff, hcontacts, htarget, hsourcePart, htargetPart, hdisjoint,
      hsectors, hempty, hmax, hmesh, hsmall, hboundary⟩
    let A := fun j ↦ (d.stages j).region
    let K := fun j ↦ (d.stages j).target
    let T := fun j ↦ (d.stages j).contacts σ
    let I := fun j ↦ ResidualComponent (T j)
    let β := fun j (i : I j) ↦ ((d.steps j).star i).sector
    have hsep : Disjoint a (range σ) := by
      obtain ⟨x, _, hx⟩ := haComponent
      apply Set.disjoint_left.mpr
      intro z hz hzσ
      exact (connectedComponentIn_subset (range σ)ᶜ x (hx.symm ▸ hz)) hzσ
    have hsource : (⋃ j, A j) = a := by
      apply cairns_shrinking_residual_exhaustion a (range σ) A β
        (fun j ↦ (hs j).2.2.1) hsep (isCompact_range hσ.continuous).isClosed
      · intro j
        rw [hsourcePart j]
      · intro j z hz
        rw [(hfront j).2.1] at hz
        rcases hz with hz | hz
        · exact Or.inl (image_subset_range _ _ hz)
        · obtain ⟨i, hi⟩ := mem_iUnion.mp hz
          right
          change z ∈ (d.stages (j + 1)).region
          rw [d.next_eq j]
          exact Or.inr (mem_iUnion.mpr ⟨i, Or.inr hi⟩)
      · exact fun j i ↦ (hboundary j i).1
      · intro j i
        apply haBounded.subset
        intro z hz
        have hmem : z ∈ a \ closure (A j) := by
          rw [hsourcePart j]
          exact mem_iUnion.mpr ⟨i, hz⟩
        exact hmem.1
      · intro ε hε
        obtain ⟨J, hJ⟩ := hsmall ε hε
        exact ⟨J, fun j hj i ↦ (hJ j hj i).1⟩
    have htargetSep : Disjoint (Metric.ball (0 : ℂ) 1) k := by
      apply Set.disjoint_left.mpr
      intro z hz hzK
      obtain ⟨t, rfl⟩ := hzK
      simp at hz
    have htargetExhaust : (⋃ j, K j) = Metric.ball (0 : ℂ) 1 := by
      apply cairns_shrinking_residual_exhaustion (Metric.ball (0 : ℂ) 1) k K βt
        (fun j ↦ (hs j).2.2.2.2.2.2) htargetSep
        (isCompact_range (show Continuous (fun z : Circle ↦ (z : ℂ)) from
          continuous_subtype_val)).isClosed
      · intro j
        rw [htargetPart j]
      · intro j z hz
        rw [(hfront j).2.2] at hz
        rcases hz with hz | hz
        · obtain ⟨t, _, rfl⟩ := hz
          exact Or.inl ⟨h ⟨σ t, ⟨t, rfl⟩⟩, rfl⟩
        · obtain ⟨i, hi⟩ := mem_iUnion.mp hz
          right
          change z ∈ (d.stages (j + 1)).target
          exact (congrArg (fun S : Set ℂ ↦ z ∈ S) (htarget j)).mpr
            (Or.inr (mem_iUnion.mpr ⟨i, Or.inr hi⟩))
      · exact fun j i ↦ (hboundary j i).2
      · intro j i
        apply Metric.isBounded_ball.subset
        intro z hz
        have hmem : z ∈ Metric.ball (0 : ℂ) 1 \ closure (K j) := by
          rw [htargetPart j]
          exact mem_iUnion.mpr ⟨i, hz⟩
        exact hmem.1
      · intro ε hε
        obtain ⟨J, hJ⟩ := hsmall ε hε
        exact ⟨J, fun j hj i ↦ (hJ j hj i).2⟩
    exact ⟨d, βt, hs, hA, hK, hT, hc, hd, hcl, hcount, hfront, hhomeo, hcompat,
      haff, hcontacts, htarget, hsourcePart, htargetPart, hdisjoint, hsectors, hempty,
      hmax, hmesh, hsmall, hsource, htargetExhaust⟩
  exact cairns_residual_chord_refinement_data σ hσ a ha haBounded haComponent h p q hpq hChord

end HolomorphicAnosov.Topology.Plane
