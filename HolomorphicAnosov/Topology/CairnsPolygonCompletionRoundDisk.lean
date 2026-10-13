import HolomorphicAnosov.Topology.CircleComplementRegions
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.LocallyConvex.WithSeminorms
import HolomorphicAnosov.Topology.OpenConnectedSegmentChain
import Mathlib.Topology.Connected.LocallyConnected
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Analysis.Complex.Basic
import Mathlib.Geometry.Polygon.Basic
import Mathlib.Topology.Connected.Basic
import HolomorphicAnosov.Topology.CairnsRoundDiskTwoWalkPolygonProvider

/-!
# Controlled polygon completion across the round disk

DAG node: `topo.cairns_polygon_completion_across_round_disk`.
Source: Stewart S. Cairns, *An Elementary Proof of the Jordan-Schoenflies Theorem*,
Proceedings AMS 2 (1951), 860–867, Lemma 5.1, printed p.866 (PDF p.8),
`literature/cairns-jordan-schoenflies-1951.pdf`.

Cairns asserts completion outside the circle but omits the controlled finite construction.
The node's proof is honestly agent-written; its three proof steps are reproduced below.
Mathlib's `Polygon` supplies a cyclic vertex array and actual affine segment edges.
Simplicity is expressed by injective vertices and exact pairwise edge intersections:
two different edges meet precisely in their common endpoint set. No new polygon
predicate or circle-arc definition is introduced.

The plane is `ℂ` as a real normed vector space. The two open circle arcs are connected
components of the unit circle minus the marked points. Taking the ambient closure of
the component containing `a` gives the closed circle arc in the last conclusion.
The coordinate dot product with the circle contact is the normal component of an edge;
its nonvanishing expresses transversality. No Jordan separation premise or conclusion
is included in this construction theorem.
-/

open Set

namespace HolomorphicAnosov

/-- Complete the interior collar connector to a simple closed polygon missing the compact
obstacle, with exactly the prescribed two transverse radial circle contacts.

Source scope: Cairns 1951, Lemma 5.1, printed p.866 (PDF p.8), asserts exterior completion.
The following full natural-language proof is the existing agent construction in the DAG,
not a claim that Cairns writes its finite subdivision or radial-contact controls.
Its non-elementary inputs are the public open-set segment-chain and standard circle-region
providers and Mathlib's abstract edge-preserving loop erasure,
`SimpleGraph.Walk.edges_toPath_subset`, recorded by the node's named suppliers.

Natural-language proof:
Every component of an open plane set is open and polygonally connected. Here is the direct
argument needed: from a fixed point define R as points reached by finitely many straight segments
staying in the open set. A small convex ball around any point of R extends its chain, so R is
open. A small ball around any point outside R cannot meet R, since its segments would then extend
a chain to that point, so its relative complement is open. Connectedness of the component forces R
to be all of it. The same ball argument shows the component is open, since every small ball is
connected and hence belongs to the component of its center. Apply this to connect the two
specified collar points by finitely many segments in the open disk minus K.

Append the two radial collar segments to obtain a finite segment chain from a to b, meeting S1
only at its endpoints and missing K. Subdivide all finitely many segments at their endpoints and
pairwise intersection points; for collinear overlaps add the finitely many overlap endpoints and
retain each geometric subsegment only once. Distinct open subedges are then disjoint. The
resulting finite embedded graph contains an a-to-b walk. Let p be this a-to-b walk in the finite
embedded simple graph G; its vertex type admits decidable equality. Apply
mathlib.simpleGraph_walk_toPath_edges_subset_g10, with its supporting definition Walk.toPath, to
obtain the path p.toPath from a to b whose edges are a subset of p.edges. As a G.Path it is
vertex-simple. Thus this step uses only edges of the already subdivided segment union. Its
geometric realization is a simple polygonal arc q. All retained segments belonged to the original
union, so q remains in the disk away from its endpoints and disjoint from K. The polygonal chain
and appended stubs have positive distance from a and b except on the relevant final radial
subedge: trim each stub below the smallest positive distance of the finite connector from its
endpoint before subdivision if necessary. Consequently the first and last retained edges of q are
radial. This is finite graph loop removal, not uncontrolled approximation of K.

The exterior of the closed unit disk is connected and open by the standard circle-region
provider. Join 2a to 2b there by a finite segment chain using the same polygonal-connectivity
provider as above, then dilate that chain by two. The resulting chain joins 4a to 4b outside
the closed radius-two disk, so all its edges miss the radius-one-half balls around a and b.
The outward radial segment [z,4z], for z=a or b, meets the closed unit disk
only at z: a point has the form (s+4t)z with s,t≥0 and s+t=1, and norm≤1 forces t=0.
Consequently these two radial segments miss K, since z is not u or v. For each contact z, choose epsilon as half the minimum of its inner-connector clearance,
the two inward collar parameters, and one half. The radial segment from (1-epsilon)z to
(1+epsilon)z contains z in its open interior and lies in its radius-epsilon ball by convexity.
It therefore misses both the inner connector and every edge of the dilated exterior chain.
Apply the finite subdivision and loop-erasure construction of the
preceding paragraph to get an exterior simple polygonal arc retaining its radial endpoint
segments. Its union with the interior simple polygonal arc is a simple closed polygon, since
the two arcs lie on opposite sides of the circle away from their endpoints. At a and b merge
the collinear inner and outer radial subedges, placing both contacts strictly inside edges.
All other edges stay strictly inside or outside the unit circle. The radial direction has
nonzero normal component at the circle, proving transversality. The resulting polygon misses K.
The last circle-arc assertion follows from a,b lying in different u-v arcs.

Formal conventions: `finRotate n` closes the last edge back to the first vertex.
The edge-intersection equalities and distinct vertices are an explicit simple closed
polygon condition; collinear redundant vertices are permitted. Repeating a contact's
edge index is permitted if both contacts happen to lie in one edge. The collar points
are actual points with positive collar parameters less than one, and the closed collar
segments miss `K`. The second collar point lies in the connected component of the first
in the open disk minus `K`. All of these are input data, not separation assumptions.
-/
theorem cairns_polygon_completion_across_round_disk
    (K : Set ℂ) (hK : IsCompact K) (hKdisk : K ⊆ Metric.closedBall (0 : ℂ) 1)
    (u v a b : ℂ) (hu : u ∈ Metric.sphere (0 : ℂ) 1)
    (hv : v ∈ Metric.sphere (0 : ℂ) 1) (huv : u ≠ v)
    (hKcircle : K ∩ Metric.sphere (0 : ℂ) 1 = {u, v})
    (ha : a ∈ Metric.sphere (0 : ℂ) 1 \ {u, v})
    (hb : b ∈ Metric.sphere (0 : ℂ) 1 \ {u, v})
    (harcs : b ∉ connectedComponentIn (Metric.sphere (0 : ℂ) 1 \ {u, v}) a)
    (eta_a eta_b : ℝ) (heta_a : 0 < eta_a ∧ eta_a < 1)
    (heta_b : 0 < eta_b ∧ eta_b < 1)
    (hcollar_a : Disjoint (segment ℝ a ((1 - eta_a) • a)) K)
    (hcollar_b : Disjoint (segment ℝ b ((1 - eta_b) • b)) K)
    (hcomponent : (1 - eta_b) • b ∈
      connectedComponentIn (Metric.ball (0 : ℂ) 1 \ K) ((1 - eta_a) • a)) :
    ∃ (n : ℕ) (P : Polygon ℂ n),
      3 ≤ n ∧ Function.Injective P.vertices ∧ P.HasNondegenerateEdges ∧
      (∀ i j : Fin n, i ≠ j →
        P.edgeSet ℝ i ∩ P.edgeSet ℝ j =
          ({P i, P (finRotate n i)} ∩ {P j, P (finRotate n j)})) ∧
      Disjoint (P.boundary ℝ) K ∧
      P.boundary ℝ ∩ Metric.sphere (0 : ℂ) 1 = {a, b} ∧
      (∀ z ∈ ({a, b} : Set ℂ), ∃ (i : Fin n) (r s : ℝ),
        P i = r • z ∧ P (finRotate n i) = s • z ∧
        z ∈ openSegment ℝ (P i) (P (finRotate n i)) ∧
        (P (finRotate n i) - P i).re * z.re +
          (P (finRotate n i) - P i).im * z.im ≠ 0) ∧
      closure (connectedComponentIn (Metric.sphere (0 : ℂ) 1 \ {u, v}) a) ∩
        P.boundary ℝ = {a} := by
  classical
  have hab : a ≠ b := by
    rintro rfl
    exact harcs (mem_connectedComponentIn ha)
  have hanorm : ‖a‖ = 1 := by
    simpa [Metric.mem_sphere, dist_zero_right] using ha.1
  have hacollar : (1 - eta_a) • a ∈ Metric.ball (0 : ℂ) 1 \ K := by
    constructor
    · rw [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs,
        abs_of_pos (sub_pos.mpr heta_a.2), hanorm, mul_one]
      exact sub_lt_self _ heta_a.1
    · intro hbad
      exact Set.disjoint_left.mp hcollar_a (right_mem_segment ℝ a _) hbad
  have hopen : IsOpen (Metric.ball (0 : ℂ) 1 \ K) :=
    Metric.isOpen_ball.sdiff hK.isClosed
  have hconnector := open_preconnected_segment_chain hopen.connectedComponentIn
    (isConnected_connectedComponentIn_iff.mpr hacollar).isPreconnected
    (mem_connectedComponentIn hacollar) hcomponent
  -- Record an actual compact union of segments, so both radial collars can be shortened
  -- before the finite graph construction. The connector itself stays strictly inside the disk.
  have hfinite : ∀ y : ℂ,
      Relation.ReflTransGen
        (fun p q ↦ segment ℝ p q ⊆
          connectedComponentIn (Metric.ball (0 : ℂ) 1 \ K) ((1 - eta_a) • a))
        ((1 - eta_a) • a) y →
      ∃ S : Finset (ℂ × ℂ),
        Relation.ReflTransGen (fun p q ↦ (p, q) ∈ S) ((1 - eta_a) • a) y ∧
        (1 - eta_a) • a ∈ ⋃ q ∈ S, segment ℝ q.1 q.2 ∧
        y ∈ ⋃ q ∈ S, segment ℝ q.1 q.2 ∧
        (⋃ q ∈ S, segment ℝ q.1 q.2) ⊆ Metric.ball (0 : ℂ) 1 \ K := by
    intro y hchain
    induction hchain with
    | refl =>
      refine ⟨{((1 - eta_a) • a, (1 - eta_a) • a)}, .refl, ?_, ?_, ?_⟩
      · simp
      · simp
      · simpa using singleton_subset_iff.mpr hacollar
    | @tail p q hprev hpq ih =>
      obtain ⟨S, hwalk, hstart, hend, hS⟩ := ih
      refine ⟨insert (p, q) S, ?_, ?_, ?_, ?_⟩
      · exact (Relation.ReflTransGen.mono
          (fun _ _ h ↦ Finset.mem_insert_of_mem h) _ _ hwalk).tail
            (Finset.mem_insert_self _ _)
      · simp only [Finset.mem_insert, iUnion_iUnion_eq_or_left]
        exact Or.inr hstart
      · simp only [Finset.mem_insert, iUnion_iUnion_eq_or_left]
        exact Or.inl (right_mem_segment ℝ p q)
      · intro z hz
        simp only [Finset.mem_insert, iUnion_iUnion_eq_or_left, mem_union] at hz
        exact hz.elim (fun hz ↦ connectedComponentIn_subset _ _ (hpq hz)) (fun hz ↦ hS hz)
  obtain ⟨S, hSwalk, hSa, hSb, hSdisk⟩ := hfinite _ hconnector
  have hScompact : IsCompact (⋃ q ∈ S, segment ℝ q.1 q.2) := by
    apply S.finite_toSet.isCompact_biUnion
    intro q _
    rw [← convexHull_pair]
    exact ((Set.finite_singleton q.2).insert q.1).isCompact_convexHull ℝ
  have hclearance : ∀ z ∈ ({a, b} : Set ℂ), ∃ δ : ℝ,
      0 < δ ∧ Metric.closedBall z δ ⊆ (⋃ q ∈ S, segment ℝ q.1 q.2)ᶜ := by
    intro z hz
    have hznorm : ‖z‖ = 1 := by
      rcases hz with rfl | rfl
      · exact hanorm
      · simpa [Metric.mem_sphere, dist_zero_right] using hb.1
    have hzavoid : z ∉ ⋃ q ∈ S, segment ℝ q.1 q.2 := by
      intro hzS
      have hzball := (hSdisk hzS).1
      simp [Metric.mem_ball, dist_zero_right, hznorm] at hzball
    exact Metric.nhds_basis_closedBall.mem_iff.mp
      (hScompact.isClosed.isOpen_compl.mem_nhds hzavoid)
  -- The existing circle-region theorem supplies the exterior connector directly.
  obtain ⟨_, hEconnected, _, hEopen, _⟩ := circle_complement_regions
  have hdouble (z : ℂ) (hz : z ∈ ({a, b} : Set ℂ)) :
      (2 : ℝ) • z ∈ (Metric.closedBall (0 : ℂ) 1)ᶜ := by
    have hznorm : ‖z‖ = 1 := by
      rcases hz with rfl | rfl
      · exact hanorm
      · simpa [Metric.mem_sphere, dist_zero_right] using hb.1
    norm_num [Metric.mem_closedBall, dist_zero_right, norm_smul, hznorm]
  have hexterior := open_preconnected_segment_chain hEopen hEconnected.isPreconnected
    (hdouble a (by simp)) (hdouble b (by simp))
  -- Dilation gives a uniform exterior margin, without a separate compactness argument.
  have hexterior_far : Relation.ReflTransGen
      (fun p q : ℂ ↦ segment ℝ p q ⊆ (Metric.closedBall (0 : ℂ) 2)ᶜ)
      ((4 : ℝ) • a) ((4 : ℝ) • b) := by
    have hscaled := hexterior.lift (p := fun p q : ℂ ↦
      segment ℝ p q ⊆ (Metric.closedBall (0 : ℂ) 2)ᶜ) (fun z : ℂ ↦ (2 : ℝ) • z) (by
      intro p q hpq y hy
      obtain ⟨s, t, hs, ht, hst, rfl⟩ := hy
      have hmem : s • p + t • q ∈ segment ℝ p q := ⟨s, t, hs, ht, hst, rfl⟩
      have hnorm : 1 < ‖s • p + t • q‖ := by
        simpa only [Metric.mem_closedBall, dist_zero_right, Set.mem_compl_iff, not_le]
          using hpq hmem
      have heq : s • ((2 : ℝ) • p) + t • ((2 : ℝ) • q) =
          (2 : ℝ) • (s • p + t • q) := by
        simp only [smul_add, smul_smul, mul_comm]
      change s • ((2 : ℝ) • p) + t • ((2 : ℝ) • q) ∉ Metric.closedBall (0 : ℂ) 2
      rw [Metric.mem_closedBall, dist_zero_right, heq, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      intro hh
      linarith)
    simpa only [Function.onFun, smul_smul, show (2 : ℝ) * 2 = 4 by norm_num] using hscaled
  have hfar_clearance : ∀ p q : ℂ,
      segment ℝ p q ⊆ (Metric.closedBall (0 : ℂ) 2)ᶜ →
      ∀ z ∈ ({a, b} : Set ℂ),
        Disjoint (segment ℝ p q) (Metric.closedBall z (1 / 2 : ℝ)) := by
    intro p q hpq z hz
    have hznorm : ‖z‖ = 1 := by
      rcases hz with rfl | rfl
      · exact hanorm
      · simpa [Metric.mem_sphere, dist_zero_right] using hb.1
    apply Set.disjoint_left.mpr
    intro y hy hyz
    have hynorm : 2 < ‖y‖ := by
      simpa only [Metric.mem_closedBall, dist_zero_right, Set.mem_compl_iff, not_le]
        using hpq hy
    have hydist : ‖y - z‖ ≤ 1 / 2 := by
      simpa only [Metric.mem_closedBall, dist_eq_norm] using hyz
    have htriangle := norm_add_le (y - z) z
    rw [sub_add_cancel, hznorm] at htriangle
    linarith
  have houtercontact : ∀ z ∈ ({a, b} : Set ℂ),
      segment ℝ z ((4 : ℝ) • z) ∩ Metric.closedBall (0 : ℂ) 1 = {z} := by
    intro z hz
    have hzsphere : z ∈ Metric.sphere (0 : ℂ) 1 := by
      rcases hz with rfl | rfl
      · exact ha.1
      · exact hb.1
    have hznorm : ‖z‖ = 1 := by
      simpa [Metric.mem_sphere, dist_zero_right] using hzsphere
    apply subset_antisymm
    · rintro y ⟨⟨s, t, hs, ht, hst, rfl⟩, hy⟩
      have hcoeff : 0 ≤ s + t * 4 := by positivity
      have hnorm : ‖s • z + t • ((4 : ℝ) • z)‖ = s + t * 4 := by
        rw [smul_smul, ← add_smul, norm_smul, Real.norm_eq_abs,
          abs_of_nonneg hcoeff, hznorm, mul_one]
      have hle : s + t * 4 ≤ 1 := by
        simpa only [Metric.mem_closedBall, dist_zero_right, hnorm] using hy
      have htzero : t = 0 := by linarith
      subst t
      have hsone : s = 1 := by simpa using hst
      simp [hsone]
    · rintro y (rfl : y = z)
      exact ⟨left_mem_segment ℝ _ _, Metric.sphere_subset_closedBall hzsphere⟩
  have houteravoid : ∀ z ∈ ({a, b} : Set ℂ),
      Disjoint (segment ℝ z ((4 : ℝ) • z)) K := by
    intro z hz
    apply Set.disjoint_left.mpr
    intro y hy hyK
    have hyz : y = z := (houtercontact z hz).subset ⟨hy, hKdisk hyK⟩
    subst y
    have hzsphere : z ∈ Metric.sphere (0 : ℂ) 1 := by
      rcases hz with rfl | rfl
      · exact ha.1
      · exact hb.1
    have hzuv : z ∈ ({u, v} : Set ℂ) := hKcircle.subset ⟨hyK, hzsphere⟩
    rcases hz with rfl | rfl
    · exact ha.2 hzuv
    · exact hb.2 hzuv
  have hprotected_crossing : ∀ z ∈ ({a, b} : Set ℂ), ∃ ε : ℝ,
      0 < ε ∧ ε < eta_a ∧ ε < eta_b ∧ ε < 1 / 2 ∧
      z ∈ openSegment ℝ ((1 - ε) • z) ((1 + ε) • z) ∧
      Disjoint (segment ℝ ((1 - ε) • z) ((1 + ε) • z))
        (⋃ q ∈ S, segment ℝ q.1 q.2) ∧
      ∀ p q : ℂ, segment ℝ p q ⊆ (Metric.closedBall (0 : ℂ) 2)ᶜ →
        Disjoint (segment ℝ ((1 - ε) • z) ((1 + ε) • z)) (segment ℝ p q) := by
    intro z hz
    obtain ⟨δ, hδ, hδavoid⟩ := hclearance z hz
    let m : ℝ := min δ (min eta_a (min eta_b (1 / 2)))
    have hm : 0 < m := lt_min hδ (lt_min heta_a.1 (lt_min heta_b.1 (by norm_num)))
    have hmδ : m ≤ δ := min_le_left _ _
    have hma : m ≤ eta_a := (min_le_right _ _).trans (min_le_left _ _)
    have hmb : m ≤ eta_b :=
      ((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_left _ _)
    have hmh : m ≤ 1 / 2 :=
      ((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_right _ _)
    let ε := m / 2
    have he : 0 < ε := half_pos hm
    have hem : ε < m := half_lt_self hm
    have heδ : ε ≤ δ := hem.le.trans hmδ
    have heh : ε ≤ 1 / 2 := hem.le.trans hmh
    have hznorm : ‖z‖ = 1 := by
      rcases hz with rfl | rfl
      · exact hanorm
      · simpa [Metric.mem_sphere, dist_zero_right] using hb.1
    have hpoint (t : ℝ) (ht : |t - 1| ≤ ε) : t • z ∈ Metric.closedBall z ε := by
      rw [Metric.mem_closedBall, dist_eq_norm,
        show t • z - z = (t - 1) • z by rw [sub_smul, one_smul],
        norm_smul, Real.norm_eq_abs, hznorm, mul_one]
      exact ht
    have hseg : segment ℝ ((1 - ε) • z) ((1 + ε) • z) ⊆
        Metric.closedBall z ε := by
      apply (convex_closedBall z ε).segment_subset
      · apply hpoint
        rw [sub_sub_cancel_left, abs_neg, abs_of_pos he]
      · apply hpoint
        rw [add_sub_cancel_left, abs_of_pos he]
    refine ⟨ε, he, hem.trans_le hma, hem.trans_le hmb, hem.trans_le hmh, ?_, ?_, ?_⟩
    · refine ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, ?_⟩
      rw [smul_smul, smul_smul, ← add_smul,
        show (1 / 2 : ℝ) * (1 - ε) + (1 / 2) * (1 + ε) = 1 by ring, one_smul]
    · apply Set.disjoint_left.mpr
      intro y hy hyS
      exact hδavoid (Metric.closedBall_subset_closedBall heδ (hseg hy)) hyS
    · intro p q hpq
      exact ((hfar_clearance p q hpq z hz).mono_right
        (hseg.trans (Metric.closedBall_subset_closedBall heh))).symm
  have hbclosure : b ∉ closure
      (connectedComponentIn (Metric.sphere (0 : ℂ) 1 \ {u, v}) a) := by
    intro hbc
    apply harcs
    rw [connectedComponentIn_eq_image ha] at hbc ⊢
    have hsub : (⟨b, hb⟩ : ↥(Metric.sphere (0 : ℂ) 1 \ {u, v})) ∈
        closure (connectedComponent (⟨a, ha⟩ : ↥(Metric.sphere (0 : ℂ) 1 \ {u, v}))) :=
      closure_subtype.mpr hbc
    rw [isClosed_connectedComponent.closure_eq] at hsub
    exact ⟨⟨b, hb⟩, hsub, rfl⟩
  have hclosesphere : closure
      (connectedComponentIn (Metric.sphere (0 : ℂ) 1 \ {u, v}) a) ⊆
      Metric.sphere (0 : ℂ) 1 := by
    exact closure_minimal
      ((connectedComponentIn_subset _ _).trans sdiff_subset) Metric.isClosed_sphere
  suffices hpolygon :
    ∃ (n : ℕ) (P : Polygon ℂ n),
      3 ≤ n ∧ Function.Injective P.vertices ∧ P.HasNondegenerateEdges ∧
      (∀ i j : Fin n, i ≠ j →
        P.edgeSet ℝ i ∩ P.edgeSet ℝ j =
          ({P i, P (finRotate n i)} ∩ {P j, P (finRotate n j)})) ∧
      Disjoint (P.boundary ℝ) K ∧
      P.boundary ℝ ∩ Metric.sphere (0 : ℂ) 1 = {a, b} ∧
      (∀ z ∈ ({a, b} : Set ℂ), ∃ (i : Fin n) (r s : ℝ),
        P i = r • z ∧ P (finRotate n i) = s • z ∧
        z ∈ openSegment ℝ (P i) (P (finRotate n i))) by
    obtain ⟨n, P, hn, hinj, hnd, hint, hdisj, hcircle, htrans⟩ := hpolygon
    have htransverse : ∀ z ∈ ({a, b} : Set ℂ), ∃ (i : Fin n) (r s : ℝ),
        P i = r • z ∧ P (finRotate n i) = s • z ∧
        z ∈ openSegment ℝ (P i) (P (finRotate n i)) ∧
        (P (finRotate n i) - P i).re * z.re +
          (P (finRotate n i) - P i).im * z.im ≠ 0 := by
      intro z hz
      obtain ⟨i, r, s, hr, hs, hzi⟩ := htrans z hz
      refine ⟨i, r, s, hr, hs, hzi, ?_⟩
      have hrs : s - r ≠ 0 := by
        intro heq
        have hsr : s = r := sub_eq_zero.mp heq
        exact hnd i (hr.trans (hs.trans (congrArg (fun t : ℝ ↦ t • z) hsr)).symm)
      have hznorm : ‖z‖ = 1 := by
        have hzsphere := (hcircle.symm.subset hz).2
        simpa only [Metric.mem_sphere, dist_zero_right] using hzsphere
      have hsq : z.re * z.re + z.im * z.im = 1 := by
        have heq := Complex.sq_norm z
        rw [hznorm] at heq
        simpa only [Complex.normSq_apply, one_pow] using heq.symm
      rw [hr, hs]
      simp only [Complex.sub_re, Complex.sub_im, Complex.real_smul, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, add_zero]
      have hdot : (s * z.re - r * z.re) * z.re +
          (s * z.im - r * z.im) * z.im = s - r := by
        calc
          _ = (s - r) * (z.re * z.re + z.im * z.im) := by ring
          _ = s - r := by rw [hsq, mul_one]
      exact hdot.symm ▸ hrs
    refine ⟨n, P, hn, hinj, hnd, hint, hdisj, hcircle, htransverse, ?_⟩
    apply subset_antisymm
    · rintro z ⟨hzarc, hzP⟩
      have hzab := hcircle.subset ⟨hzP, hclosesphere hzarc⟩
      rcases hzab with rfl | rfl
      · simp
      · exact (hbclosure hzarc).elim
    · intro z hz
      have hza : z = a := hz
      subst z
      exact ⟨subset_closure (mem_connectedComponentIn ha),
        (hcircle.symm.subset (by simp : a ∈ ({a, b} : Set ℂ))).1⟩
  exact cairns_round_disk_two_walk_polygon_provider
    (K := K) (hK := hK) (hKdisk := hKdisk) (u := u) (v := v)
    (a := a) (b := b) (hu := hu) (hv := hv) (huv := huv)
    (hKcircle := hKcircle) (ha := ha) (hb := hb) (harcs := harcs)
    (eta_a := eta_a) (eta_b := eta_b) (heta_a := heta_a)
    (heta_b := heta_b) (hcollar_a := hcollar_a)
    (hcollar_b := hcollar_b) (hcomponent := hcomponent) (S := S)
    (hSwalk := hSwalk) (hSdisk := hSdisk) (hScompact := hScompact)
    (hclearance := hclearance) (hexterior_far := hexterior_far)
    (houteravoid := houteravoid)
    (hprotected_crossing := hprotected_crossing)

end HolomorphicAnosov

