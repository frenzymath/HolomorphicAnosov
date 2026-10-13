import HolomorphicAnosov.Topology.PolygonBoundaryCompact
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Tactic.Linarith
import Mathlib.Geometry.Polygon.Basic
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.MetricSpace.Bounded

/-!
# An admissible diagonal of a simple plane polygon

Source: Cairns, *An Elementary Proof of the Jordan–Schoenflies Theorem* (1951),
pp.860–861, Lemma 2.1 and Theorem 2.1. The corrected affine-level selection and
accessibility argument are the explicitly agent-written filler of the DAG node
`topo.cairns_polygon_admissible_diagonal_g2`; they are not attributed to Cairns's
faulty literal global-abscissa selection.

The plane is `ℝ × ℝ`. We reuse Mathlib's `Polygon`, `finRotate`, `edgeSet`, and
`boundary`. The explicit simplicity condition below specifies all allowed edge
intersections. A polygonal path is stated directly by a finite vertex list and an
injective continuous parametrization, affine on every unit parameter interval.
Transversality means that the two actual straight-edge directions have nonzero
coordinate determinant. No bounded Jordan component is assumed or defined.
-/

noncomputable section

open Set
open scoped Classical

namespace HolomorphicAnosov.Topology

/-- Simple closed polygons, with possible redundant collinear vertices, as used
by Cairns (1951), pp.860–861: distinct vertices, nonzero edges, and no edge
intersections other than the common endpoint of consecutive edges. -/
def IsCairnsSimplePolygon {n : ℕ} (p : Polygon (ℝ × ℝ) n) : Prop :=
  3 ≤ n ∧ Function.Injective p.vertices ∧ p.HasNondegenerateEdges ∧
    ∀ i j : Fin n, i ≠ j → ∀ x : ℝ × ℝ,
      (x ∈ p.edgeSet ℝ i ∧ x ∈ p.edgeSet ℝ j) ↔
        (i = finRotate n j ∧ x = p i) ∨ (j = finRotate n i ∧ x = p j)

/-- The forward cyclic boundary arc with k edges, closed by its endpoint chord,
as in Cairns (1951), p.861. Its vertex list includes both arc endpoints; the
closing edge is supplied by Mathlib's cyclic polygon convention. -/
def cairnsCyclicArcPolygon {n : ℕ} (p : Polygon (ℝ × ℝ) n) (i : Fin n) (k : ℕ) :
    Polygon (ℝ × ℝ) (k + 1) :=
  ⟨fun r ↦ p ((finRotate n)^[r.val] i)⟩

/--
An admissible diagonal, with pointwise simple one-crossing polygonal accessibility
from the unique unbounded complementary component, and the two smaller cyclic
polygons. The natural numbers a and b are the numbers of original boundary edges
in the two arcs. The path has m nonzero affine pieces: its restriction to [0,m]
is continuous and injective, and every affine piece has the stated endpoints.
The single crossing occurs strictly within one of these pieces and strictly
within an original polygon edge; their coordinate determinant is nonzero.

Source:
Cairns, An Elementary Proof of the Jordan-Schoenflies Theorem (1951), printed pp.860–861,
literature/cairns-jordan-schoenflies-1951.pdf physical pp.2–3. Lemma2.1 and the induction step in
Theorem2.1; the literal least-abscissa choice is corrected by the explicitly agent-written
affine-level argument below.

Complete natural-language proof:

1. The polygon boundary is compact as a finite union of compact affine segments. Enclose it in a
   square. The square exterior is the union of four convex open half-planes, with consecutive
   overlaps, so it is preconnected and unbounded. It lies in one complementary component. Every
   unbounded component meets that exterior because its complement is bounded; hence this component
   U∞ is unique. Choose a linear functional L(x,y)=x+εy with distinct values at the finitely many
   vertices by avoiding the finitely many forbidden slopes. Let P0 be its unique minimum vertex,
   with preceding and following vertices P1,P2. The half-plane L<L(P0) is preconnected, unbounded
   and disjoint from the polygon, so it lies in U∞. Every nonincident edge has L>L(P0). Their finite
   compact union therefore misses a ball of radius δ>0 about P0.

2. Noncollinearity gives the affine basis (P1,P0,P2), with barycentric coordinates C0,C1,C2. These
   sum to one and reconstruct each point; Δ=conv{P1,P0,P2} is exactly the set where all three
   coordinates are nonnegative. Put λ=1−C1=C0+C2. Thus 0≤λ≤1 on Δ, and λ=0 there only at P0.
   Simplicity implies that a polygon vertex lying on an edge is one of its endpoints. Consequently
   every additional vertex Q in Δ has C0(Q)>0 and C2(Q)>0. If such vertices exist, choose one
   minimizing λ and put c=λ(Q); otherwise put c=1.

3. Here is the edge-clipping argument. A nonincident edge cannot meet either radial side below λ=1:
   the polygon intersection rule would force P0 or a neighbor, whereas nonincidence excludes P0 and
   the neighbors have λ=1. Suppose an edge contains z with C0(z)>0, C2(z)>0 and λ(z)≤1, and another
   point y on that edge has λ(y)<1 but y∉Δ. Then C1(y)>0 and min(C0(y),C2(y))<0. Along [y,z], the
   continuous minimum of these two affine coordinates changes from negative to positive. The
   intermediate value theorem supplies u before z with minimum zero; both coordinates are
   nonnegative, while λ(u)<1 gives C1(u)>0. Thus u belongs to a radial side below λ=1,
   contradiction. Therefore y∈Δ. If z has λ(z)<c, affine linearity gives a polygon-edge endpoint y
   with λ(y)<c. The clipping argument puts it in Δ, but the minimum choice permits only P0; an edge
   containing P0 is incident and has a zero radial coordinate, contradicting the strict coordinates
   of z. Hence the region C0>0,C2>0,λ<c misses the entire polygon. In the additional-vertex case
   every point of (P0,Q) lies in this region, so this diagonal misses the boundary.

4. In the empty-triangle case choose d=[P1,P2]. A point z in its open segment has C0,C2>0 and λ=1.
   If z belonged to an edge, the clipping argument would put any endpoint of height below one in Δ,
   impossible except P0, which again would make the edge incident. Both edge endpoints therefore
   have height at least one. Neither endpoint equals z, because no additional vertex lies in Δ;
   strict affine interpolation at z forces both heights to equal one. For a polygon vertex of height
   one, its C0 coordinate is outside (0,1), since otherwise it would be an additional vertex of Δ.
   The two endpoint C0 values surround C0(z)∈(0,1), so their real interval contains both zero and
   one. The affine image-of-segment identity and uniqueness of coordinates put both P1 and P2 on
   this edge. The vertex-on-edge rule makes them its endpoints, but P1 and P2 are not consecutive
   when n≥4. This contradiction also excludes a collinear overlap. Thus d° misses the polygon. In
   both cases the diagonal endpoints are nonconsecutive and all points t∈d° satisfy C0(t),C2(t)>0
   and λ(t)≤c.

5. For each t∈d°, construct an explicit two-segment simple crossing path. Write v=P1−P0, w=P2−P0,
   α=L(P1)−L(P0)>0 and β=L(P2)−L(P0)>0. Let A(a,b)=P0+av+bw; its C0,C2 coordinates are a,b. Choose
   κ>0 sufficiently small that a=κβ<C0(t), 2a<c, and both x=A(a,−κ(α+β)) and y=A(a,a) lie in the
   radius-δ ball. Such κ follows by bounding their displacements with κ times the sum of two fixed
   vector norms plus β+1. Then L(x)−L(P0)=−κβ²<0, so x∈U∞. On [x,y] the coordinate C0 is the
   positive constant a, and C2 vanishes exactly at s0=(α+β)/(α+2β)∈(0,1). The whole segment stays in
   the convex ball, which excludes nonincident edges; C0>0 excludes the other radial edge. At s0 the
   point is A(a,0), strictly within [P0,P1], since 0<a<1. The crossing direction is κ(α+2β)w, and
   the crossed edge direction is −v; their determinant is κ(α+2β)det(v,w)≠0 by noncollinearity. The
   segment [y,t] has positive C0,C2, and all its points except possibly t have λ<c, so it misses the
   boundary; t misses it by the diagonal result. The first piece has constant C0=a, while C0
   strictly increases along the second piece after y, giving disjoint piece interiors. Each piece is
   nonzero. Parametrize them affinely on [0,1] and [1,2], pasting at y. Continuity, injectivity on
   [0,2], and the unique transverse boundary crossing at s0 follow. This proves precisely the stated
   accessibility, without asserting that t is the first intersection with the diagonal.

6. Let a be the cyclic forward distance from the first chosen endpoint i to the second j, and b=n−a.
   Nonconsecutiveness gives a,b≥2, so a+1<n and b+1<n. The iterate identity for finRotate identifies
   each arc's vertices with the corresponding consecutive offsets in Fin n; because the arc has
   fewer than n vertices, these vertices are distinct. Every edge except the closing edge is an
   original polygon edge. The closing edge is the diagonal. Any intersection of its closed segment
   with the polygon is one of its endpoints, since its open segment is disjoint from the boundary.
   The original vertex-on-edge rule then makes every new edge intersection a common endpoint.
   Injectivity of the arc vertex list converts this endpoint description into exactly the
   consecutive-edge intersection formula defining IsCairnsSimplePolygon. Both cyclic arc polygons
   therefore satisfy the original, unchanged definition.

Source discrepancy:
location: Cairns printed p.861, Lemma2.1 verification
reason: No preceding affine normalization makes P1P2 vertical. The printed least global abscissa
criterion does not ensure nonintersection. This disputes the recipe, not the diagonal-existence
conclusion.
counterexample: The cyclic simple pentagon (0,0),(1,10),(6,1),(5,3),(10,0) has P0=(0,0),
neighbours P1=(1,10), P2=(10,0). The least-abscissa non-neighbour vertex in their triangle is
P3=(5,3), but P0P3 intersects edge (1,10)(6,1) at (59/12,59/20), interior to both segments. P1P2
lies on the exterior side of the pentagon.
correction: Minimize λ(P0)=0, λ(P1)=λ(P2)=1 over other triangle vertices instead; ties and base
vertices are allowed.
-/
theorem cairns_polygon_admissible_diagonal
    {n : ℕ} (p : Polygon (ℝ × ℝ) n) (hn : 4 ≤ n)
    (hsimple : IsCairnsSimplePolygon p)
    (hcorners : ∀ i : Fin n,
      ¬Collinear ℝ ({p i, p (finRotate n i),
        p (finRotate n (finRotate n i))} : Set (ℝ × ℝ))) :
    ∃ Uinf : Set (ℝ × ℝ),
      (∃ x ∈ (p.boundary ℝ)ᶜ, Uinf = connectedComponentIn (p.boundary ℝ)ᶜ x) ∧
      ¬Bornology.IsBounded Uinf ∧
      (∀ V : Set (ℝ × ℝ),
        (∃ x ∈ (p.boundary ℝ)ᶜ, V = connectedComponentIn (p.boundary ℝ)ᶜ x) →
        ¬Bornology.IsBounded V → V = Uinf) ∧
      ∃ (i j : Fin n) (a b : ℕ),
        i ≠ j ∧ j ≠ finRotate n i ∧ i ≠ finRotate n j ∧
        2 ≤ a ∧ 2 ≤ b ∧ a + b = n ∧ j = (finRotate n)^[a] i ∧
        Disjoint (openSegment ℝ (p i) (p j)) (p.boundary ℝ) ∧
        (∀ t ∈ openSegment ℝ (p i) (p j),
          ∃ (m : ℕ) (w : Fin (m + 1) → ℝ × ℝ) (γ : ℝ → ℝ × ℝ),
            0 < m ∧
            (∀ r : Fin m, w r.castSucc ≠ w r.succ) ∧
            ContinuousOn γ (Icc (0 : ℝ) m) ∧ InjOn γ (Icc (0 : ℝ) m) ∧
            γ 0 ∈ Uinf ∧ γ m = t ∧
            (∀ (r : Fin m) (s : ℝ), s ∈ Icc (0 : ℝ) 1 →
              γ ((r.val : ℝ) + s) = AffineMap.lineMap (w r.castSucc) (w r.succ) s) ∧
            ∃ (r : Fin m) (s : ℝ) (e : Fin n),
              0 < s ∧ s < 1 ∧
              γ ((r.val : ℝ) + s) ∈ openSegment ℝ (p e) (p (finRotate n e)) ∧
              (w r.succ - w r.castSucc).1 * (p (finRotate n e) - p e).2 -
                (w r.succ - w r.castSucc).2 * (p (finRotate n e) - p e).1 ≠ 0 ∧
              (∀ τ ∈ Icc (0 : ℝ) m,
                γ τ ∈ p.boundary ℝ ↔ τ = (r.val : ℝ) + s)) ∧
        IsCairnsSimplePolygon (cairnsCyclicArcPolygon p i a) ∧ a + 1 < n ∧
        IsCairnsSimplePolygon (cairnsCyclicArcPolygon p j b) ∧ b + 1 < n := by
  have hexterior : ∃ Uinf : Set (ℝ × ℝ),
      (∃ x ∈ (p.boundary ℝ)ᶜ, Uinf = connectedComponentIn (p.boundary ℝ)ᶜ x) ∧
      ¬Bornology.IsBounded Uinf ∧
      (∀ V : Set (ℝ × ℝ),
        (∃ x ∈ (p.boundary ℝ)ᶜ, V = connectedComponentIn (p.boundary ℝ)ᶜ x) →
        ¬Bornology.IsBounded V → V = Uinf) := by
    obtain ⟨R, hR, hKR⟩ := p.isCompact_boundary.isBounded.subset_ball_lt 0 (0 : ℝ × ℝ)
    let A : Set (ℝ × ℝ) := {z | R < z.1}
    let B : Set (ℝ × ℝ) := {z | R < z.2}
    let C : Set (ℝ × ℝ) := {z | z.1 < -R}
    let D : Set (ℝ × ℝ) := {z | z.2 < -R}
    let S := ((A ∪ B) ∪ C) ∪ D
    have hA : IsPreconnected A :=
      (convex_halfSpace_gt (LinearMap.fst ℝ ℝ ℝ).isLinear R).isPreconnected
    have hB : IsPreconnected B :=
      (convex_halfSpace_gt (LinearMap.snd ℝ ℝ ℝ).isLinear R).isPreconnected
    have hC : IsPreconnected C :=
      (convex_halfSpace_lt (LinearMap.fst ℝ ℝ ℝ).isLinear (-R)).isPreconnected
    have hD : IsPreconnected D :=
      (convex_halfSpace_lt (LinearMap.snd ℝ ℝ ℝ).isLinear (-R)).isPreconnected
    have hAB : IsPreconnected (A ∪ B) :=
      hA.union (R + 1, R + 1) (by dsimp [A]; linarith) (by dsimp [B]; linarith) hB
    have hABC : IsPreconnected ((A ∪ B) ∪ C) :=
      hAB.union (-R - 1, R + 1) (Or.inr (by dsimp [B]; linarith))
        (by dsimp [C]; linarith) hC
    have hS : IsPreconnected S :=
      hABC.union (-R - 1, -R - 1) (Or.inr (by dsimp [C]; linarith))
        (by dsimp [D]; linarith) hD
    have hSq : ∀ z : ℝ × ℝ, z ∉ S → z ∈ Metric.closedBall 0 R := by
      intro z hz
      simp only [S, A, B, C, D, mem_union, mem_ofPred_eq, not_or, not_lt] at hz
      simp only [Metric.mem_closedBall, dist_zero_right, Prod.norm_def, Real.norm_eq_abs,
        max_le_iff, abs_le]
      exact ⟨⟨by linarith [hz.1.2], hz.1.1.1⟩, ⟨by linarith [hz.2], hz.1.1.2⟩⟩
    have hSK : S ⊆ (p.boundary ℝ)ᶜ := by
      intro z hz hk
      have hb := hKR hk
      simp only [Metric.mem_ball, dist_zero_right, Prod.norm_def, Real.norm_eq_abs,
        max_lt_iff, abs_lt] at hb
      rcases hz with ((ha | hb') | hc) | hd
      · dsimp [A] at ha; linarith [hb.1.2]
      · dsimp [B] at hb'; linarith [hb.2.2]
      · dsimp [C] at hc; linarith [hb.1.1]
      · dsimp [D] at hd; linarith [hb.2.1]
    have hS_unbounded : ¬Bornology.IsBounded S := by
      intro hb
      obtain ⟨r, hr⟩ := hb.subset_closedBall (0 : ℝ × ℝ)
      have hx : (max R r + 1, 0) ∈ S :=
        Or.inl (Or.inl (Or.inl (by dsimp [A]; linarith [le_max_left R r])))
      have hh := hr hx
      simp only [Metric.mem_closedBall, dist_zero_right, Prod.norm_def, Real.norm_eq_abs,
        max_le_iff] at hh
      have := le_abs_self (max R r + 1)
      linarith [le_max_right R r, hh.1]
    let x : ℝ × ℝ := (R + 1, R + 1)
    have hxS : x ∈ S := Or.inl (Or.inl (Or.inl (by dsimp [A, x]; linarith)))
    have hsub := hS.subset_connectedComponentIn hxS hSK
    refine ⟨connectedComponentIn (p.boundary ℝ)ᶜ x, ⟨x, hSK hxS, rfl⟩,
      fun hb ↦ hS_unbounded (hb.subset hsub), ?_⟩
    rintro V ⟨y, hy, rfl⟩ hV
    have hmeet : ∃ z ∈ connectedComponentIn (p.boundary ℝ)ᶜ y, z ∈ S := by
      by_contra! h
      exact hV (Metric.isBounded_closedBall.subset fun z hz ↦ hSq z (h z hz))
    obtain ⟨z, hzV, hzS⟩ := hmeet
    exact (connectedComponentIn_eq hzV).trans (connectedComponentIn_eq (hsub hzS)).symm
  obtain ⟨Uinf, hUinf, hUnbounded, hUnique⟩ := hexterior
  refine ⟨Uinf, hUinf, hUnbounded, hUnique, ?_⟩
  obtain ⟨ε, hε⟩ := (Set.finite_range
    (fun ij : Fin n × Fin n ↦ ((p ij.2).1 - (p ij.1).1) /
      ((p ij.1).2 - (p ij.2).2))).exists_notMem
  let L : (ℝ × ℝ) →ₗ[ℝ] ℝ := LinearMap.fst ℝ ℝ ℝ + ε • LinearMap.snd ℝ ℝ ℝ
  have hL (z : ℝ × ℝ) : L z = z.1 + ε * z.2 := rfl
  have hLinj : Function.Injective (fun i : Fin n ↦ L (p i)) := by
    intro i j hij
    dsimp only at hij
    rw [hL, hL] at hij
    by_cases hy : (p i).2 = (p j).2
    · apply hsimple.2.1
      apply Prod.ext
      · rw [hy] at hij
        linarith
      · exact hy
    · have hden : (p i).2 - (p j).2 ≠ 0 := sub_ne_zero.mpr hy
      have heq : ((p j).1 - (p i).1) / ((p i).2 - (p j).2) = ε := by
        apply (div_eq_iff hden).mpr
        nlinarith
      exact (hε ⟨(i, j), heq⟩).elim
  obtain ⟨i₀, _, hi₀⟩ := Set.exists_min_image (univ : Set (Fin n))
    (fun i ↦ L (p i)) (Set.finite_univ) ⟨⟨0, by omega⟩, mem_univ _⟩
  have hstrict (j : Fin n) (hj : j ≠ i₀) : L (p i₀) < L (p j) :=
    lt_of_le_of_ne (hi₀ j (mem_univ _)) (fun h ↦ hj (hLinj h).symm)
  have hposEdges (i : Fin n) (hi : i ≠ i₀) (hnext : finRotate n i ≠ i₀) :
      p.edgeSet ℝ i ⊆ {z | L (p i₀) < L z} := by
    simp only [Polygon.edgeSet, affineSegment_eq_segment]
    exact (convex_halfSpace_gt L.isLinear (L (p i₀))).segment_subset
      (hstrict i hi) (hstrict _ hnext)
  have hboundaryLevel : p.boundary ℝ ⊆ {z | L (p i₀) ≤ L z} := by
    intro z hz
    obtain ⟨i, hi⟩ := mem_iUnion.mp hz
    exact (convex_halfSpace_ge L.isLinear (L (p i₀))).segment_subset
      (hi₀ i (mem_univ _)) (hi₀ _ (mem_univ _))
      (by simpa only [Polygon.edgeSet, affineSegment_eq_segment] using hi)
  let H : Set (ℝ × ℝ) := {z | L z < L (p i₀)}
  have hHconn : IsPreconnected H := (convex_halfSpace_lt L.isLinear _).isPreconnected
  have hHsub : H ⊆ (p.boundary ℝ)ᶜ := by
    intro z hz hzP
    exact (not_lt_of_ge (hboundaryLevel hzP)) (show L z < L (p i₀) from hz)
  have hHunbounded : ¬Bornology.IsBounded H := by
    intro hb
    obtain ⟨R, hR⟩ := hb.subset_closedBall (0 : ℝ × ℝ)
    let c := min (L (p i₀) - 1) (-R - 1)
    have hcH : (c, 0) ∈ H := by
      change L (c, 0) < L (p i₀)
      rw [hL]
      dsimp [c]
      nlinarith [min_le_left (L (p i₀) - 1) (-R - 1)]
    have hbnd := hR hcH
    simp only [Metric.mem_closedBall, dist_zero_right, Prod.norm_def, Real.norm_eq_abs,
      abs_zero, max_le_iff] at hbnd
    have hc := min_le_right (L (p i₀) - 1) (-R - 1)
    have := neg_le_abs c
    dsimp only [c] at this hbnd
    linarith [hbnd.1]
  have hHne : H.Nonempty := by
    refine ⟨(L (p i₀) - 1, 0), ?_⟩
    change L (L (p i₀) - 1, 0) < L (p i₀)
    rw [hL]
    simp
  have hHU : H ⊆ Uinf := by
    obtain ⟨x, hx⟩ := hHne
    have hsub := hHconn.subset_connectedComponentIn hx hHsub
    have heq := hUnique (connectedComponentIn (p.boundary ℝ)ᶜ x)
      ⟨x, hHsub hx, rfl⟩ (fun hb ↦ hHunbounded (hb.subset hsub))
    exact heq ▸ hsub
  let F : Set (ℝ × ℝ) := ⋃ (i : Fin n) (_ : i ≠ i₀ ∧ finRotate n i ≠ i₀), p.edgeSet ℝ i
  have hFcompact : IsCompact F := by
    apply isCompact_iUnion
    intro i
    apply isCompact_iUnion
    intro hi
    rw [Polygon.edgeSet_eq_image_edgePath (R := ℝ)]
    exact isCompact_Icc.image (by dsimp [Polygon.edgePath]; fun_prop)
  have hnotF : p i₀ ∉ F := by
    intro h
    obtain ⟨i, hi⟩ := mem_iUnion.mp h
    obtain ⟨hne, hmem⟩ := mem_iUnion.mp hi
    exact (lt_irrefl (L (p i₀))) (hposEdges i hne.1 hne.2 hmem)
  obtain ⟨δ, hδ, hδF⟩ : ∃ δ : ℝ, 0 < δ ∧ Metric.ball (p i₀) δ ⊆ Fᶜ :=
    Metric.isOpen_iff.mp hFcompact.isClosed.isOpen_compl (p i₀) hnotF
  let iprev := (finRotate n).symm i₀
  let inext := finRotate n i₀
  have htri : AffineIndependent ℝ ![p iprev, p i₀, p inext] := by
    apply affineIndependent_iff_not_collinear_set.mpr
    simpa only [iprev, inext, Equiv.apply_symm_apply] using hcorners iprev
  let T : AffineBasis (Fin 3) ℝ (ℝ × ℝ) :=
    ⟨![p iprev, p i₀, p inext], htri,
      htri.affineSpan_eq_top_iff_card_eq_finrank_add_one.mpr (by
        simp [Module.finrank_prod, Module.finrank_self])⟩
  let Λ : (ℝ × ℝ) →ᵃ[ℝ] ℝ := AffineMap.const ℝ (ℝ × ℝ) 1 - T.coord 1
  have hΛ0 : Λ (p i₀) = 0 := by
    change 1 - T.coord 1 (T 1) = 0
    simp
  have hΛprev : Λ (p iprev) = 1 := by
    change 1 - T.coord 1 (T 0) = 1
    simp
  have hΛnext : Λ (p inext) = 1 := by
    change 1 - T.coord 1 (T 2) = 1
    simp
  let Δ := convexHull ℝ ({p iprev, p i₀, p inext} : Set (ℝ × ℝ))
  have hΛnonneg : Δ ⊆ {z | 0 ≤ Λ z} := by
    apply convexHull_min
    · simp only [insert_subset_iff, singleton_subset_iff, mem_ofPred_eq]
      simp [hΛprev, hΛ0, hΛnext]
    · exact (convex_Ici (0 : ℝ)).affine_preimage Λ
  have hΛle : Δ ⊆ {z | Λ z ≤ 1} := by
    apply convexHull_min
    · simp only [insert_subset_iff, singleton_subset_iff, mem_ofPred_eq]
      simp [hΛprev, hΛ0, hΛnext]
    · exact (convex_Iic (1 : ℝ)).affine_preimage Λ
  have hΔcoord (z : ℝ × ℝ) : z ∈ Δ ↔ ∀ k, 0 ≤ T.coord k z := by
    have hrange : Set.range T = {p iprev, p i₀, p inext} := by
      change Set.range ![p iprev, p i₀, p inext] = _
      simp only [Matrix.range_cons, Matrix.range_empty, Set.singleton_union, insert_empty_eq]
    change z ∈ convexHull ℝ {p iprev, p i₀, p inext} ↔ _
    rw [← hrange, T.convexHull_eq_nonneg_coord]
    rfl
  have hΛpos (z : ℝ × ℝ) (hz : z ∈ Δ) (hne : z ≠ p i₀) : 0 < Λ z := by
    have hc := (hΔcoord z).mp hz
    have hsum := T.sum_coord_apply_eq_one z
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hsum
    change T.coord 0 z + (T.coord 1 z + T.coord 2 z) = 1 at hsum
    apply lt_of_le_of_ne (hΛnonneg hz)
    intro heq
    have hc1 : T.coord 1 z = 1 := by
      change 0 = 1 - T.coord 1 z at heq
      linarith
    have hc0 : T.coord 0 z = 0 := by linarith [hc 0, hc 2]
    have hc2 : T.coord 2 z = 0 := by linarith [hc 0, hc 2]
    apply hne
    change z = T 1
    apply T.ext_elem
    intro k
    fin_cases k <;> simp [hc0, hc1, hc2]
  let E : Set (Fin n) := {j | p j ∈ Δ ∧ j ≠ iprev ∧ j ≠ i₀ ∧ j ≠ inext}
  have hselection : E = ∅ ∨ ∃ q ∈ E, 0 < Λ (p q) ∧ Λ (p q) ≤ 1 ∧
      ∀ j ∈ E, Λ (p q) ≤ Λ (p j) := by
    rcases E.eq_empty_or_nonempty with he | he
    · exact Or.inl he
    · obtain ⟨q, hq, hmin⟩ := Set.exists_min_image E (fun j ↦ Λ (p j)) E.toFinite he
      exact Or.inr ⟨q, hq, hΛpos _ hq.1 (fun h ↦ hq.2.2.1 (hsimple.2.1 h)),
        hΛle hq.1, hmin⟩
  have hvertexEdge (i j : Fin n) (hj : p j ∈ p.edgeSet ℝ i) :
      j = i ∨ j = finRotate n i := by
    by_cases hji : j = i
    · exact Or.inl hji
    have hjj : p j ∈ p.edgeSet ℝ j := by
      simpa only [Polygon.edgeSet, affineSegment_eq_segment] using left_mem_segment ℝ (p j) (p (finRotate n j))
    rcases (hsimple.2.2.2 i j (Ne.symm hji) (p j)).mp ⟨hj, hjj⟩ with h | h
    · exact Or.inl (hsimple.2.1 h.2)
    · exact Or.inr h.1
  have hradial0 (z : ℝ × ℝ) (hz : z ∈ Δ) (hzero : T.coord 0 z = 0) :
      z ∈ p.edgeSet ℝ i₀ := by
    have hc := (hΔcoord z).mp hz
    have hs := T.sum_coord_apply_eq_one z
    have hv := T.linear_combination_coord_eq_self z
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hs hv
    change T.coord 0 z + (T.coord 1 z + T.coord 2 z) = 1 at hs
    change T.coord 0 z • p iprev + (T.coord 1 z • p i₀ + T.coord 2 z • p inext) = z at hv
    rw [hzero, zero_smul, zero_add] at hv
    simp only [Polygon.edgeSet, affineSegment_eq_segment]
    exact ⟨T.coord 1 z, T.coord 2 z, hc 1, hc 2, by linarith, hv⟩
  have hradial2 (z : ℝ × ℝ) (hz : z ∈ Δ) (hzero : T.coord 2 z = 0) :
      z ∈ p.edgeSet ℝ iprev := by
    have hc := (hΔcoord z).mp hz
    have hs := T.sum_coord_apply_eq_one z
    have hv := T.linear_combination_coord_eq_self z
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hs hv
    change T.coord 0 z + (T.coord 1 z + T.coord 2 z) = 1 at hs
    change T.coord 0 z • p iprev + (T.coord 1 z • p i₀ + T.coord 2 z • p inext) = z at hv
    rw [hzero, zero_smul, add_zero] at hv
    simp only [Polygon.edgeSet, affineSegment_eq_segment, iprev, Equiv.apply_symm_apply]
    exact ⟨T.coord 0 z, T.coord 1 z, hc 0, hc 1, by linarith, hv⟩
  have hinnerVertex (q : Fin n) (hq : q ∈ E) :
      0 < T.coord 0 (p q) ∧ 0 < T.coord 2 (p q) := by
    have hc := (hΔcoord (p q)).mp hq.1
    constructor
    · apply lt_of_le_of_ne (hc 0)
      intro heq
      rcases hvertexEdge i₀ q (hradial0 _ hq.1 heq.symm) with h | h
      · exact hq.2.2.1 h
      · exact hq.2.2.2 h
    · apply lt_of_le_of_ne (hc 2)
      intro heq
      rcases hvertexEdge iprev q (hradial2 _ hq.1 heq.symm) with h | h
      · exact hq.2.1 h
      · apply hq.2.2.1
        simpa only [iprev, Equiv.apply_symm_apply] using h
  have hchordCoords (q : Fin n) (hq : q ∈ E) (z : ℝ × ℝ)
      (hz : z ∈ openSegment ℝ (p i₀) (p q)) :
      0 < T.coord 0 z ∧ 0 < T.coord 2 z ∧ Λ z < Λ (p q) := by
    obtain ⟨s, hs, rfl⟩ := (openSegment_eq_image_lineMap ℝ (p i₀) (p q)) ▸ hz
    have hc := hinnerVertex q hq
    have h0 : T.coord 0 (p i₀) = 0 := by change T.coord 0 (T 1) = 0; simp
    have h2 : T.coord 2 (p i₀) = 0 := by change T.coord 2 (T 1) = 0; simp
    simp only [AffineMap.apply_lineMap, AffineMap.lineMap_apply_ring, h0, h2,
      hΛ0, mul_zero, zero_add]
    exact ⟨mul_pos hs.1 hc.1, mul_pos hs.1 hc.2,
      mul_lt_of_lt_one_left (hΛpos _ hq.1 (fun h ↦ hq.2.2.1 (hsimple.2.1 h))) hs.2⟩
  have hincident0 (z : ℝ × ℝ) (hz : z ∈ p.edgeSet ℝ i₀) : T.coord 0 z = 0 := by
    simp only [Polygon.edgeSet, affineSegment_eq_segment, segment_eq_image_lineMap] at hz
    obtain ⟨s, hs, rfl⟩ := hz
    have h0 : T.coord 0 (p i₀) = 0 := by change T.coord 0 (T 1) = 0; simp
    have h2 : T.coord 0 (p (finRotate n i₀)) = 0 := by change T.coord 0 (T 2) = 0; simp
    simp only [AffineMap.apply_lineMap, h0, h2, AffineMap.lineMap_same, AffineMap.const_apply]
  have hincidentPrev (z : ℝ × ℝ) (hz : z ∈ p.edgeSet ℝ iprev) : T.coord 2 z = 0 := by
    simp only [Polygon.edgeSet, affineSegment_eq_segment, segment_eq_image_lineMap] at hz
    obtain ⟨s, hs, rfl⟩ := hz
    have h0 : T.coord 2 (p iprev) = 0 := by change T.coord 2 (T 0) = 0; simp
    have h1 : T.coord 2 (p (finRotate n iprev)) = 0 := by
      simp only [iprev, Equiv.apply_symm_apply]
      change T.coord 2 (T 1) = 0
      simp
    simp only [AffineMap.apply_lineMap, h0, h1, AffineMap.lineMap_same, AffineMap.const_apply]
  have hnoRadialLow (i : Fin n) (hi : i ≠ i₀) (hiprev : i ≠ iprev)
      (z : ℝ × ℝ) (hz : z ∈ p.edgeSet ℝ i) (hl : Λ z < 1) :
      z ∉ p.edgeSet ℝ i₀ ∧ z ∉ p.edgeSet ℝ iprev := by
    constructor
    · intro hz0
      rcases (hsimple.2.2.2 i i₀ hi z).mp ⟨hz, hz0⟩ with h | h
      · have hznext : z = p inext := h.2.trans (congrArg p h.1)
        rw [hznext, hΛnext] at hl
        exact (lt_irrefl 1) hl
      · apply hiprev
        simpa only [iprev, Equiv.symm_apply_apply] using
          (congrArg (finRotate n).symm h.1).symm
    · intro hzprev
      rcases (hsimple.2.2.2 i iprev hiprev z).mp ⟨hz, hzprev⟩ with h | h
      · apply hi
        simpa only [iprev, Equiv.apply_symm_apply] using h.1
      · rw [h.2, hΛprev] at hl
        exact (lt_irrefl 1) hl
  have hclip (i : Fin n) (hi : i ≠ i₀) (hiprev : i ≠ iprev)
      (z y : ℝ × ℝ) (hz : z ∈ p.edgeSet ℝ i) (hy : y ∈ p.edgeSet ℝ i)
      (hz0 : 0 < T.coord 0 z) (hz2 : 0 < T.coord 2 z)
      (hzL : Λ z ≤ 1) (hyL : Λ y < 1) : y ∈ Δ := by
    by_contra hyΔ
    have hy1 : 0 < T.coord 1 y := by
      change 1 - T.coord 1 y < 1 at hyL
      linarith
    have hymin : min (T.coord 0 y) (T.coord 2 y) < 0 := by
      by_contra h
      have hh := le_min_iff.mp (le_of_not_gt h)
      apply hyΔ
      apply (hΔcoord y).mpr
      intro k
      fin_cases k
      · exact hh.1
      · exact hy1.le
      · exact hh.2
    let f : ℝ → ℝ := fun s ↦ min (T.coord 0 (AffineMap.lineMap y z s))
      (T.coord 2 (AffineMap.lineMap y z s))
    have hc (k : Fin 3) : Continuous (fun s : ℝ ↦ T.coord k (AffineMap.lineMap y z s)) := by
      simp_rw [AffineMap.apply_lineMap, AffineMap.lineMap_apply_ring]
      fun_prop
    have hf : Continuous f := (hc 0).min (hc 2)
    obtain ⟨s, hs, hfs⟩ := intermediate_value_Icc (show (0 : ℝ) ≤ 1 by norm_num)
      hf.continuousOn (show 0 ∈ Icc (f 0) (f 1) by
        simpa only [f, AffineMap.lineMap_apply_zero, AffineMap.lineMap_apply_one, mem_Icc] using
          And.intro hymin.le (le_min hz0.le hz2.le))
    let u := AffineMap.lineMap y z s
    have hs1 : s < 1 := by
      apply lt_of_le_of_ne hs.2
      intro heq
      subst s
      simp only [f, AffineMap.lineMap_apply_one] at hfs
      exact (ne_of_gt (lt_min hz0 hz2)) hfs
    have huSeg : u ∈ segment ℝ y z := lineMap_mem_segment ℝ y z hs
    have huEdge : u ∈ p.edgeSet ℝ i := by
      have hconv : Convex ℝ (p.edgeSet ℝ i) := by
        simpa only [Polygon.edgeSet, affineSegment_eq_segment] using
          convex_segment (𝕜 := ℝ) (p i) (p (finRotate n i))
      exact hconv.segment_subset hy hz huSeg
    have huL : Λ u < 1 := by
      change Λ (AffineMap.lineMap y z s) < 1
      rw [AffineMap.apply_lineMap, AffineMap.lineMap_apply_ring]
      nlinarith [mul_pos (sub_pos.mpr hs1) (sub_pos.mpr hyL),
        mul_nonneg hs.1 (sub_nonneg.mpr hzL)]
    have hu1 : 0 < T.coord 1 u := by
      change 1 - T.coord 1 u < 1 at huL
      linarith
    change min (T.coord 0 u) (T.coord 2 u) = 0 at hfs
    have hu0 : 0 ≤ T.coord 0 u := by simpa only [hfs] using min_le_left (T.coord 0 u) (T.coord 2 u)
    have hu2 : 0 ≤ T.coord 2 u := by simpa only [hfs] using min_le_right (T.coord 0 u) (T.coord 2 u)
    have huΔ : u ∈ Δ := by
      apply (hΔcoord u).mpr
      intro k
      fin_cases k
      · exact hu0
      · exact hu1.le
      · exact hu2
    have havoid := hnoRadialLow i hi hiprev u huEdge huL
    by_cases hh : T.coord 0 u ≤ T.coord 2 u
    · rw [min_eq_left hh] at hfs
      exact havoid.1 (hradial0 u huΔ hfs)
    · rw [min_eq_right (le_of_not_ge hh)] at hfs
      exact havoid.2 (hradial2 u huΔ hfs)
  have hlowNoBoundary (c : ℝ) (hc : c ≤ 1)
      (hvertices : ∀ j : Fin n, p j ∈ Δ → Λ (p j) < c → j = i₀)
      (z : ℝ × ℝ) (hz0 : 0 < T.coord 0 z) (hz2 : 0 < T.coord 2 z)
      (hzL : Λ z < c) : z ∉ p.boundary ℝ := by
    intro hzP
    obtain ⟨i, hiEdge⟩ := mem_iUnion.mp hzP
    have hi : i ≠ i₀ := by
      intro heq
      subst i
      exact (ne_of_gt hz0) (hincident0 z hiEdge)
    have hiprev : i ≠ iprev := by
      intro heq
      subst i
      exact (ne_of_gt hz2) (hincidentPrev z hiEdge)
    obtain ⟨j, hjEdge, hjL⟩ : ∃ j : Fin n, p j ∈ p.edgeSet ℝ i ∧ Λ (p j) < c := by
      by_cases hleft : Λ (p i) < c
      · refine ⟨i, ?_, hleft⟩
        simpa only [Polygon.edgeSet, affineSegment_eq_segment] using
          left_mem_segment ℝ (p i) (p (finRotate n i))
      · refine ⟨finRotate n i, ?_, ?_⟩
        · simpa only [Polygon.edgeSet, affineSegment_eq_segment] using
            right_mem_segment ℝ (p i) (p (finRotate n i))
        · by_contra hright
          have hzge : c ≤ Λ z := ((convex_Ici c).affine_preimage Λ).segment_subset
            (le_of_not_gt hleft) (le_of_not_gt hright)
            (by simpa only [Polygon.edgeSet, affineSegment_eq_segment] using hiEdge)
          exact (not_lt_of_ge hzge) hzL
    have hjΔ := hclip i hi hiprev z (p j) hiEdge hjEdge hz0 hz2 (hzL.le.trans hc) (hjL.trans_le hc)
    have hji := hvertices j hjΔ hjL
    subst j
    rcases hvertexEdge i i₀ hjEdge with heq | heq
    · exact hi heq.symm
    · apply hiprev
      simpa only [iprev, Equiv.symm_apply_apply] using
        (congrArg (finRotate n).symm heq).symm
  have hselectedChord (q : Fin n) (hq : q ∈ E)
      (hmin : ∀ j ∈ E, Λ (p q) ≤ Λ (p j)) :
      Disjoint (openSegment ℝ (p i₀) (p q)) (p.boundary ℝ) := by
    apply Set.disjoint_left.mpr
    intro z hz hzP
    have hzcoord := hchordCoords q hq z hz
    apply hlowNoBoundary (Λ (p q)) (hΛle hq.1) ?_ z hzcoord.1 hzcoord.2.1 hzcoord.2.2 hzP
    intro j hjΔ hjL
    by_contra hji
    have hjprev : j ≠ iprev := by
      intro heq
      subst j
      rw [hΛprev] at hjL
      exact (not_lt_of_ge (hΛle hq.1)) hjL
    have hjnext : j ≠ inext := by
      intro heq
      subst j
      rw [hΛnext] at hjL
      exact (not_lt_of_ge (hΛle hq.1)) hjL
    exact (not_lt_of_ge (hmin j ⟨hjΔ, hjprev, hji, hjnext⟩)) hjL
  have hbaseCoords (z : ℝ × ℝ) (hz : z ∈ openSegment ℝ (p iprev) (p inext)) :
      0 < T.coord 0 z ∧ 0 < T.coord 2 z ∧ Λ z = 1 := by
    obtain ⟨s, hs, rfl⟩ := (openSegment_eq_image_lineMap ℝ (p iprev) (p inext)) ▸ hz
    have h00 : T.coord 0 (p iprev) = 1 := by change T.coord 0 (T 0) = 1; simp
    have h02 : T.coord 0 (p inext) = 0 := by change T.coord 0 (T 2) = 0; simp
    have h20 : T.coord 2 (p iprev) = 0 := by change T.coord 2 (T 0) = 0; simp
    have h22 : T.coord 2 (p inext) = 1 := by change T.coord 2 (T 2) = 1; simp
    simp only [AffineMap.apply_lineMap, AffineMap.lineMap_apply_ring, h00, h02, h20, h22,
      hΛprev, hΛnext, mul_zero, mul_one, add_zero, zero_add]
    exact ⟨sub_pos.mpr hs.2, hs.1, sub_add_cancel _ _⟩
  have hemptyVertices (hE : E = ∅) (j : Fin n) (hj : p j ∈ Δ) :
      j = iprev ∨ j = i₀ ∨ j = inext := by
    by_cases h0 : j = iprev
    · exact Or.inl h0
    by_cases h1 : j = i₀
    · exact Or.inr (Or.inl h1)
    by_cases h2 : j = inext
    · exact Or.inr (Or.inr h2)
    have hje : j ∈ E := ⟨hj, h0, h1, h2⟩
    rw [hE] at hje
    exact hje.elim
  have hemptyBaseLevels (hE : E = ∅) (i : Fin n) (z : ℝ × ℝ)
      (hz : z ∈ openSegment ℝ (p iprev) (p inext)) (hzEdge : z ∈ p.edgeSet ℝ i) :
      ∀ j : Fin n, p j ∈ p.edgeSet ℝ i → 1 ≤ Λ (p j) := by
    have hzc := hbaseCoords z hz
    have hi : i ≠ i₀ := by
      intro heq
      subst i
      exact (ne_of_gt hzc.1) (hincident0 z hzEdge)
    have hiprev : i ≠ iprev := by
      intro heq
      subst i
      exact (ne_of_gt hzc.2.1) (hincidentPrev z hzEdge)
    intro j hj
    by_contra hjL
    have hjL := lt_of_not_ge hjL
    have hjΔ := hclip i hi hiprev z (p j) hzEdge hj hzc.1 hzc.2.1 hzc.2.2.le hjL
    rcases hemptyVertices hE j hjΔ with h | h | h
    · subst j
      rw [hΛprev] at hjL
      exact (lt_irrefl 1) hjL
    · subst j
      rcases hvertexEdge i i₀ hj with heq | heq
      · exact hi heq.symm
      · apply hiprev
        simpa only [iprev, Equiv.symm_apply_apply] using
          (congrArg (finRotate n).symm heq).symm
    · subst j
      rw [hΛnext] at hjL
      exact (lt_irrefl 1) hjL
  have hemptyBaseVertexBound (hE : E = ∅) (j : Fin n) (hjL : Λ (p j) = 1) :
      T.coord 0 (p j) ≤ 0 ∨ 1 ≤ T.coord 0 (p j) := by
    by_contra hh
    push Not at hh
    have hj1 : T.coord 1 (p j) = 0 := by
      change 1 - T.coord 1 (p j) = 1 at hjL
      linarith
    have hs := T.sum_coord_apply_eq_one (p j)
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hs
    change T.coord 0 (p j) + (T.coord 1 (p j) + T.coord 2 (p j)) = 1 at hs
    have hjΔ : p j ∈ Δ := by
      apply (hΔcoord (p j)).mpr
      intro k
      fin_cases k
      · exact hh.1.le
      · exact hj1.ge
      · change 0 ≤ T.coord 2 (p j)
        linarith
    rcases hemptyVertices hE j hjΔ with h | h | h
    · subst j
      have hc : T.coord 0 (p iprev) = 1 := by change T.coord 0 (T 0) = 1; simp
      rw [hc] at hh
      exact (lt_irrefl 1) hh.2
    · subst j
      rw [hΛ0] at hjL
      norm_num at hjL
    · subst j
      have hc : T.coord 0 (p inext) = 0 := by change T.coord 0 (T 2) = 0; simp
      rw [hc] at hh
      exact (lt_irrefl 0) hh.1
  have hbaseNoVertex (hE : E = ∅) (j : Fin n) :
      p j ∉ openSegment ℝ (p iprev) (p inext) := by
    intro hj
    have hc := hbaseCoords (p j) hj
    have hs := T.sum_coord_apply_eq_one (p j)
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hs
    change T.coord 0 (p j) + (T.coord 1 (p j) + T.coord 2 (p j)) = 1 at hs
    have hj1 : T.coord 1 (p j) = 0 := by
      have := hc.2.2
      change 1 - T.coord 1 (p j) = 1 at this
      linarith
    rcases hemptyBaseVertexBound hE j hc.2.2 with h | h <;> linarith
  have hneighborsNonadjacent : inext ≠ finRotate n iprev ∧ iprev ≠ finRotate n inext := by
    have : NeZero n := ⟨by omega⟩
    constructor
    · intro heq
      have heq' : finRotate n i₀ = i₀ := by
        simpa only [inext, iprev, Equiv.apply_symm_apply] using heq
      exact hsimple.2.2.1 i₀ (congrArg p heq').symm
    · intro heq
      have hh := congrArg (finRotate n) heq
      simp only [iprev, inext, Equiv.apply_symm_apply, finRotate_apply] at hh
      have heq3 : (0 : Fin n) = 1 + 1 + 1 := by
        apply add_left_cancel (a := i₀)
        simpa only [add_zero, ← add_assoc] using hh
      have hv := congrArg Fin.val heq3
      norm_num [Fin.val_add, Fin.val_one, Nat.mod_eq_of_lt (show 1 < n by omega),
        Nat.mod_eq_of_lt (show 2 < n by omega), Nat.mod_eq_of_lt (show 3 < n by omega)] at hv
  have hbaseUnique (u v : ℝ × ℝ) (hL : Λ u = Λ v)
      (h0 : T.coord 0 u = T.coord 0 v) : u = v := by
    have h1 : T.coord 1 u = T.coord 1 v := by
      change 1 - T.coord 1 u = 1 - T.coord 1 v at hL
      linarith
    have hu := T.sum_coord_apply_eq_one u
    have hv := T.sum_coord_apply_eq_one v
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hu hv
    change T.coord 0 u + (T.coord 1 u + T.coord 2 u) = 1 at hu
    change T.coord 0 v + (T.coord 1 v + T.coord 2 v) = 1 at hv
    have h2 : T.coord 2 u = T.coord 2 v := by linarith
    apply T.ext_elem
    intro k
    fin_cases k
    · exact h0
    · exact h1
    · exact h2
  have hemptyBase (hE : E = ∅) :
      Disjoint (openSegment ℝ (p iprev) (p inext)) (p.boundary ℝ) := by
    apply Set.disjoint_left.mpr
    intro z hz hzP
    have hzc := hbaseCoords z hz
    obtain ⟨i, hzEdge⟩ := mem_iUnion.mp hzP
    have hleft : p i ∈ p.edgeSet ℝ i := by
      simpa only [Polygon.edgeSet, affineSegment_eq_segment] using
        left_mem_segment ℝ (p i) (p (finRotate n i))
    have hright : p (finRotate n i) ∈ p.edgeSet ℝ i := by
      simpa only [Polygon.edgeSet, affineSegment_eq_segment] using
        right_mem_segment ℝ (p i) (p (finRotate n i))
    have hge0 := hemptyBaseLevels hE i z hz hzEdge i hleft
    have hge1 := hemptyBaseLevels hE i z hz hzEdge (finRotate n i) hright
    obtain ⟨s, hs, heq⟩ := (show z ∈ AffineMap.lineMap (p i) (p (finRotate n i)) '' Icc (0 : ℝ) 1 by
      simpa only [Polygon.edgeSet, affineSegment_eq_segment, segment_eq_image_lineMap] using hzEdge)
    have hs0 : 0 < s := by
      apply lt_of_le_of_ne hs.1
      intro he
      subst s
      simp only [AffineMap.lineMap_apply_zero] at heq
      exact hbaseNoVertex hE i (heq ▸ hz)
    have hs1 : s < 1 := by
      apply lt_of_le_of_ne hs.2
      intro he
      subst s
      simp only [AffineMap.lineMap_apply_one] at heq
      exact hbaseNoVertex hE (finRotate n i) (heq ▸ hz)
    have hweight : (1 - s) * Λ (p i) + s * Λ (p (finRotate n i)) = 1 := by
      rw [← AffineMap.lineMap_apply_ring, ← AffineMap.apply_lineMap, heq]
      exact hzc.2.2
    have he0 : Λ (p i) = 1 := by
      apply le_antisymm _ hge0
      by_contra h
      have hprod := mul_pos (sub_pos.mpr hs1) (sub_pos.mpr (lt_of_not_ge h))
      nlinarith [mul_nonneg hs0.le (sub_nonneg.mpr hge1)]
    have he1 : Λ (p (finRotate n i)) = 1 := by
      apply le_antisymm _ hge1
      by_contra h
      have hprod := mul_pos hs0 (sub_pos.mpr (lt_of_not_ge h))
      nlinarith [mul_nonneg (sub_nonneg.mpr hs1.le) (sub_nonneg.mpr hge0)]
    have hlevel (u : ℝ × ℝ) (hu : u ∈ p.edgeSet ℝ i) : Λ u = 1 := by
      simp only [Polygon.edgeSet, affineSegment_eq_segment, segment_eq_image_lineMap] at hu
      obtain ⟨t, ht, rfl⟩ := hu
      simp only [AffineMap.apply_lineMap, he0, he1, AffineMap.lineMap_same, AffineMap.const_apply]
    have himage : T.coord 0 '' p.edgeSet ℝ i =
        uIcc (T.coord 0 (p i)) (T.coord 0 (p (finRotate n i))) := by
      simp only [Polygon.edgeSet, affineSegment_eq_segment, image_segment, segment_eq_uIcc]
    have hzcoord : T.coord 0 z ∈ uIcc (T.coord 0 (p i)) (T.coord 0 (p (finRotate n i))) := by
      rw [← himage]
      exact ⟨z, hzEdge, rfl⟩
    have hzlt : T.coord 0 z < 1 := by
      have hz1 : T.coord 1 z = 0 := by
        have hh := hzc.2.2
        change 1 - T.coord 1 z = 1 at hh
        linarith
      have hsum := T.sum_coord_apply_eq_one z
      simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hsum
      change T.coord 0 z + (T.coord 1 z + T.coord 2 z) = 1 at hsum
      linarith [hzc.2.1]
    have hI : Icc (0 : ℝ) 1 ⊆ uIcc (T.coord 0 (p i)) (T.coord 0 (p (finRotate n i))) := by
      have hb0 := hemptyBaseVertexBound hE i he0
      have hb1 := hemptyBaseVertexBound hE (finRotate n i) he1
      intro r hr
      rcases le_total (T.coord 0 (p i)) (T.coord 0 (p (finRotate n i))) with hab | hba
      · rw [uIcc_of_le hab] at hzcoord ⊢
        rcases hb0 with hb0 | hb0 <;> rcases hb1 with hb1 | hb1 <;>
          constructor <;> linarith [hzc.1, hzcoord.1, hzcoord.2, hr.1, hr.2]
      · rw [uIcc_of_ge hba] at hzcoord ⊢
        rcases hb0 with hb0 | hb0 <;> rcases hb1 with hb1 | hb1 <;>
          constructor <;> linarith [hzc.1, hzcoord.1, hzcoord.2, hr.1, hr.2]
    obtain ⟨u, hu, hu0⟩ := himage ▸ hI (show (0 : ℝ) ∈ Icc 0 1 by norm_num)
    have huEq : u = p inext := hbaseUnique u (p inext) ((hlevel u hu).trans hΛnext.symm)
      (hu0.trans (by change (0 : ℝ) = T.coord 0 (T 2); simp))
    obtain ⟨v, hv, hv1⟩ := himage ▸ hI (show (1 : ℝ) ∈ Icc 0 1 by norm_num)
    have hvEq : v = p iprev := hbaseUnique v (p iprev) ((hlevel v hv).trans hΛprev.symm)
      (hv1.trans (by change (1 : ℝ) = T.coord 0 (T 0); simp))
    have hnextEdge : p inext ∈ p.edgeSet ℝ i := huEq ▸ hu
    have hprevEdge : p iprev ∈ p.edgeSet ℝ i := hvEq ▸ hv
    have hprevNext : iprev ≠ inext := by
      intro hh
      have h := htri.injective (show (![p iprev, p i₀, p inext] : Fin 3 → ℝ × ℝ) 0 =
          (![p iprev, p i₀, p inext] : Fin 3 → ℝ × ℝ) 2 from congrArg p hh)
      norm_num at h
    rcases hvertexEdge i inext hnextEdge with hni | hni <;>
      rcases hvertexEdge i iprev hprevEdge with hpi | hpi
    · exact hprevNext (hpi.trans hni.symm)
    · exact hneighborsNonadjacent.2 (hpi.trans (congrArg (finRotate n) hni.symm))
    · exact hneighborsNonadjacent.1 (hni.trans (congrArg (finRotate n) hpi.symm))
    · exact hprevNext (hpi.trans hni.symm)
  obtain ⟨i, j, c, hij, hnext, hprev, hcpos, hcle, hdisj, hcoords, hvertices⟩ :
      ∃ (i j : Fin n) (c : ℝ), i ≠ j ∧ j ≠ finRotate n i ∧ i ≠ finRotate n j ∧
        0 < c ∧ c ≤ 1 ∧ Disjoint (openSegment ℝ (p i) (p j)) (p.boundary ℝ) ∧
        (∀ t ∈ openSegment ℝ (p i) (p j),
          0 < T.coord 0 t ∧ 0 < T.coord 2 t ∧ Λ t ≤ c) ∧
        (∀ k : Fin n, p k ∈ Δ → Λ (p k) < c → k = i₀) := by
    rcases hselection with hE | ⟨q, hq, hqpos, hqle, hmin⟩
    · have hne : iprev ≠ inext := by
        intro hh
        have h := htri.injective (show (![p iprev, p i₀, p inext] : Fin 3 → ℝ × ℝ) 0 =
            (![p iprev, p i₀, p inext] : Fin 3 → ℝ × ℝ) 2 from congrArg p hh)
        norm_num at h
      refine ⟨iprev, inext, 1, hne, hneighborsNonadjacent.1, hneighborsNonadjacent.2,
        zero_lt_one, le_rfl, hemptyBase hE, ?_, ?_⟩
      · intro t ht
        have hh := hbaseCoords t ht
        exact ⟨hh.1, hh.2.1, hh.2.2.le⟩
      · intro k hk hkL
        rcases hemptyVertices hE k hk with h | h | h
        · subst k
          rw [hΛprev] at hkL
          exact ((lt_irrefl 1) hkL).elim
        · exact h
        · subst k
          rw [hΛnext] at hkL
          exact ((lt_irrefl 1) hkL).elim
    · have hback : i₀ ≠ finRotate n q := by
        intro heq
        apply hq.2.1
        simpa only [iprev, Equiv.symm_apply_apply] using
          (congrArg (finRotate n).symm heq).symm
      refine ⟨i₀, q, Λ (p q), Ne.symm hq.2.2.1, hq.2.2.2, hback,
        hqpos, hqle, hselectedChord q hq hmin, ?_, ?_⟩
      · intro t ht
        have hh := hchordCoords q hq t ht
        exact ⟨hh.1, hh.2.1, hh.2.2.le⟩
      · intro k hk hkL
        by_contra hk0
        have hkprev : k ≠ iprev := by
          intro heq
          subst k
          rw [hΛprev] at hkL
          exact (not_lt_of_ge hqle) hkL
        have hknext : k ≠ inext := by
          intro heq
          subst k
          rw [hΛnext] at hkL
          exact (not_lt_of_ge hqle) hkL
        exact (not_lt_of_ge (hmin k ⟨hk, hkprev, hk0, hknext⟩)) hkL
  let v := p iprev - p i₀
  let w := p inext - p i₀
  let A : ℝ → ℝ → ℝ × ℝ := fun a b ↦ (a • v + b • w) + p i₀
  have hA (f : (ℝ × ℝ) →ᵃ[ℝ] ℝ) (a b : ℝ) :
      f (A a b) = a * (f (p iprev) - f (p i₀)) +
        b * (f (p inext) - f (p i₀)) + f (p i₀) := by
    change f ((a • v + b • w) +ᵥ p i₀) = _
    rw [AffineMap.map_vadd, map_add, map_smul, map_smul]
    change a * f.linear (p iprev -ᵥ p i₀) + b * f.linear (p inext -ᵥ p i₀) + f (p i₀) = _
    rw [AffineMap.linearMap_vsub, AffineMap.linearMap_vsub]
    rfl
  have hA0 (a b : ℝ) : T.coord 0 (A a b) = a := by
    rw [hA]
    change a * (T.coord 0 (T 0) - T.coord 0 (T 1)) +
      b * (T.coord 0 (T 2) - T.coord 0 (T 1)) + T.coord 0 (T 1) = a
    simp
  have hA2 (a b : ℝ) : T.coord 2 (A a b) = b := by
    rw [hA]
    change a * (T.coord 2 (T 0) - T.coord 2 (T 1)) +
      b * (T.coord 2 (T 2) - T.coord 2 (T 1)) + T.coord 2 (T 1) = b
    simp
  have hAΛ (a b : ℝ) : Λ (A a b) = a + b := by simp [hA, hΛprev, hΛ0, hΛnext]
  have hv2 : (T.coord 2).linear v = 0 := by
    change (T.coord 2).linear (T 0 -ᵥ T 1) = 0
    rw [AffineMap.linearMap_vsub]
    simp
  have hw2 : (T.coord 2).linear w = 1 := by
    change (T.coord 2).linear (T 2 -ᵥ T 1) = 1
    rw [AffineMap.linearMap_vsub]
    simp
  have hvne : v ≠ 0 := by
    intro h
    have heq : p iprev = p i₀ := sub_eq_zero.mp h
    have hh := htri.injective (show (![p iprev, p i₀, p inext] : Fin 3 → ℝ × ℝ) 0 =
        (![p iprev, p i₀, p inext] : Fin 3 → ℝ × ℝ) 1 from heq)
    norm_num at hh
  have hdet : v.1 * w.2 - v.2 * w.1 ≠ 0 := by
    intro hd
    have hmultiple : ∃ r : ℝ, w = r • v := by
      by_cases hv1 : v.1 = 0
      · have hvsecond : v.2 ≠ 0 := by
          intro hh
          apply hvne
          exact Prod.ext hv1 hh
        refine ⟨w.2 / v.2, ?_⟩
        apply Prod.ext
        · change w.1 = w.2 / v.2 * v.1
          have hwfirst : w.1 = 0 := by
            rw [hv1] at hd
            have : v.2 * w.1 = 0 := by linarith
            exact (mul_eq_zero.mp this).resolve_left hvsecond
          simp [hv1, hwfirst]
        · change w.2 = w.2 / v.2 * v.2
          exact (div_mul_cancel₀ _ hvsecond).symm
      · refine ⟨w.1 / v.1, ?_⟩
        apply Prod.ext
        · change w.1 = w.1 / v.1 * v.1
          exact (div_mul_cancel₀ _ hv1).symm
        · change w.2 = w.1 / v.1 * v.2
          apply (mul_right_inj' hv1).mp
          field_simp
          nlinarith
    obtain ⟨r, hr⟩ := hmultiple
    rw [hr, map_smul, hv2, smul_zero] at hw2
    norm_num at hw2
  let α := L (p iprev) - L (p i₀)
  let β := L (p inext) - L (p i₀)
  have hα : 0 < α := by
    apply sub_pos.mpr
    apply hstrict
    intro heq
    have hh := htri.injective (show (![p iprev, p i₀, p inext] : Fin 3 → ℝ × ℝ) 0 =
        (![p iprev, p i₀, p inext] : Fin 3 → ℝ × ℝ) 1 from congrArg p heq)
    norm_num at hh
  have hβ : 0 < β := by
    apply sub_pos.mpr
    apply hstrict
    intro heq
    exact hsimple.2.2.1 i₀ (congrArg p heq).symm
  let D₀ := β • v - (α + β) • w
  let D₁ := β • v + β • w
  let C := ‖D₀‖ + ‖D₁‖ + β + 1
  have hCβ : β ≤ C := by dsimp [C]; linarith [norm_nonneg D₀, norm_nonneg D₁]
  have hCD₀ : ‖D₀‖ ≤ C := by dsimp [C]; linarith [norm_nonneg D₁]
  have hCD₁ : ‖D₁‖ ≤ C := by dsimp [C]; linarith [norm_nonneg D₀]
  have hcrossingData (t : ℝ × ℝ) (ht : t ∈ openSegment ℝ (p i) (p j)) :
      ∃ k : ℝ, 0 < k ∧ k * β < T.coord 0 t ∧ 2 * (k * β) < c ∧
        A (k * β) (-k * (α + β)) ∈ Metric.ball (p i₀) δ ∧
        A (k * β) (k * β) ∈ Metric.ball (p i₀) δ ∧
        A (k * β) (-k * (α + β)) ∈ Uinf := by
    obtain ⟨k, hk, hkC⟩ := exists_pos_mul_lt
      (lt_min hδ (lt_min (hcoords t ht).1 (half_pos hcpos))) C
    rw [mul_comm C k] at hkC
    have hkδ : k * C < δ := hkC.trans_le (min_le_left _ _)
    have hkt : k * C < T.coord 0 t := hkC.trans_le ((min_le_right _ _).trans (min_le_left _ _))
    have hkc : k * C < c / 2 := hkC.trans_le ((min_le_right _ _).trans (min_le_right _ _))
    have hkβ : k * β ≤ k * C := mul_le_mul_of_nonneg_left hCβ hk.le
    have hxEq : A (k * β) (-k * (α + β)) = k • D₀ + p i₀ := by
      dsimp [A, D₀]
      module
    have hyEq : A (k * β) (k * β) = k • D₁ + p i₀ := by
      dsimp [A, D₁]
      module
    refine ⟨k, hk, hkβ.trans_lt hkt, by linarith, ?_, ?_, ?_⟩
    · rw [hxEq, Metric.mem_ball, dist_eq_norm, add_sub_cancel_right, norm_smul,
        Real.norm_eq_abs, abs_of_pos hk]
      exact (mul_le_mul_of_nonneg_left hCD₀ hk.le).trans_lt hkδ
    · rw [hyEq, Metric.mem_ball, dist_eq_norm, add_sub_cancel_right, norm_smul,
        Real.norm_eq_abs, abs_of_pos hk]
      exact (mul_le_mul_of_nonneg_left hCD₁ hk.le).trans_lt hkδ
    · apply hHU
      change L (A (k * β) (-k * (α + β))) < L (p i₀)
      have heq := hA L.toAffineMap (k * β) (-k * (α + β))
      change L (A (k * β) (-k * (α + β))) =
        k * β * α + (-k * (α + β)) * β + L (p i₀) at heq
      nlinarith only [heq, mul_pos hk (mul_pos hβ hβ)]
  have hΛcoords (z : ℝ × ℝ) : Λ z = T.coord 0 z + T.coord 2 z := by
    have hs := T.sum_coord_apply_eq_one z
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hs
    change T.coord 0 z + (T.coord 1 z + T.coord 2 z) = 1 at hs
    change 1 - T.coord 1 z = _
    linarith
  have hroute (t : ℝ × ℝ) (ht : t ∈ openSegment ℝ (p i) (p j)) :
      ∃ (x y : ℝ × ℝ) (s₀ : ℝ), x ∈ Uinf ∧
        T.coord 0 x = T.coord 0 y ∧ T.coord 0 y < T.coord 0 t ∧ x ≠ y ∧
        0 < s₀ ∧ s₀ < 1 ∧
        AffineMap.lineMap x y s₀ ∈ openSegment ℝ (p iprev) (p (finRotate n iprev)) ∧
        (y - x).1 * (p (finRotate n iprev) - p iprev).2 -
          (y - x).2 * (p (finRotate n iprev) - p iprev).1 ≠ 0 ∧
        (∀ s ∈ Icc (0 : ℝ) 1, AffineMap.lineMap x y s ∈ p.boundary ℝ ↔ s = s₀) ∧
        (∀ s ∈ Icc (0 : ℝ) 1, AffineMap.lineMap y t s ∉ p.boundary ℝ) := by
    obtain ⟨k, hk, hkt, hkc, hxball, hyball, hxU⟩ := hcrossingData t ht
    let a := k * β
    let x := A a (-k * (α + β))
    let y := A a a
    let s₀ := (α + β) / (α + 2 * β)
    have ha : 0 < a := mul_pos hk hβ
    have ha1 : a < 1 := by dsimp [a]; linarith
    have hden : 0 < α + 2 * β := by linarith
    have hs₀ : 0 < s₀ := div_pos (by linarith) hden
    have hs₁ : s₀ < 1 := (div_lt_one hden).mpr (by linarith)
    have hsEq : s₀ * (α + 2 * β) = α + β := div_mul_cancel₀ _ hden.ne'
    have hx0 : T.coord 0 x = a := hA0 _ _
    have hy0 : T.coord 0 y = a := hA0 _ _
    have hx2 : T.coord 2 x = -k * (α + β) := hA2 _ _
    have hy2 : T.coord 2 y = a := hA2 _ _
    have hxy : x ≠ y := by
      intro heq
      have hh := congrArg (T.coord 2) heq
      rw [hx2, hy2] at hh
      have := mul_pos hk (show 0 < α + β by linarith)
      dsimp [a] at hh
      nlinarith only [hh, this, mul_pos hk hβ]
    have hfirst0 (s : ℝ) : T.coord 0 (AffineMap.lineMap x y s) = a := by
      rw [AffineMap.apply_lineMap, hx0, hy0]
      simp
    have hfirst2 (s : ℝ) : T.coord 2 (AffineMap.lineMap x y s) =
        k * (s * (α + 2 * β) - (α + β)) := by
      rw [AffineMap.apply_lineMap, AffineMap.lineMap_apply_ring, hx2, hy2]
      dsimp [a]
      ring
    have hzero (s : ℝ) : T.coord 2 (AffineMap.lineMap x y s) = 0 ↔ s = s₀ := by
      rw [hfirst2, mul_eq_zero, or_iff_right hk.ne', sub_eq_zero, ← hsEq]
      exact mul_right_cancel_iff_of_pos hden
    have hcross : AffineMap.lineMap x y s₀ = A a 0 := by
      apply hbaseUnique
      · rw [hΛcoords, hfirst0, (hzero s₀).mpr rfl, hAΛ]
      · rw [hfirst0, hA0]
    have hcrossEdge : AffineMap.lineMap x y s₀ ∈
        openSegment ℝ (p iprev) (p (finRotate n iprev)) := by
      rw [hcross]
      have heq : A a 0 = AffineMap.lineMap (p i₀) (p iprev) a := by
        dsimp [A, v]
        simp only [zero_smul, add_zero, AffineMap.lineMap_apply_module']
      rw [heq]
      simpa only [iprev, Equiv.apply_symm_apply, openSegment_symm ℝ (p iprev) (p i₀)] using
        lineMap_mem_openSegment ℝ (p i₀) (p iprev) ⟨ha, ha1⟩
    have hfirstBoundary (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
        AffineMap.lineMap x y s ∈ p.boundary ℝ ↔ s = s₀ := by
      constructor
      · intro hzP
        obtain ⟨e, he⟩ := mem_iUnion.mp hzP
        have hzball : AffineMap.lineMap x y s ∈ Metric.ball (p i₀) δ :=
          (convex_ball (p i₀) δ).segment_subset hxball hyball
            (lineMap_mem_segment ℝ x y hs)
        by_cases he0 : e = i₀
        · subst e
          have hh := hincident0 _ he
          rw [hfirst0] at hh
          exact ((ne_of_gt ha) hh).elim
        by_cases henext : finRotate n e = i₀
        · have heprev : e = iprev := by
            simpa only [iprev, Equiv.symm_apply_apply] using congrArg (finRotate n).symm henext
          rw [heprev] at he
          exact (hzero s).mp (hincidentPrev _ he)
        · exact (hδF hzball (mem_iUnion.mpr ⟨e, mem_iUnion.mpr ⟨⟨he0, henext⟩, he⟩⟩)).elim
      · intro heq
        subst s
        apply mem_iUnion.mpr
        refine ⟨iprev, ?_⟩
        simpa only [Polygon.edgeSet, affineSegment_eq_segment] using
          openSegment_subset_segment ℝ (p iprev) (p (finRotate n iprev)) hcrossEdge
    have hsecondBoundary (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
        AffineMap.lineMap y t s ∉ p.boundary ℝ := by
      by_cases hs1 : s = 1
      · subst s
        simpa only [AffineMap.lineMap_apply_one] using Set.disjoint_left.mp hdisj ht
      have hslt : s < 1 := lt_of_le_of_ne hs.2 hs1
      have hyt0 : 0 < T.coord 0 (AffineMap.lineMap y t s) := by
        rw [AffineMap.apply_lineMap, AffineMap.lineMap_apply_ring, hy0]
        exact add_pos_of_pos_of_nonneg (mul_pos (sub_pos.mpr hslt) ha)
          (mul_nonneg hs.1 (hcoords t ht).1.le)
      have hyt2 : 0 < T.coord 2 (AffineMap.lineMap y t s) := by
        rw [AffineMap.apply_lineMap, AffineMap.lineMap_apply_ring, hy2]
        exact add_pos_of_pos_of_nonneg (mul_pos (sub_pos.mpr hslt) ha)
          (mul_nonneg hs.1 (hcoords t ht).2.1.le)
      have hyΛ : Λ y < c := by rw [hAΛ]; dsimp [a]; linarith only [hkc]
      have hytΛ : Λ (AffineMap.lineMap y t s) < c := by
        rw [AffineMap.apply_lineMap, AffineMap.lineMap_apply_ring]
        nlinarith only [mul_pos (sub_pos.mpr hslt) (sub_pos.mpr hyΛ),
          mul_nonneg hs.1 (sub_nonneg.mpr (hcoords t ht).2.2)]
      exact hlowNoBoundary c hcle hvertices _ hyt0 hyt2 hytΛ
    have hdir : y - x = (k * (α + 2 * β)) • w := by
      dsimp [x, y, A, a]
      module
    have hdetxy : (y - x).1 * (p (finRotate n iprev) - p iprev).2 -
        (y - x).2 * (p (finRotate n iprev) - p iprev).1 ≠ 0 := by
      have hedge : p (finRotate n iprev) - p iprev = -v := by
        simp only [iprev, Equiv.apply_symm_apply, v, neg_sub]
      rw [hdir, hedge]
      change (k * (α + 2 * β) * w.1) * (-v.2) -
        (k * (α + 2 * β) * w.2) * (-v.1) ≠ 0
      have heq : (k * (α + 2 * β) * w.1) * (-v.2) -
          (k * (α + 2 * β) * w.2) * (-v.1) =
          (k * (α + 2 * β)) * (v.1 * w.2 - v.2 * w.1) := by ring
      rw [heq]
      exact mul_ne_zero (mul_ne_zero hk.ne' hden.ne') hdet
    exact ⟨x, y, s₀, hxU, hx0.trans hy0.symm, hy0 ▸ hkt, hxy, hs₀, hs₁,
      hcrossEdge, hdetxy, hfirstBoundary, hsecondBoundary⟩
  have haccess (t : ℝ × ℝ) (ht : t ∈ openSegment ℝ (p i) (p j)) :
      ∃ (m : ℕ) (w : Fin (m + 1) → ℝ × ℝ) (γ : ℝ → ℝ × ℝ),
        0 < m ∧ (∀ r : Fin m, w r.castSucc ≠ w r.succ) ∧
        ContinuousOn γ (Icc (0 : ℝ) m) ∧ InjOn γ (Icc (0 : ℝ) m) ∧
        γ 0 ∈ Uinf ∧ γ m = t ∧
        (∀ (r : Fin m) (s : ℝ), s ∈ Icc (0 : ℝ) 1 →
          γ ((r.val : ℝ) + s) = AffineMap.lineMap (w r.castSucc) (w r.succ) s) ∧
        ∃ (r : Fin m) (s : ℝ) (e : Fin n),
          0 < s ∧ s < 1 ∧
          γ ((r.val : ℝ) + s) ∈ openSegment ℝ (p e) (p (finRotate n e)) ∧
          (w r.succ - w r.castSucc).1 * (p (finRotate n e) - p e).2 -
            (w r.succ - w r.castSucc).2 * (p (finRotate n e) - p e).1 ≠ 0 ∧
          (∀ τ ∈ Icc (0 : ℝ) m, γ τ ∈ p.boundary ℝ ↔ τ = (r.val : ℝ) + s) := by
    obtain ⟨x, y, s₀, hxU, hxy0, hyt0, hxy, hs0, hs1, hcross, htrans,
      hfirstBoundary, hsecondBoundary⟩ := hroute t ht
    have hyt : y ≠ t := by
      intro heq
      exact (ne_of_lt hyt0) (congrArg (T.coord 0) heq)
    let γ : ℝ → ℝ × ℝ := fun τ ↦ if τ ≤ 1 then AffineMap.lineMap x y τ
      else AffineMap.lineMap y t (τ - 1)
    have hgcont : Continuous γ := by
      apply Continuous.if_le
      · change Continuous (fun r : ℝ ↦ r • (y - x) + x)
        fun_prop
      · change Continuous (fun r : ℝ ↦ (r - 1) • (t - y) + y)
        fun_prop
      · exact continuous_id
      · exact continuous_const
      · intro r hr
        simp only [hr, sub_self, AffineMap.lineMap_apply_one, AffineMap.lineMap_apply_zero]
    have hfirst (s : ℝ) (hs : s ≤ 1) : γ s = AffineMap.lineMap x y s := ite_eq_left hs
    have hsecond (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
        γ (1 + s) = AffineMap.lineMap y t s := by
      by_cases hs0 : s = 0
      · subst s
        simp only [γ, add_zero, le_refl, ↓reduceIte,
          AffineMap.lineMap_apply_one, AffineMap.lineMap_apply_zero]
      · have hspos : 0 < s := lt_of_le_of_ne hs.1 (Ne.symm hs0)
        have hnot : ¬1 + s ≤ 1 := by linarith only [hspos]
        simp only [γ, hnot, ↓reduceIte, add_sub_cancel_left]
    have hfirstCoord (s : ℝ) (hs : s ≤ 1) : T.coord 0 (γ s) = T.coord 0 y := by
      rw [hfirst s hs, AffineMap.apply_lineMap, hxy0]
      simp
    have hsecondCoord (s : ℝ) (hs : 1 < s) : T.coord 0 y < T.coord 0 (γ s) := by
      change T.coord 0 y < T.coord 0 (if s ≤ 1 then _ else _)
      rw [ite_eq_right (not_le_of_gt hs), AffineMap.apply_lineMap, AffineMap.lineMap_apply_ring]
      nlinarith only [mul_pos (sub_pos.mpr hs) (sub_pos.mpr hyt0)]
    have hginj : InjOn γ (Icc (0 : ℝ) 2) := by
      intro r hr s hs heq
      by_cases hr1 : r ≤ 1 <;> by_cases hs1 : s ≤ 1
      · rw [hfirst r hr1, hfirst s hs1] at heq
        exact AffineMap.lineMap_injective ℝ hxy heq
      · have hh := congrArg (T.coord 0) heq
        rw [hfirstCoord r hr1] at hh
        exact ((ne_of_lt (hsecondCoord s (lt_of_not_ge hs1))) hh).elim
      · have hh := congrArg (T.coord 0) heq
        rw [hfirstCoord s hs1] at hh
        exact ((ne_of_lt (hsecondCoord r (lt_of_not_ge hr1))) hh.symm).elim
      · change (if r ≤ 1 then _ else _) = (if s ≤ 1 then _ else _) at heq
        rw [ite_eq_right hr1, ite_eq_right hs1] at heq
        have hh := AffineMap.lineMap_injective ℝ hyt heq
        linarith only [hh]
    refine ⟨2, ![x, y, t], γ, by norm_num, ?_, hgcont.continuousOn, hginj, ?_, ?_, ?_, ?_⟩
    · intro r
      fin_cases r
      · exact hxy
      · exact hyt
    · simpa only [hfirst 0 (by norm_num), AffineMap.lineMap_apply_zero] using hxU
    · have hh := hsecond 1 (by norm_num)
      norm_num only [one_add_one_eq_two, AffineMap.lineMap_apply_one, Nat.cast_ofNat] at hh ⊢
      exact hh
    · intro r s hs
      fin_cases r
      · simpa using hfirst s hs.2
      · simpa using hsecond s hs
    · refine ⟨0, s₀, iprev, hs0, hs1, ?_, htrans, ?_⟩
      · simpa only [Fin.val_zero, Nat.cast_zero, zero_add, hfirst s₀ hs1.le] using hcross
      · intro τ hτ
        norm_num only [Nat.cast_ofNat] at hτ
        simp only [Fin.val_zero, Nat.cast_zero, zero_add]
        by_cases hτ1 : τ ≤ 1
        · rw [hfirst τ hτ1]
          exact hfirstBoundary τ ⟨hτ.1, hτ1⟩
        · have hs : τ - 1 ∈ Icc (0 : ℝ) 1 := by constructor <;> linarith only [hτ.1, hτ.2, hτ1]
          have hnot : γ τ ∉ p.boundary ℝ := by
            change (if τ ≤ 1 then _ else _) ∉ p.boundary ℝ
            rw [ite_eq_right hτ1]
            exact hsecondBoundary (τ - 1) hs
          exact iff_of_false hnot (by intro heq; subst τ; exact hτ1 hs1.le)
  have harc (base : Fin n) (k : ℕ) (hk2 : 2 ≤ k) (hkn : k + 1 < n)
      (hdisj : Disjoint (openSegment ℝ (p base) (p ((finRotate n)^[k] base))) (p.boundary ℝ)) :
      IsCairnsSimplePolygon (cairnsCyclicArcPolygon p base k) := by
    have : NeZero n := ⟨by omega⟩
    let q := cairnsCyclicArcPolygon p base k
    let J : Fin (k + 1) → Fin n := fun r ↦ (finRotate n)^[r.val] base
    have hJ (r : Fin (k + 1)) : J r = base + (⟨r.val, by omega⟩ : Fin n) := by
      exact (congrFun (finCycle_eq_finRotate_iterate (k := ⟨r.val, by omega⟩)) base).symm
    have hJinj : Function.Injective J := by
      intro r s hrs
      rw [hJ, hJ] at hrs
      have hh : (⟨r.val, by omega⟩ : Fin n) = ⟨s.val, by omega⟩ := add_left_cancel hrs
      exact Fin.ext (congrArg (fun z : Fin n ↦ z.val) hh)
    have hq (r : Fin (k + 1)) : q r = p (J r) := rfl
    have hqinj : Function.Injective q.vertices := fun r s h ↦ hJinj (hsimple.2.1 h)
    have hJrot (r : Fin (k + 1)) (hr : r ≠ Fin.last k) :
        J (finRotate (k + 1) r) = finRotate n (J r) := by
      change (finRotate n)^[(finRotate (k + 1) r).val] base = _
      rw [coe_finRotate_of_ne_last hr, Function.iterate_succ_apply']
    have hqnondeg : q.HasNondegenerateEdges := by
      intro r heq
      have hh := congrArg Fin.val (hqinj heq)
      by_cases hr : r = Fin.last k
      · subst r
        simp only [finRotate_last, Fin.val_last, Fin.val_zero] at hh
        omega
      · rw [coe_finRotate_of_ne_last hr] at hh
        omega
    have hzero : q 0 = p base := rfl
    have hlast : q (Fin.last k) = p ((finRotate n)^[k] base) := rfl
    have hedge (r : Fin (k + 1)) (hr : r ≠ Fin.last k) :
        q.edgeSet ℝ r = p.edgeSet ℝ (J r) := by
      simp only [Polygon.edgeSet, hq, hJrot r hr]
    have hlastedge : q.edgeSet ℝ (Fin.last k) = segment ℝ (q (Fin.last k)) (q 0) := by
      simp only [Polygon.edgeSet, finRotate_last, affineSegment_eq_segment]
    have hchord (z : ℝ × ℝ) (hz : z ∈ q.edgeSet ℝ (Fin.last k)) (hzP : z ∈ p.boundary ℝ) :
        z = q 0 ∨ z = q (Fin.last k) := by
      rw [hlastedge, segment_symm, ← insert_endpoints_openSegment] at hz
      rcases hz with h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · exact (Set.disjoint_left.mp hdisj h hzP).elim
    have hvertex (r : Fin (k + 1)) (hr : r ≠ Fin.last k) (s : Fin (k + 1))
        (hs : q s ∈ q.edgeSet ℝ r) : s = r ∨ s = finRotate (k + 1) r := by
      by_cases hsr : s = r
      · exact Or.inl hsr
      have hsr' : J r ≠ J s := fun h ↦ hsr (hJinj h).symm
      have hss : q s ∈ p.edgeSet ℝ (J s) := by
        simpa only [Polygon.edgeSet, affineSegment_eq_segment, hq] using
          left_mem_segment ℝ (p (J s)) (p (finRotate n (J s)))
      rcases (hsimple.2.2.2 (J r) (J s) hsr' (q s)).mp ⟨hedge r hr ▸ hs, hss⟩ with h | h
      · exact Or.inl (hqinj h.2)
      · exact Or.inr (hJinj (h.1.trans (hJrot r hr).symm))
    have hmixed (r : Fin (k + 1)) (hr : r ≠ Fin.last k) (z : ℝ × ℝ)
        (hzr : z ∈ q.edgeSet ℝ r) (hzlast : z ∈ q.edgeSet ℝ (Fin.last k)) :
        (z = q r ∨ z = q (finRotate (k + 1) r)) ∧
          (z = q (Fin.last k) ∨ z = q (finRotate (k + 1) (Fin.last k))) := by
      have hzP : z ∈ p.boundary ℝ := mem_iUnion.mpr ⟨J r, hedge r hr ▸ hzr⟩
      rcases hchord z hzlast hzP with hz | hz
      · have hv := hvertex r hr 0 (hz ▸ hzr)
        refine ⟨?_, Or.inr (by simpa only [finRotate_last] using hz)⟩
        exact hv.imp (fun h ↦ hz.trans (congrArg q h)) (fun h ↦ hz.trans (congrArg q h))
      · have hv := hvertex r hr (Fin.last k) (hz ▸ hzr)
        refine ⟨?_, Or.inl hz⟩
        exact hv.imp (fun h ↦ hz.trans (congrArg q h)) (fun h ↦ hz.trans (congrArg q h))
    have hinter (r s : Fin (k + 1)) (hrs : r ≠ s) (z : ℝ × ℝ)
        (hzr : z ∈ q.edgeSet ℝ r) (hzs : z ∈ q.edgeSet ℝ s) :
        (z = q r ∨ z = q (finRotate (k + 1) r)) ∧
          (z = q s ∨ z = q (finRotate (k + 1) s)) := by
      by_cases hr : r = Fin.last k
      · subst r
        exact (hmixed s (Ne.symm hrs) z hzs hzr).symm
      by_cases hs : s = Fin.last k
      · subst s
        exact hmixed r hr z hzr hzs
      have hJs : J r ≠ J s := fun h ↦ hrs (hJinj h)
      rcases (hsimple.2.2.2 (J r) (J s) hJs z).mp
        ⟨hedge r hr ▸ hzr, hedge s hs ▸ hzs⟩ with h | h
      · exact ⟨Or.inl h.2, Or.inr (h.2.trans (congrArg p (h.1.trans (hJrot s hs).symm)))⟩
      · exact ⟨Or.inr (h.2.trans (congrArg p (h.1.trans (hJrot r hr).symm))), Or.inl h.2⟩
    refine ⟨by omega, hqinj, hqnondeg, ?_⟩
    intro r s hrs z
    constructor
    · rintro ⟨hzr, hzs⟩
      rcases hinter r s hrs z hzr hzs with ⟨hr | hr, hs | hs⟩
      · exact (hrs (hqinj (hr.symm.trans hs))).elim
      · exact Or.inl ⟨hqinj (hr.symm.trans hs), hr⟩
      · exact Or.inr ⟨(hqinj (hr.symm.trans hs)).symm, hs⟩
      · exact (hrs ((finRotate (k + 1)).injective (hqinj (hr.symm.trans hs)))).elim
    · rintro (⟨hrs, rfl⟩ | ⟨hsr, rfl⟩)
      · constructor
        · simpa only [Polygon.edgeSet, affineSegment_eq_segment] using left_mem_segment ℝ (q r) (q (finRotate (k + 1) r))
        · simpa only [hrs, Polygon.edgeSet, affineSegment_eq_segment] using right_mem_segment ℝ (q s) (q (finRotate (k + 1) s))
      · constructor
        · simpa only [hsr, Polygon.edgeSet, affineSegment_eq_segment] using right_mem_segment ℝ (q r) (q (finRotate (k + 1) r))
        · simpa only [Polygon.edgeSet, affineSegment_eq_segment] using left_mem_segment ℝ (q s) (q (finRotate (k + 1) s))
  obtain ⟨a, b, ha2, hb2, hab, han, hbn, hja, hib⟩ :
      ∃ a b : ℕ, 2 ≤ a ∧ 2 ≤ b ∧ a + b = n ∧ a + 1 < n ∧ b + 1 < n ∧
        j = (finRotate n)^[a] i ∧ i = (finRotate n)^[b] j := by
    have : NeZero n := ⟨by omega⟩
    let d : Fin n := j - i
    let a := d.val
    let b := n - a
    have han : a < n := d.isLt
    have hdi : i + d = j := add_sub_cancel _ _
    have hiter (r : Fin n) (m : ℕ) (hm : m < n) :
        (finRotate n)^[m] r = r + (⟨m, hm⟩ : Fin n) :=
      (congrFun (finCycle_eq_finRotate_iterate (k := ⟨m, hm⟩)) r).symm
    have hja : j = (finRotate n)^[a] i := by rw [hiter i a han]; exact hdi.symm
    have ha2 : 2 ≤ a := by
      by_contra ha
      have hcases : a = 0 ∨ a = 1 := by omega
      rcases hcases with h | h
      · rw [h, Function.iterate_zero_apply] at hja
        exact hij hja.symm
      · rw [h, Function.iterate_one] at hja
        exact hnext hja
    have hab : a + b = n := by dsimp [b]; omega
    have hb2 : 2 ≤ b := by
      by_contra hb
      have ha1 : a + 1 = n := by dsimp [b] at hb; omega
      have hd1 : d + 1 = 0 := by
        apply Fin.ext
        simp only [Fin.val_add, Fin.val_one', Fin.val_zero,
          Nat.mod_eq_of_lt (show 1 < n by omega)]
        change (a + 1) % n = 0
        rw [ha1, Nat.mod_self]
      apply hprev
      rw [finRotate_apply, ← hdi, add_assoc, hd1, add_zero]
    have hbn : b < n := by omega
    have hdb : d + (⟨b, hbn⟩ : Fin n) = 0 := by
      apply Fin.ext
      change (a + b) % n = 0
      rw [hab, Nat.mod_self]
    have hib : i = (finRotate n)^[b] j := by
      rw [hiter j b hbn, ← hdi, add_assoc, hdb, add_zero]
    exact ⟨a, b, ha2, hb2, hab, by omega, by omega, hja, hib⟩
  refine ⟨i, j, a, b, hij, hnext, hprev, ha2, hb2, hab, hja, hdisj, haccess,
    ?_, han, ?_, hbn⟩
  · exact harc i a ha2 han (by simpa only [← hja] using hdisj)
  · apply harc j b hb2 hbn
    simpa only [← hib, openSegment_symm ℝ (p j) (p i)] using hdisj

end HolomorphicAnosov.Topology

