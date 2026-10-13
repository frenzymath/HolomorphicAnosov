import HolomorphicAnosov.Topology.PolygonEdgeLocalLine
import HolomorphicAnosov.Topology.TwoLocalSidesSeparation
import HolomorphicAnosov.Topology.PolygonDeleteVertexSimplicity
import HolomorphicAnosov.Topology.PolygonDeleteVertexBoundary
import HolomorphicAnosov.Topology.CollinearSegmentsJoint
import HolomorphicAnosov.Topology.PolygonEdgeIntersection
import HolomorphicAnosov.Topology.AmbientCircleRegions
import HolomorphicAnosov.Topology.DiskPrescribedBoundaryExtension
import HolomorphicAnosov.Topology.CircleDiskBoundaryExtension
import HolomorphicAnosov.Topology.CairnsPolygonAdmissibleDiagonal
import HolomorphicAnosov.Topology.CairnsPolygonOppositeCellsAmalgamation
import HolomorphicAnosov.Topology.CairnsSimplePolygonAmbientCircle
import Mathlib.Geometry.Polygon.Basic
import Mathlib.Analysis.Complex.Circle
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Cairns's finite polygon Jordan–Schoenflies theorem

Source: Stewart S. Cairns, *An Elementary Proof of the Jordan-Schoenflies Theorem*,
Proc. Amer. Math. Soc. 2 (1951), 860–867, preliminary results 2(A,B), Theorem 2.1
and Lemma 2.1, printed pages 860–861. DAG node:
`topo.cairns_simple_polygon_schoenflies`.

The real plane is represented by `ℂ`, with its usual real affine structure and topology.
The polygon data, affine edges and boundary are Mathlib's `Polygon`. Simplicity below
is a condition on finite vertices and edge intersections, not an assumed Jordan conclusion.
All four additional definitions have concrete Mathlib-only bodies of at most ten lines.
Redundant-vertex deletion and the transverse crossing assertion are proved below.
The remaining gap is the ambient polygon-to-circle equivalence, whose finite
diagonal/amalgamation induction is described in the theorem docstring.
-/

noncomputable section

open Set

namespace HolomorphicAnosov

/-- Cairns's simple closed polygon: at least three distinct cyclic vertices, nonzero edges,
and different edges intersect only at vertices common to both edges. Collinear redundant
vertices are permitted. Source: Cairns (1951), Theorem 2.1, pages 860–861. -/
def IsSimpleClosedPolygon {n : ℕ} (p : Polygon ℂ n) : Prop :=
  3 ≤ n ∧ Function.Injective p.vertices ∧ p.HasNondegenerateEdges ∧
    ∀ i j : Fin n, i ≠ j →
      p.edgeSet ℝ i ∩ p.edgeSet ℝ j ⊆
        p.vertices '' ({i, finRotate n i} ∩ {j, finRotate n j})

/-- A simple polygonal path, parametrized on `[0,1]`: an injective continuous path with
a finite strictly increasing affine subdivision. Values outside `[0,1] are irrelevant.
Source: the polygonal crossing assertion in Cairns (1951), Theorem 2.1, page 860. -/
def IsSimplePolygonalPath (f : ℝ → ℂ) : Prop :=
  ContinuousOn f (Icc 0 1) ∧ Set.InjOn f (Icc 0 1) ∧
    ∃ m : ℕ, ∃ t : Fin (m + 1) → ℝ,
      0 < m ∧ StrictMono t ∧ t 0 = 0 ∧ t (Fin.last m) = 1 ∧
      ∀ i : Fin m, ∀ s ∈ Icc (t i.castSucc) (t i.succ),
        f s = AffineMap.lineMap (f (t i.castSucc)) (f (t i.succ))
          ((s - t i.castSucc) / (t i.succ - t i.castSucc))

/-- One transverse crossing at the interior of a polygon edge. The only intersection is
at an interior path parameter; immediately before and after it the path lies strictly on
opposite sides of the edge's line. `im (conj v * w)` is the real oriented area determinant.
This includes crossings at polygonal-path corners and excludes tangencies and overlaps.
Source: Cairns (1951), Theorem 2.1, page 860; the node's edge-interior formulation. -/
def CrossesPolygonOnce {n : ℕ} (p : Polygon ℂ n) (f : ℝ → ℂ) : Prop :=
  ∃ i : Fin n, ∃ t ∈ Ioo (0 : ℝ) 1,
    f '' Icc 0 1 ∩ p.boundary ℝ = {f t} ∧
    f t ∈ openSegment ℝ (p i) (p (finRotate n i)) ∧
    ∃ δ > 0, δ < t ∧ δ < 1 - t ∧
      ∀ s ∈ Ioo (t - δ) t, ∀ u ∈ Ioo t (t + δ),
        (star (p (finRotate n i) - p i) * (f s - p i)).im *
          (star (p (finRotate n i) - p i) * (f u - p i)).im < 0

/-- Delete the selected cyclic vertex while retaining all other vertices in their cyclic
order. This is concrete finite data; preservation of simplicity is a theorem conclusion.
Source: the redundant-collinear-vertex reduction in the node's Cairns polygon proof. -/
def deletePolygonVertex {n : ℕ} (p : Polygon ℂ (n + 1))
    (i : Fin (n + 1)) : Polygon ℂ n :=
  ⟨fun j ↦ p.vertices (i.succAbove j)⟩

/-- **Finite polygon Jordan–Schoenflies, prescribed boundary extension, crossing and
redundant-vertex removal.** Source: Cairns (1951), preliminary 2(A,B), Theorem 2.1
and Lemma 2.1, printed pages 860–861 (local PDF physical pages 2–3).
DAG node: `topo.cairns_simple_polygon_schoenflies`.

Natural-language proof, relative to the named prerequisites in that node:

1. For two curves already ambient-equivalent to circles, conjugate any prescribed
boundary homeomorphism to a circle homeomorphism `b`. Extend it radially by `R(0)=0`
and `R(rz)=r b(z)` for `r>0`, `z∈S¹`. Its inverse uses `b⁻¹`; preservation of radius
gives continuity at zero and polar coordinates give continuity elsewhere. This is
Cairns 2(A), and presupposes no general Jordan theorem.

2. Use the exact finite opposite-cell amalgamation prerequisite
`topo.cairns_polygon_opposite_cells_ambient_amalgamation_g2` for closed bounded cells
whose intersection is their common segment and whose bounded local sides are opposite.
Its conclusion includes the ambient exterior extension, not merely a pasted disk map.
That child's exterior-annulus proof remains open; the present statement does not
replace it by an assumption on the input polygon or by a closed-set pasting argument.

3. Consecutive collinear nonzero edges cannot reverse direction: their interiors would
overlap, contradicting the edge-intersection condition. Thus the intervening vertex is
between its neighbours and deleting it preserves both the image and simplicity. A
simple closed polygon cannot lie entirely on a line, since closing it would retrace an
interval. Repeated deletion therefore leaves at least three vertices. Three remaining
vertices are noncollinear. Their triangle is a convex body with nonempty interior;
`mathlib.gauge_convex_body_unit_ball_g10` supplies the ambient circle equivalence,
the bounded and unbounded complementary components, their frontiers and the bounded
closure. The local two sides of an edge give the triangle crossing assertion; step 1
gives every prescribed boundary extension.

4. Induct on the number of nonredundant vertices, retaining every asserted conclusion
including the one-crossing criterion in the induction hypothesis. The corrected
`topo.cairns_polygon_admissible_diagonal_g2` supplies a diagonal `d` with interior
disjoint from the polygon and its particular exterior accessibility path. The two
cyclic arcs closed by `d` are smaller simple polygons. Apply the induction hypothesis,
after deleting any redundant vertices, to obtain their bounded closed cells `D₁,D₂`.

5. The supplied accessibility path crosses one incident polygon edge once before its
endpoint in `d°`, approaches that endpoint transversely to `d`, and otherwise stays
on one side of `d`. It starts outside a common enclosing rectangle. Before its first
meeting with `d` it crosses exactly one smaller polygon once and never meets the other.
The smaller-polygon crossing criterion therefore puts its final pre-diagonal points
inside one and outside the other. A separate short transverse segment through the
diagonal endpoint identifies the bounded local half-disks. These are opposite for
the two smaller polygons; the side labels persist along the connected open diagonal.

6. Each open complementary boundary arc is connected and disjoint from the other
smaller polygon. If it were inside that polygon, the other's connected unbounded
component would be in its exterior, giving containment of the bounded closed cells.
This contradicts their opposite local bounded sides. Thus both arcs are exterior to
the other polygon. Each connected cell interior then lies in the other's exterior,
because it contains points on the appropriate side of the diagonal. Consequently
`D₁ ∩ D₂ = d`, with no appeal to an arbitrary-curve separation theorem.

7. Apply the named finite opposite-cell amalgamation, whose hypotheses have now all
been verified. Its outer boundary is the original polygon. It gives the ambient
homeomorphism, precisely the two components with that common frontier, the bounded
closure `D₁ ∪ D₂`, and all prescribed boundary extensions. This completes the induction
relative to the named exterior-amalgamation prerequisite. Normalize the image circle
to the unit circle by a plane similarity.

8. At the unique edge-interior crossing, choose a disk meeting the polygon only in
that edge. Its two connected open half-disks lie in different global components:
the ambient circle map and the common-frontier assertion ensure that both components
meet the disk and each half-disk has one constant label. The determinant sign condition
places the incoming and outgoing path pieces on opposite sides. Each remaining path
piece is connected and disjoint from the polygon, so its endpoint retains that label.
The finite affine subdivision supplies exactly the polygonal path required here.
Deleting a collinear vertex changes no boundary point or crossing conclusion; step 3
also proves the universally quantified single-deletion conclusion below.

Edge cases: fewer than three vertices, repeated vertices, zero edges, adjacent overlaps
and nonadjacent intersections fail `IsSimpleClosedPolygon`. Collinear triangles likewise
fail simplicity, so deletion never produces a genuine two-vertex simple polygon. The
crossing parameter is interior, both local sides are strict, and the path is injective.
No orientation restriction is imposed on the prescribed boundary homeomorphism.
-/
theorem cairns_simple_polygon_schoenflies {n : ℕ} (p : Polygon ℂ (n + 1))
    (hp : IsSimpleClosedPolygon p) :
    let c : Set ℂ := p.boundary ℝ
    ∃ Q E : Set ℂ,
      Q.Nonempty ∧ E.Nonempty ∧ Q ≠ E ∧ Q ∪ E = cᶜ ∧ Disjoint Q E ∧
      (fun z : ℂ ↦ connectedComponentIn cᶜ z) '' cᶜ = {Q, E} ∧
      IsConnected Q ∧ IsConnected E ∧ IsOpen Q ∧ IsOpen E ∧
      Bornology.IsBounded Q ∧ ¬Bornology.IsBounded E ∧
      frontier Q = c ∧ frontier E = c ∧ closure Q = Q ∪ c ∧
      (∃ H : ℂ ≃ₜ ℂ, H '' c = Metric.sphere (0 : ℂ) 1) ∧
      (∀ b : {z : ℂ // z ∈ c} ≃ₜ Circle,
        ∃ F : {z : ℂ // z ∈ closure Q} ≃ₜ
            {z : ℂ // z ∈ Metric.closedBall (0 : ℂ) 1},
          ∀ x : {z : ℂ // z ∈ c}, ∀ hx : x.val ∈ closure Q,
            (F ⟨x.val, hx⟩).val = (b x : ℂ)) ∧
      (∀ f : ℝ → ℂ, IsSimplePolygonalPath f → CrossesPolygonOnce p f →
        (f 0 ∈ Q ∧ f 1 ∈ E) ∨ (f 0 ∈ E ∧ f 1 ∈ Q)) ∧
      (∀ i : Fin (n + 1),
        Collinear ℝ ({p ((finRotate (n + 1)).symm i), p i,
          p (finRotate (n + 1) i)} : Set ℂ) →
        (deletePolygonVertex p i).boundary ℝ = c ∧
          IsSimpleClosedPolygon (deletePolygonVertex p i)) := by
  classical
  intro c
  have hcollinear (i : Fin (n + 1))
      (hcol : Collinear ℝ ({p ((finRotate (n + 1)).symm i), p i,
        p (finRotate (n + 1) i)} : Set ℂ)) :
      p i ∈ openSegment ℝ (p ((finRotate (n + 1)).symm i))
        (p (finRotate (n + 1) i)) ∧
      segment ℝ (p ((finRotate (n + 1)).symm i)) (p i) ∪
          segment ℝ (p i) (p (finRotate (n + 1) i)) =
        segment ℝ (p ((finRotate (n + 1)).symm i)) (p (finRotate (n + 1) i)) := by
    have hn := hp.1
    have hrot (j : Fin (n + 1)) : finRotate (n + 1) j ≠ j := by
      intro heq
      by_cases hj : j = Fin.last n
      · subst j
        have hv := congrArg Fin.val heq
        simp only [finRotate_last, Fin.val_zero, Fin.val_last] at hv
        omega
      · have hv := congrArg Fin.val heq
        rw [coe_finRotate_of_ne_last hj] at hv
        omega
    have hrot2 : finRotate (n + 1) (finRotate (n + 1) i) ≠ i := by
      intro heq
      by_cases hi : i = Fin.last n
      · subst i
        have hv := congrArg Fin.val heq
        simp only [finRotate_last, finRotate_apply_zero, Fin.val_last] at hv
        change 1 % (n + 1) = n at hv
        rw [Nat.mod_eq_of_lt (by omega : 1 < n + 1)] at hv
        omega
      · by_cases hj : finRotate (n + 1) i = Fin.last n
        · have hv := congrArg Fin.val heq
          rw [hj, finRotate_last] at hv
          simp only [Fin.val_zero] at hv
          have hvj := congrArg Fin.val hj
          rw [coe_finRotate_of_ne_last hi] at hvj
          simp only [Fin.val_last] at hvj
          omega
        · have hv := congrArg Fin.val heq
          rw [coe_finRotate_of_ne_last hj, coe_finRotate_of_ne_last hi] at hv
          omega
    have hprev : (finRotate (n + 1)).symm i ≠ i := by
      intro heq
      have h := congrArg (finRotate (n + 1)) heq
      simp only [Equiv.apply_symm_apply] at h
      exact hrot i h.symm
    have hprevnext : (finRotate (n + 1)).symm i ≠ finRotate (n + 1) i := by
      intro heq
      have h := congrArg (finRotate (n + 1)) heq
      simp only [Equiv.apply_symm_apply] at h
      exact hrot2 h.symm
    apply collinear_segments_meeting_only_at_joint _ _ _
      (fun h ↦ hprev (hp.2.1 h)) (fun h ↦ hrot i (hp.2.1 h).symm) hcol
    intro z hz
    have hbound := hp.2.2.2 ((finRotate (n + 1)).symm i) i hprev
    simp only [Polygon.edgeSet, affineSegment_eq_segment, Equiv.apply_symm_apply] at hbound
    obtain ⟨k, ⟨hk₁, hk₂⟩, hkz⟩ := hbound hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hk₁ hk₂
    rcases hk₁ with rfl | rfl
    · exact (hk₂.elim hprev hprevnext).elim
    · exact hkz.symm
  have hambient : ∃ H : ℂ ≃ₜ ℂ, H '' c = Metric.sphere (0 : ℂ) 1 := by
    simpa only [IsSimpleClosedPolygon] using cairns_simple_polygon_ambient_circle p hp
  obtain ⟨H, hH⟩ := hambient
  obtain ⟨Q, E, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12,
    h13, h14, h15, hboundary⟩ := ambient_circle_regions c H hH
  refine ⟨Q, E, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12,
    h13, h14, h15, ⟨H, hH⟩, hboundary, ?_, ?_⟩
  · intro f hf hcross
    obtain ⟨i, t, ht, hinter, hedge, δ, hδ, hδt, hδ1, hsign⟩ := hcross
    have havoid : ∀ s ∈ Icc (0 : ℝ) 1, s ≠ t → f s ∉ c := by
      intro s hs hst hmem
      have heq : f s = f t := by
        have : f s ∈ ({f t} : Set ℂ) := hinter ▸ ⟨⟨s, hs, rfl⟩, hmem⟩
        exact Set.mem_singleton_iff.mp this
      exact hst (hf.2.1 hs ⟨ht.1.le, ht.2.le⟩ heq)
    have hleft : IsPreconnected (f '' Ico (0 : ℝ) t) :=
      isPreconnected_Ico.image f (hf.1.mono (by
        intro s hs
        exact ⟨hs.1, hs.2.le.trans ht.2.le⟩))
    have hright : IsPreconnected (f '' Ioc t (1 : ℝ)) :=
      isPreconnected_Ioc.image f (hf.1.mono (by
        intro s hs
        exact ⟨ht.1.le.trans hs.1.le, hs.2⟩))
    have hleftsub : f '' Ico (0 : ℝ) t ⊆ Q ∪ E := by
      rw [h4]
      rintro _ ⟨s, hs, rfl⟩
      exact havoid s ⟨hs.1, hs.2.le.trans ht.2.le⟩ hs.2.ne
    have hrightsub : f '' Ioc t (1 : ℝ) ⊆ Q ∪ E := by
      rw [h4]
      rintro _ ⟨s, hs, rfl⟩
      exact havoid s ⟨ht.1.le.trans hs.1.le, hs.2⟩ hs.1.ne'
    have hlocal : ∃ s ∈ Ico (0 : ℝ) t, ∃ u ∈ Ioc t (1 : ℝ),
        (f s ∈ Q ∧ f u ∈ E) ∨ (f s ∈ E ∧ f u ∈ Q) := by
      obtain ⟨ε, hε, hball⟩ := polygon_edge_local_line p hp.2.2.1 hp.2.2.2 i hedge
      let L : ℂ →ₗ[ℝ] ℝ :=
        Complex.imLm.comp (LinearMap.mulLeft ℝ (star (p (finRotate (n + 1) i) - p i)))
      have hL (z : ℂ) :
          (star (p (finRotate (n + 1) i) - p i) * (z - p i)).im = L z - L (p i) := by
        simp only [L, LinearMap.comp_apply, LinearMap.mulLeft_apply,
          mul_sub, Complex.sub_im]
        rfl
      let P := Metric.ball (f t) ε ∩ {z : ℂ | L (p i) < L z}
      let N := Metric.ball (f t) ε ∩ {z : ℂ | L z < L (p i)}
      have hP : IsPreconnected P :=
        ((convex_ball (f t) ε).inter (convex_halfSpace_gt L.isLinear (L (p i)))).isPreconnected
      have hN : IsPreconnected N :=
        ((convex_ball (f t) ε).inter (convex_halfSpace_lt L.isLinear (L (p i)))).isPreconnected
      have hsides : Metric.ball (f t) ε \ c = P ∪ N := by
        ext z
        constructor
        · rintro ⟨hzb, hzc⟩
          have hne : L z - L (p i) ≠ 0 := by
            rw [← hL]
            exact fun hz ↦ hzc ((hball z hzb).mpr hz)
          rcases lt_or_gt_of_ne (sub_ne_zero.mp hne) with hn | hp
          · exact Or.inr ⟨hzb, hn⟩
          · exact Or.inl ⟨hzb, hp⟩
        · rintro (⟨hzb, hp⟩ | ⟨hzb, hn⟩)
          · refine ⟨hzb, ?_⟩
            intro hzc
            have hz := (hball z hzb).mp hzc
            rw [hL] at hz
            exact (sub_pos.mpr hp).ne' hz
          · refine ⟨hzb, ?_⟩
            intro hzc
            have hz := (hball z hzb).mp hzc
            rw [hL] at hz
            exact (sub_neg.mpr hn).ne hz
      have hftc : f t ∈ c := by
        exact mem_iUnion.mpr ⟨i, by
          simpa only [Polygon.edgeSet, affineSegment_eq_segment] using
            openSegment_subset_segment ℝ _ _ hedge⟩
      have hlabels := two_local_sides_separation h9 h10 h5 h4
        (frontier_subset_closure (h13.symm ▸ hftc))
        (frontier_subset_closure (h14.symm ▸ hftc))
        Metric.isOpen_ball (Metric.mem_ball_self hε) hP hN hsides
      have hft : ContinuousAt f t := hf.1.continuousAt (Icc_mem_nhds ht.1 ht.2)
      obtain ⟨ρ, hρ, hfρ⟩ := Metric.continuousAt_iff.mp hft ε hε
      let η := min δ ρ / 2
      have hη : 0 < η := half_pos (lt_min hδ hρ)
      have hηδ : η < δ := (half_lt_self (lt_min hδ hρ)).trans_le (min_le_left _ _)
      have hηρ : η < ρ := (half_lt_self (lt_min hδ hρ)).trans_le (min_le_right _ _)
      have hs : t - η ∈ Ico (0 : ℝ) t := ⟨by linarith, by linarith⟩
      have hu : t + η ∈ Ioc t (1 : ℝ) := ⟨by linarith, by linarith⟩
      have hsball : f (t - η) ∈ Metric.ball (f t) ε := by
        apply hfρ
        rw [Real.dist_eq]
        have habs : |t - η - t| = η := by rw [show t - η - t = -η by ring, abs_neg, abs_of_pos hη]
        rwa [habs]
      have huball : f (t + η) ∈ Metric.ball (f t) ε := by
        apply hfρ
        rw [Real.dist_eq]
        have habs : |t + η - t| = η := by rw [show t + η - t = η by ring, abs_of_pos hη]
        rwa [habs]
      have hprod := hsign (t - η) ⟨by linarith, by linarith⟩
        (t + η) ⟨by linarith, by linarith⟩
      rw [hL, hL] at hprod
      refine ⟨t - η, hs, t + η, hu, ?_⟩
      rcases mul_neg_iff.mp hprod with ⟨hspos, huneg⟩ | ⟨hsneg, hupos⟩
      · have hsP : f (t - η) ∈ P := ⟨hsball, sub_pos.mp hspos⟩
        have huN : f (t + η) ∈ N := ⟨huball, sub_neg.mp huneg⟩
        exact hlabels.elim (fun h ↦ Or.inl ⟨h.1 hsP, h.2 huN⟩)
          (fun h ↦ Or.inr ⟨h.1 hsP, h.2 huN⟩)
      · have hsN : f (t - η) ∈ N := ⟨hsball, sub_neg.mp hsneg⟩
        have huP : f (t + η) ∈ P := ⟨huball, sub_pos.mp hupos⟩
        exact hlabels.elim (fun h ↦ Or.inr ⟨h.2 hsN, h.1 huP⟩)
          (fun h ↦ Or.inl ⟨h.2 hsN, h.1 huP⟩)
    obtain ⟨s, hs, u, hu, hsu⟩ := hlocal
    have h0 : f 0 ∈ f '' Ico (0 : ℝ) t := ⟨0, ⟨le_rfl, ht.1⟩, rfl⟩
    have h1' : f 1 ∈ f '' Ioc t (1 : ℝ) := ⟨1, ⟨ht.2, le_rfl⟩, rfl⟩
    have hsm : f s ∈ f '' Ico (0 : ℝ) t := ⟨s, hs, rfl⟩
    have hum : f u ∈ f '' Ioc t (1 : ℝ) := ⟨u, hu, rfl⟩
    rcases hleft.subset_or_subset h9 h10 h5 hleftsub with hL | hL <;>
      rcases hright.subset_or_subset h9 h10 h5 hrightsub with hR | hR
    · rcases hsu with hsu | hsu
      · exact (Set.disjoint_left.mp h5 (hR hum) hsu.2).elim
      · exact (Set.disjoint_left.mp h5 (hL hsm) hsu.1).elim
    · exact Or.inl ⟨hL h0, hR h1'⟩
    · exact Or.inr ⟨hL h0, hR h1'⟩
    · rcases hsu with hsu | hsu
      · exact (Set.disjoint_left.mp h5 hsu.1 (hL hsm)).elim
      · exact (Set.disjoint_left.mp h5 hsu.2 (hR hum)).elim
  · intro i hcol
    refine ⟨?_, ?_⟩
    · exact polygon_boundary_delete_vertex (by have := hp.1; omega) p i
        (hcollinear i hcol).2
    · cases n with
      | zero => have := hp.1; omega
      | succ n =>
        exact polygon_delete_vertex_simplicity p i hp.1 hp.2.1 hp.2.2.2
          (hcollinear i hcol).1 (hcollinear i hcol).2

end HolomorphicAnosov

