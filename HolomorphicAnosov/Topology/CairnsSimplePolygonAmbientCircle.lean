import HolomorphicAnosov.Topology.CairnsTriangleAmbientCircleG6
import HolomorphicAnosov.Topology.CairnsCyclicSplitBoundariesG6
import HolomorphicAnosov.Topology.CairnsPolygonBoundaryCircleG6
import HolomorphicAnosov.Topology.CairnsCellsDisjointOfOutsideWitnessesG6
import HolomorphicAnosov.Topology.CairnsCircleMinusSegmentG6
import HolomorphicAnosov.Topology.CairnsLocalLineSidesG6
import HolomorphicAnosov.Topology.CairnsNestedCellsRegionsG6
import HolomorphicAnosov.Topology.CairnsPiecewiseAccessCrossingG6
import HolomorphicAnosov.Topology.AmbientCircleRegions
import HolomorphicAnosov.Topology.PolygonDeleteVertexBoundary
import HolomorphicAnosov.Topology.PolygonDeleteVertexSimplicity
import HolomorphicAnosov.Topology.CollinearSegmentsJoint
import HolomorphicAnosov.Topology.CairnsPolygonAdmissibleDiagonal
import HolomorphicAnosov.Topology.CairnsPolygonOppositeCellsAmalgamation
import Mathlib.Geometry.Polygon.Basic
import Mathlib.Analysis.Complex.Circle

/-!
# Ambient circle map for a finite simple polygon

Source: S. S. Cairns, *An Elementary Proof of the Jordan–Schoenflies Theorem*
(1951), preliminary 2(A,B), Theorem 2.1 and Lemma 2.1, printed pp. 860–861
(literature/cairns-jordan-schoenflies-1951.pdf, physical pp. 2–3).

This module isolates the ambient-map induction used by the finite polygon theorem.
The finite diagonal lemma supplies two smaller polygons and an accessible transverse
path; the opposite-cell amalgamation lemma then pastes their bounded cells and the
finite exterior annulus.  The statement intentionally contains only the polygon
simplicity hypotheses and the ambient conclusion, so it can be reused by the
crossing and prescribed-boundary consumers.
-/

noncomputable section
open Set
namespace HolomorphicAnosov
open Metric

/-- Every finite simple closed polygon has an ambient plane homeomorphism carrying
its boundary onto the unit circle.

Source: Cairns (1951), preliminary 2(A,B), Theorem 2.1, pp.860–861.
Induct on the number of vertices. A collinear corner lies between its neighbors:
a reversal would overlap two edges. Delete it without changing the boundary.
For three remaining vertices affine independence gives a nondegenerate triangle;
its convex hull has the polygon as frontier and the gauge map sends it to a circle.

For more vertices the admissible diagonal produces two smaller simple cyclic
polygons. Induction supplies ambient circle maps and hence their bounded cells
and unbounded exteriors. Cyclic edge bookkeeping identifies their boundary
intersection as the diagonal and their outer boundary as the original polygon.
The remaining arc of each smaller boundary is connected, with closure equal to
the boundary minus the open diagonal, by transporting the directed-circle-arc
identities through the circle chart.

The cells cannot be nested. If the second cell lies inside the first, its
intersection with the first exterior is empty, and the two boundaries have the
same half-ball labeling at their common straight edge. Consequently the first
cell minus the second closed cell, and the union of the second cell, the first
exterior and the open diagonal, are disjoint open regions covering the original
polygon complement. Each accumulates at every original boundary point: off the
seam this follows from the smaller frontiers, and the arc-closure identity adds
the seam endpoints. The first region is bounded, so the connected unbounded
component belongs to the second. But the admissible access path starts in that
component and ends on the open diagonal, crossing the original polygon exactly
once and transversely. Rescale its piecewise affine parameter to the unit interval;
the nonzero transverse determinant changes sign. The two-region crossing lemma
places the endpoints in different regions, a contradiction. Interchanging the
cells excludes the other nesting.

Failure of containment supplies an interior point in the other's exterior:
an open cell touching the other boundary would meet that exterior by frontier
density. The connected nonseam boundary arcs therefore lie in the opposite
exteriors, as does each cell interior; otherwise boundedness and exterior
connectedness would contradict these two outside witnesses. Thus the closed
cells meet exactly on the diagonal. Their local half-ball labels must now be
opposite, because their interiors are disjoint. Normalize the perpendicular
complex direction to give the exact unit-normal coordinates.

Apply the named finite opposite-cell ambient amalgamation theorem. A direct
concatenation of the polygon edges gives its prescribed boundary circle map.
The resulting ambient map agrees with this surjective map on the original
boundary and therefore sends that boundary exactly onto the unit circle. This
proof uses the separate amalgamation prerequisite for the exterior extension.
-/
theorem cairns_simple_polygon_ambient_circle {n : ℕ} (p : Polygon ℂ (n + 1))
    (hp : 3 ≤ n + 1 ∧ Function.Injective p.vertices ∧ p.HasNondegenerateEdges ∧
      ∀ i j : Fin (n + 1), i ≠ j →
        p.edgeSet ℝ i ∩ p.edgeSet ℝ j ⊆
          p.vertices '' ({i, finRotate (n + 1) i} ∩ {j, finRotate (n + 1) j})) :
    ∃ H : ℂ ≃ₜ ℂ, H '' p.boundary ℝ = Metric.sphere (0 : ℂ) 1 := by
  classical
  induction n using Nat.strong_induction_on with
  | h n ih =>
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
    by_cases hcorner : ∃ i : Fin (n + 1),
        Collinear ℝ ({p ((finRotate (n + 1)).symm i), p i,
          p (finRotate (n + 1) i)} : Set ℂ)
    · obtain ⟨i, hi⟩ := hcorner
      obtain ⟨hb, hj⟩ := hcollinear i hi
      cases n with
      | zero => omega
      | succ m =>
        let q : Polygon ℂ (m + 1) := ⟨fun j ↦ p (i.succAbove j)⟩
        have hq := polygon_delete_vertex_simplicity p i hp.1 hp.2.1 hp.2.2.2 hb hj
        have hboundary := polygon_boundary_delete_vertex (by omega : 0 < m + 1) p i hj
        obtain ⟨H, hH⟩ := ih m (by omega) q hq
        exact ⟨H, hboundary ▸ hH⟩
    · have hcorners : ∀ i : Fin (n + 1),
          ¬Collinear ℝ ({p ((finRotate (n + 1)).symm i), p i,
            p (finRotate (n + 1) i)} : Set ℂ) := not_exists.mp hcorner
      by_cases hn : n = 2
      · subst n
        apply cairns_triangle_ambient_circle_g6 p
        apply affineIndependent_iff_not_collinear.mpr
        have h := hcorners 1
        have hr : range p.vertices = ({p 0, p 1, p 2} : Set ℂ) := by
          ext z
          simp only [mem_range, mem_insert_iff, mem_singleton_iff]
          constructor
          · rintro ⟨i, rfl⟩
            fin_cases i <;> simp
          · rintro (rfl | rfl | rfl)
            · exact ⟨0, rfl⟩
            · exact ⟨1, rfl⟩
            · exact ⟨2, rfl⟩
        rw [hr]
        exact h
      · let e := Complex.equivRealProdLm
        let q : Polygon (ℝ × ℝ) (n + 1) := ⟨fun i ↦ e (p i)⟩
        have hqinj : Function.Injective q.vertices := e.injective.comp hp.2.1
        have hqedges : q.HasNondegenerateEdges := fun i h ↦ hp.2.2.1 i (e.injective h)
        have hedge (i : Fin (n + 1)) : q.edgeSet ℝ i = e '' p.edgeSet ℝ i := by
          simp only [Polygon.edgeSet, affineSegment_eq_segment]
          exact (image_segment ℝ e.toAffineMap (p i) (p (finRotate (n + 1) i))).symm
        have hqsimple : Topology.IsCairnsSimplePolygon q := by
          refine ⟨hp.1, hqinj, hqedges, ?_⟩
          intro i j hij x
          constructor
          · rintro ⟨hxi, hxj⟩
            rw [hedge] at hxi hxj
            obtain ⟨z, hzi, rfl⟩ := hxi
            obtain ⟨w, hwj, hew⟩ := hxj
            have hwz : w = z := e.injective hew
            subst w
            obtain ⟨k, ⟨hki, hkj⟩, hkz⟩ := hp.2.2.2 i j hij ⟨hzi, hwj⟩
            simp only [mem_insert_iff, mem_singleton_iff] at hki hkj
            rcases hki with rfl | rfl
            · rcases hkj with h | h
              · exact (hij h).elim
              · exact Or.inl ⟨h, congrArg e hkz.symm⟩
            · rcases hkj with h | h
              · exact Or.inr ⟨h.symm, by simpa only [← h] using congrArg e hkz.symm⟩
              · exact (hij ((finRotate (n + 1)).injective h)).elim
          · rintro (⟨hij, rfl⟩ | ⟨hji, rfl⟩)
            · exact ⟨left_mem_affineSegment ℝ _ _, hij ▸ right_mem_affineSegment ℝ _ _⟩
            · exact ⟨hji ▸ right_mem_affineSegment ℝ _ _, left_mem_affineSegment ℝ _ _⟩
        have hqcorners : ∀ i : Fin (n + 1),
            ¬Collinear ℝ ({q i, q (finRotate (n + 1) i),
              q (finRotate (n + 1) (finRotate (n + 1) i))} : Set (ℝ × ℝ)) := by
          intro i
          have h := hcorners (finRotate (n + 1) i)
          simp only [Equiv.symm_apply_apply] at h
          have ha := affineIndependent_iff_not_collinear_set.mpr h
          have ham := ha.map' e.toAffineMap e.injective
          apply affineIndependent_iff_not_collinear_set.mp
          convert ham using 1
          funext j
          fin_cases j <;> rfl
        obtain ⟨Uinf, hUinf, hUnbounded, hUnique, i, j, a, b,
          hij, hjnext, hinext, ha, hb, hab, hjiter, hdiag, haccess,
          hqa, haless, hqb, hbless⟩ :=
          Topology.cairns_polygon_admissible_diagonal q (by omega) hqsimple hqcorners
        have hcomplex_simple (m : ℕ) (r : Polygon (ℝ × ℝ) (m + 1))
            (hr : Topology.IsCairnsSimplePolygon r) :
            let r' : Polygon ℂ (m + 1) := ⟨fun k ↦ e.symm (r k)⟩
            3 ≤ m + 1 ∧ Function.Injective r'.vertices ∧ r'.HasNondegenerateEdges ∧
              ∀ k l : Fin (m + 1), k ≠ l →
                r'.edgeSet ℝ k ∩ r'.edgeSet ℝ l ⊆
                  r'.vertices '' ({k, finRotate (m + 1) k} ∩ {l, finRotate (m + 1) l}) := by
          intro r'
          refine ⟨hr.1, e.symm.injective.comp hr.2.1,
            fun k h ↦ hr.2.2.1 k (e.symm.injective h), ?_⟩
          intro k l hkl z hz
          have hmem (k : Fin (m + 1)) (hz : z ∈ r'.edgeSet ℝ k) :
              e z ∈ r.edgeSet ℝ k := by
            have he : e '' r'.edgeSet ℝ k = r.edgeSet ℝ k := by
              simp only [Polygon.edgeSet, affineSegment_eq_segment]
              change e.toAffineMap '' segment ℝ (r' k) (r' (finRotate (m + 1) k)) = _
              rw [image_segment ℝ e.toAffineMap]
              change segment ℝ (e (e.symm (r k)))
                (e (e.symm (r (finRotate (m + 1) k)))) = _
              simp only [LinearEquiv.apply_symm_apply]
            rw [← he]
            exact mem_image_of_mem e hz
          rcases (hr.2.2.2 k l hkl (e z)).mp ⟨hmem k hz.1, hmem l hz.2⟩ with
            ⟨hkl', hz⟩ | ⟨hlk', hz⟩
          · refine ⟨k, ⟨by simp, by simp [hkl']⟩, ?_⟩
            exact (congrArg e.symm hz).symm.trans (e.symm_apply_apply z)
          · refine ⟨l, ⟨by simp [hlk'], by simp⟩, ?_⟩
            exact (congrArg e.symm hz).symm.trans (e.symm_apply_apply z)
        let A : Polygon ℂ (a + 1) := ⟨fun r ↦ p ((finRotate (n + 1))^[r.val] i)⟩
        let B : Polygon ℂ (b + 1) := ⟨fun r ↦ p ((finRotate (n + 1))^[r.val] j)⟩
        have hAc := hcomplex_simple a (Topology.cairnsCyclicArcPolygon q i a) hqa
        have hBc := hcomplex_simple b (Topology.cairnsCyclicArcPolygon q j b) hqb
        simp only [Topology.cairnsCyclicArcPolygon, q, LinearEquiv.symm_apply_apply] at hAc hBc
        obtain ⟨Ha, hHa⟩ := ih a (by omega) A hAc
        obtain ⟨Hb, hHb⟩ := ih b (by omega) B hBc
        have hdiagC : Disjoint (openSegment ℝ (p i) (p j)) (p.boundary ℝ) := by
          apply disjoint_left.mpr
          intro z hz hpz
          apply disjoint_left.mp hdiag
          · have he := image_openSegment ℝ e.toAffineMap (p i) (p j)
            apply he ▸ mem_image_of_mem e hz
          · obtain ⟨k, hk⟩ := mem_iUnion.mp hpz
            apply mem_iUnion.mpr
            exact ⟨k, hedge k ▸ mem_image_of_mem e hk⟩
        obtain ⟨hAB, houter⟩ := cairns_cyclic_split_boundaries_g6 p hp.2.1 hp.2.2.2
          i j a b ha hb hab hjiter hdiagC
        have hcircle := cairns_polygon_boundary_circle_g6 p hp.1 hp.2.1 hp.2.2.2
        obtain ⟨γ, hγ, hγrange⟩ := hcircle
        let β : p.boundary ℝ ≃ₜ Metric.sphere (0 : ℂ) 1 :=
          (hγ.toHomeomorph.trans (Homeomorph.setCongr hγrange)).symm
        obtain ⟨Ca, Ea, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, ha9, ha10,
          ha11, ha12, ha13, ha14, ha15, haBoundary⟩ := ambient_circle_regions _ Ha hHa
        obtain ⟨Cb, Eb, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10,
          hb11, hb12, hb13, hb14, hb15, hbBoundary⟩ := ambient_circle_regions _ Hb hHb
        have hpij : p i ≠ p j := fun h ↦ hij (hp.2.1 h)
        let D := segment ℝ (p i) (p j)
        let d := openSegment ℝ (p i) (p j)
        have hDab : D ⊆ A.boundary ℝ ∩ B.boundary ℝ := fun x hx ↦ hAB.symm ▸ hx
        have hda : d ⊆ A.boundary ℝ := fun x hx ↦ (hDab (openSegment_subset_segment ℝ _ _ hx)).1
        have hdb : d ⊆ B.boundary ℝ := fun x hx ↦ (hDab (openSegment_subset_segment ℝ _ _ hx)).2
        have hCa : A.boundary ℝ ⊆ closure Ca := ha13 ▸ frontier_subset_closure
        have hEa : A.boundary ℝ ⊆ closure Ea := ha14 ▸ frontier_subset_closure
        have hCb : B.boundary ℝ ⊆ closure Cb := hb13 ▸ frontier_subset_closure
        have hEb : B.boundary ℝ ⊆ closure Eb := hb14 ▸ frontier_subset_closure
        let βa : A.boundary ℝ ≃ₜ sphere (0:ℂ) 1 :=
          (Ha.image _).trans (Homeomorph.setCongr hHa)
        let βb : B.boundary ℝ ≃ₜ sphere (0:ℂ) 1 :=
          (Hb.image _).trans (Homeomorph.setCongr hHb)
        obtain ⟨harca,hclArca⟩ := cairns_circle_minus_segment_data_g6
          (A.boundary ℝ) βa (p i) (p j) hpij (fun x hx ↦ (hDab hx).1)
        obtain ⟨harcb,hclArcb⟩ := cairns_circle_minus_segment_data_g6
          (B.boundary ℝ) βb (p i) (p j) hpij (fun x hx ↦ (hDab hx).2)
        have hreturn : (finRotate (n+1))^[b] j = i := by
          have hiter (m : ℕ) (hm : m < n+1) (r : Fin (n+1)) :
              (finRotate (n+1))^[m] r = r + (⟨m,hm⟩ : Fin (n+1)) :=
            (congrFun (finCycle_eq_finRotate_iterate (k := ⟨m,hm⟩)) r).symm
          rw [hiter b (by omega), hjiter, hiter a (by omega), add_assoc]
          have hz : (⟨a,by omega⟩ : Fin (n+1)) + ⟨b,by omega⟩ = 0 := by
            apply Fin.ext
            change (a+b)%(n+1)=0
            rw [hab,Nat.mod_self]
          rw [hz,add_zero]
        have haend : A (Fin.last a) = p j := congrArg p hjiter.symm
        have hbend : B (Fin.last b) = p i := congrArg p hreturn
        have ha0 : A 0 = p i := rfl
        have hb0 : B 0 = p j := rfl
        let L : ℂ →ₗ[ℝ] ℝ := Complex.imLm.comp (LinearMap.mulLeft ℝ (star (p j-p i)))
        have hL (z : ℂ) : (star (p j-p i)*(z-p i)).im = L z-L (p i) := by
          simp only [L,LinearMap.comp_apply,LinearMap.mulLeft_apply,mul_sub,Complex.sub_im]
          rfl
        have hlocal (x : ℂ) (hx : x ∈ d) : ∃ ε>0,
            (∀ z ∈ ball x ε, z ∈ A.boundary ℝ ↔ L z=L x) ∧
            (∀ z ∈ ball x ε, z ∈ B.boundary ℝ ↔ L z=L x) ∧
            (∀ z ∈ ball x ε, L z=L x → z ∈ d) := by
          have hxa : x ∈ openSegment ℝ (A (Fin.last a)) (A (finRotate (a+1) (Fin.last a))) := by
            rw [finRotate_last,haend,ha0,openSegment_symm]
            exact hx
          have hxb : x ∈ openSegment ℝ (B (Fin.last b)) (B (finRotate (b+1) (Fin.last b))) := by
            rw [finRotate_last,hbend,hb0]
            exact hx
          obtain ⟨εa,hεa,hla⟩ := polygon_edge_local_line A hAc.2.2.1 hAc.2.2.2 (Fin.last a) hxa
          obtain ⟨εb,hεb,hlb⟩ := polygon_edge_local_line B hBc.2.2.1 hBc.2.2.2 (Fin.last b) hxb
          simp only [finRotate_last,haend,ha0] at hla
          simp only [finRotate_last,hbend,hb0] at hlb
          have hzero : L x=L (p i) := by
            have := (hlb x (mem_ball_self hεb)).mp (hdb hx)
            rw [hL] at this
            exact sub_eq_zero.mp this
          have hrev (z : ℂ) :
              (star (p i-p j)*(z-p j)).im = -(star (p j-p i)*(z-p i)).im := by
            simp only [Complex.mul_im,Complex.sub_re,Complex.sub_im,Complex.star_def,
              Complex.conj_re,Complex.conj_im]
            ring
          have hxne : x ∉ ({p i,p j} : Set ℂ) := by
            rintro (hx' | hx')
            · exact hpij (left_mem_openSegment_iff.mp (hx' ▸ hx))
            · exact hpij (right_mem_openSegment_iff.mp ((mem_singleton_iff.mp hx') ▸ hx))
          obtain ⟨ρ,hρ,hρball⟩ := Metric.mem_nhds_iff.mp
            ((Set.Finite.isClosed (toFinite ({p i,p j} : Set ℂ))).isOpen_compl.mem_nhds hxne)
          refine ⟨min εa (min εb ρ),lt_min hεa (lt_min hεb hρ),?_,?_,?_⟩
          · intro z hz
            rw [hla z (ball_subset_ball (min_le_left _ _) hz),hrev,hL,neg_eq_zero,sub_eq_zero,←hzero]
          · intro z hz
            rw [hlb z (ball_subset_ball ((min_le_right _ _).trans (min_le_left _ _)) hz),hL,sub_eq_zero,←hzero]
          · intro z hz hzx
            have hza : z ∈ A.boundary ℝ := (hla z (ball_subset_ball (min_le_left _ _) hz)).mpr (by
              rw [hrev,hL,hzx,hzero,sub_self,neg_zero])
            have hzb : z ∈ B.boundary ℝ := (hlb z
              (ball_subset_ball ((min_le_right _ _).trans (min_le_left _ _)) hz)).mpr (by
                rw [hL,hzx,hzero,sub_self])
            have hzD : z ∈ D := by
              change z ∈ segment ℝ (p i) (p j)
              exact hAB ▸ ⟨hza,hzb⟩
            have hzends := hρball (ball_subset_ball ((min_le_right _ _).trans (min_le_right _ _)) hz)
            have hseg : segment ℝ (p i) (p j) = insert (p i) (insert (p j) d) :=
              (insert_endpoints_openSegment ℝ (p i) (p j)).symm
            rw [show D = segment ℝ (p i) (p j) from rfl,hseg] at hzD
            rcases hzD with hzD | hzD | hzD
            · exact (hzends (Or.inl hzD)).elim
            · exact (hzends (Or.inr hzD)).elim
            · exact hzD
        have hboundary : e '' p.boundary ℝ = q.boundary ℝ := by
          apply subset_antisymm
          · rintro z ⟨w,hw,rfl⟩
            obtain ⟨k,hk⟩ := mem_iUnion.mp hw
            exact mem_iUnion.mpr ⟨k,hedge k ▸ mem_image_of_mem e hk⟩
          · intro z hz
            obtain ⟨k,hk⟩ := mem_iUnion.mp hz
            rw [hedge] at hk
            obtain ⟨w,hw,rfl⟩ := hk
            exact ⟨w,mem_iUnion.mpr ⟨k,hw⟩,rfl⟩
        let U := e.symm '' Uinf
        have hUconn : IsPreconnected U := by
          obtain ⟨u,hu,hUeq⟩ := hUinf
          exact (hUeq ▸ isPreconnected_connectedComponentIn).image e.symm e.symm.toContinuousLinearEquiv.continuous.continuousOn
        have hUunbounded : ¬Bornology.IsBounded U := by
          intro hbounded
          have heU : e '' U = Uinf := by
            simp only [U,image_image,e.apply_symm_apply,image_id']
          have hbnd := e.toContinuousLinearMap.lipschitzWith.isBounded_image hbounded
          change Bornology.IsBounded (e '' U) at hbnd
          rw [heU] at hbnd
          exact hUnbounded hbnd
        have hUsub : U ⊆ (p.boundary ℝ)ᶜ := by
          rintro z ⟨w,hw,rfl⟩ hz
          obtain ⟨u,hu,hUeq⟩ := hUinf
          have hwp : w ∉ q.boundary ℝ := connectedComponentIn_subset _ _ (hUeq ▸ hw)
          apply hwp
          rw [←hboundary]
          exact ⟨e.symm w,hz,e.apply_symm_apply w⟩
        have haccess_cross (Q E : Set ℂ) (hoQ : IsOpen Q) (hoE : IsOpen E)
            (hdis : Disjoint Q E) (hcover : Q ∪ E = (p.boundary ℝ)ᶜ)
            (hclQ : p.boundary ℝ ⊆ closure Q) (hclE : p.boundary ℝ ⊆ closure E) :
            ∃ u ∈ U, ∃ v ∈ d, (u ∈ Q ∧ v ∈ E) ∨ (u ∈ E ∧ v ∈ Q) := by
          let x := midpoint ℝ (p i) (p j)
          have hx : x ∈ d := midpoint_mem_openSegment _ _
          have hex : e x ∈ openSegment ℝ (q i) (q j) := by
            have he := image_openSegment ℝ e.toAffineMap (p i) (p j)
            exact he ▸ mem_image_of_mem e hx
          obtain ⟨m,w,γ,hm,hwne,hγ,hinj,hγ0,hγm,haff,r,s,k,hs0,hs1,hcross,htrans,hunique⟩ :=
            haccess (e x) hex
          let w' := fun t ↦ e.symm (w t)
          let γ' := fun t ↦ e.symm (γ t)
          have haff' (r : Fin m) (s : ℝ) (hs : s ∈ Icc (0:ℝ) 1) :
              γ' ((r.val:ℝ)+s) = AffineMap.lineMap (w' r.castSucc) (w' r.succ) s := by
            dsimp only [γ',w']
            rw [haff r s hs]
            exact e.symm.toAffineMap.apply_lineMap _ _ _
          have hedge' : γ' ((r.val:ℝ)+s) ∈ openSegment ℝ (p k) (p (finRotate (n+1) k)) := by
            have he : e.symm '' openSegment ℝ (q k) (q (finRotate (n+1) k)) =
                openSegment ℝ (p k) (p (finRotate (n+1) k)) := by
              change e.symm.toAffineMap '' openSegment ℝ (q k) (q (finRotate (n+1) k)) = _
              rw [image_openSegment ℝ e.symm.toAffineMap]
              change openSegment ℝ (e.symm (e (p k))) (e.symm (e (p (finRotate (n+1) k)))) = _
              simp only [e.symm_apply_apply]
            exact he ▸ mem_image_of_mem e.symm hcross
          have htrans' : (star (p (finRotate (n+1) k)-p k)*(w' r.succ-w' r.castSucc)).im ≠ 0 := by
            intro hz
            apply htrans
            change (w r.succ-w r.castSucc).1 * (e (p (finRotate (n+1) k))-e (p k)).2 -
              (w r.succ-w r.castSucc).2 * (e (p (finRotate (n+1) k))-e (p k)).1 = 0
            change _ = 0 at hz
            simp only [w',e,Complex.equivRealProdLm_apply,Complex.equivRealProdLm_symm_apply,
              Complex.mul_im,Complex.sub_re,Complex.sub_im,Complex.star_def,Complex.conj_re,
              Complex.conj_im,Complex.add_re,Complex.add_im,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
              Complex.I_re,Complex.I_im,Prod.fst_sub,Prod.snd_sub,mul_zero,mul_one,add_zero,zero_add] at hz ⊢
            linarith
          have hunique' (τ : ℝ) (hτ : τ ∈ Icc (0:ℝ) m) :
              γ' τ ∈ p.boundary ℝ ↔ τ = (r.val:ℝ)+s := by
            rw [←hunique τ hτ,←hboundary]
            constructor
            · intro hz
              exact ⟨γ' τ,hz,e.apply_symm_apply _⟩
            · rintro ⟨z,hz,heq⟩
              have : z=γ' τ := (congrArg e.symm heq).symm.trans (e.symm_apply_apply z) |>.symm
              exact this ▸ hz
          have hγ' : ContinuousOn γ' (Icc (0:ℝ) m) := e.symm.toContinuousLinearEquiv.continuous.comp_continuousOn hγ
          have hinj' : InjOn γ' (Icc (0:ℝ) m) := fun t ht u hu h ↦ hinj ht hu (e.symm.injective h)
          have hh := cairns_piecewise_access_crossing_g6 p hp.2.2.1 hp.2.2.2 Q E
            hoQ hoE hdis hcover hclQ hclE m hm w' γ' hγ' hinj' haff' r s k
            ⟨hs0,hs1⟩ hedge' htrans' hunique'
          refine ⟨γ' 0,⟨γ 0,hγ0,rfl⟩,γ' m,?_,hh⟩
          dsimp only [γ']
          rw [hγm,e.symm_apply_apply]
          exact hx
        have hregion_contradiction (Q E : Set ℂ) (hoQ : IsOpen Q) (hoE : IsOpen E)
            (hdis : Disjoint Q E) (hcover : Q ∪ E = (p.boundary ℝ)ᶜ)
            (hclQ : p.boundary ℝ ⊆ closure Q) (hclE : p.boundary ℝ ⊆ closure E)
            (hbQ : Bornology.IsBounded Q) (hdE : d ⊆ E) : False := by
          have hUE : U ⊆ E := by
            rcases hUconn.subset_or_subset hoQ hoE hdis (hcover.symm ▸ hUsub) with h | h
            · exact (hUunbounded (hbQ.subset h)).elim
            · exact h
          obtain ⟨u,hu,v,hv,hh⟩ := haccess_cross Q E hoQ hoE hdis hcover hclQ hclE
          rcases hh with hh | hh
          · exact disjoint_left.mp hdis hh.1 (hUE hu)
          · exact disjoint_left.mp hdis hh.2 (hdE hv)
        have hnotba : ¬Cb ⊆ Ca := by
          intro hsub
          have hseam (x : ℂ) (hx : x ∈ d) : Cb ∪ Ea ∪ d ∈ nhds x := by
            obtain ⟨ε,hε,hla,hlb,hld⟩ := hlocal x hx
            exact cairns_nested_local_seam_g6 Ca Ea (A.boundary ℝ) Cb Eb (B.boundary ℝ)
              d L x ε hε ha9 ha10 hb9 hb10 ha5 hb5 ha4 hb4
              (hCa (hda hx)) (hEa (hda hx)) (hCb (hdb hx)) (hEb (hdb hx)) hla hlb hld hsub
          obtain ⟨hoQ,hoE,hdis,hcover,hclQ,hclE⟩ := cairns_nested_cells_regions_g6
            ha9 ha10 hb9 hb10 ha5 hb5 ha4 hb4 ha15 hCb hEa hEb hAB
            (openSegment_subset_segment ℝ (p i) (p j)) hclArca hclArcb hsub hseam
          rw [houter] at hcover hclQ hclE
          exact hregion_contradiction _ _ hoQ hoE hdis hcover hclQ hclE
            (ha11.subset inter_subset_left) (fun x hx ↦ Or.inr hx)
        have hnotab : ¬Ca ⊆ Cb := by
          intro hsub
          have hseam (x : ℂ) (hx : x ∈ d) : Ca ∪ Eb ∪ d ∈ nhds x := by
            obtain ⟨ε,hε,hla,hlb,hld⟩ := hlocal x hx
            exact cairns_nested_local_seam_g6 Cb Eb (B.boundary ℝ) Ca Ea (A.boundary ℝ)
              d L x ε hε hb9 hb10 ha9 ha10 hb5 ha5 hb4 ha4
              (hCb (hdb hx)) (hEb (hdb hx)) (hCa (hda hx)) (hEa (hda hx)) hlb hla hld hsub
          have hBA : B.boundary ℝ ∩ A.boundary ℝ = D := (inter_comm _ _).trans hAB
          have houter' : (B.boundary ℝ ∪ A.boundary ℝ) \ d = p.boundary ℝ := by
            rw [union_comm]
            exact houter
          obtain ⟨hoQ,hoE,hdis,hcover,hclQ,hclE⟩ := cairns_nested_cells_regions_g6
            hb9 hb10 ha9 ha10 hb5 ha5 hb4 ha4 hb15 hCa hEb hEa hBA
            (openSegment_subset_segment ℝ (p i) (p j)) hclArcb hclArca hsub hseam
          rw [houter'] at hcover hclQ hclE
          exact hregion_contradiction _ _ hoQ hoE hdis hcover hclQ hclE
            (hb11.subset inter_subset_left) (fun x hx ↦ Or.inr hx)
        have hwitness {C E c C' : Set ℂ} (hcover : C ∪ E = cᶜ)
            (hfront : c ⊆ closure E) (hopen : IsOpen C') (hnot : ¬C' ⊆ C) :
            (C' ∩ E).Nonempty := by
          by_contra hempty
          apply hnot
          intro z hz
          have hzE : z ∉ E := fun h ↦ hempty ⟨z,hz,h⟩
          have hzc : z ∉ c := by
            intro hzc
            obtain ⟨w,hwC,hwE⟩ := _root_.mem_closure_iff.mp (hfront hzc) C' hopen hz
            exact hempty ⟨w,hwC,hwE⟩
          exact (hcover.symm ▸ hzc : z ∈ C ∪ E).resolve_right hzE
        have hwab := hwitness hb4 hEb ha9 hnotab
        have hwba := hwitness ha4 hEa hb9 hnotba
        have hclosed : closure Ca ∩ closure Cb = D :=
          cairns_cells_disjoint_of_outside_witnesses_g6 ha7.isPreconnected ha8.isPreconnected
            hb7.isPreconnected hb8.isPreconnected ha9 ha10 hb9 hb10 ha5 hb5 ha4 hb4
            ha15 hb15 ha11 hb11 ha12 hb12 hAB harca harcb hwab hwba
        have hdiscells : Disjoint Ca Cb := by
          apply disjoint_left.mpr
          intro x hxa hxb
          have hxD : x ∈ D := hclosed ▸ ⟨subset_closure hxa,subset_closure hxb⟩
          exact (show x ∈ (A.boundary ℝ)ᶜ from ha4 ▸ Or.inl hxa) (hDab hxD).1
        have hopposite (x : ℂ) (hx : x ∈ d) : ∃ ε : ℝ, 0<ε ∧
            ∃ ν : ℂ, ‖ν‖=1 ∧ ((p j-p i)/ν).re=0 ∧
              ball x ε ∩ Ca = {z | z∈ball x ε ∧ 0<((z-x)/ν).re} ∧
              ball x ε ∩ Cb = {z | z∈ball x ε ∧ ((z-x)/ν).re<0} := by
          obtain ⟨ε,hε,hla,hlb,hld⟩ := hlocal x hx
          obtain ⟨ν,hν,hperp,hcoord⟩ := cairns_unit_normal_coordinate_g6 (p j-p i)
            (sub_ne_zero.mpr hpij.symm)
          have hn : 0<‖p j-p i‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hpij.symm)
          have hcoord' (z : ℂ) : ((z-x)/ν).re = (L z-L x)/‖p j-p i‖ := by
            rw [hcoord]
            change L (z-x)/_ = _
            rw [map_sub]
          have hP : ball x ε ∩ {z | L x<L z} = {z | z∈ball x ε ∧ 0<((z-x)/ν).re} := by
            ext z
            simp only [mem_inter_iff,mem_ofPred_eq,hcoord',div_pos_iff_of_pos_right hn,sub_pos]
          have hN : ball x ε ∩ {z | L z<L x} = {z | z∈ball x ε ∧ ((z-x)/ν).re<0} := by
            ext z
            simp only [mem_inter_iff,mem_ofPred_eq,hcoord',div_lt_iff₀ hn,zero_mul,sub_neg]
          have hla' := cairns_local_line_sides_g6 Ca Ea (A.boundary ℝ) L x ε hε
            ha9 ha10 ha5 ha4 (hCa (hda hx)) (hEa (hda hx)) hla
          have hlb' := cairns_local_line_sides_g6 Cb Eb (B.boundary ℝ) L x ε hε
            hb9 hb10 hb5 hb4 (hCb (hdb hx)) (hEb (hdb hx)) hlb
          obtain ⟨w,hwb,hwC⟩ := _root_.mem_closure_iff.mp (hCa (hda hx)) (ball x ε)
            isOpen_ball (mem_ball_self hε)
          have hfalse (heq : ball x ε ∩ Ca = ball x ε ∩ Cb) : False :=
            disjoint_left.mp hdiscells hwC ((heq ▸ ⟨hwb,hwC⟩ : w∈ball x ε∩Cb).2)
          rcases hla' with ⟨hla',hea'⟩ | ⟨hla',hea'⟩ <;>
            rcases hlb' with ⟨hlb',heb'⟩ | ⟨hlb',heb'⟩
          · exact (hfalse (hla'.trans hlb'.symm)).elim
          · exact ⟨ε,hε,ν,hν,hperp,hla'.trans hP,hlb'.trans hN⟩
          · refine ⟨ε,hε,-ν,by simpa using hν,by simpa only [div_neg,Complex.neg_re,neg_eq_zero] using hperp,?_,?_⟩
            · simpa only [div_neg,Complex.neg_re,neg_pos] using hla'.trans hN
            · simpa only [div_neg,Complex.neg_re,neg_lt_zero] using hlb'.trans hP
          · exact (hfalse (hla'.trans hlb'.symm)).elim
        have hexact {m : ℕ} (r : Polygon ℂ m) (hinj : Function.Injective r.vertices)
            (hs : ∀ k l : Fin m, k≠l → r.edgeSet ℝ k ∩ r.edgeSet ℝ l ⊆
              r.vertices '' ({k,finRotate m k}∩{l,finRotate m l})) :
            ∀ k l : Fin m, k≠l → r.edgeSet ℝ k ∩ r.edgeSet ℝ l =
              ({r k,r (finRotate m k)} : Set ℂ) ∩ {r l,r (finRotate m l)} := by
          intro k l hkl
          apply subset_antisymm
          · rintro z hz
            obtain ⟨t,⟨htk,htl⟩,rfl⟩ := hs k l hkl hz
            constructor
            · rcases htk with rfl | ht
              · exact Or.inl rfl
              · exact Or.inr (congrArg r (mem_singleton_iff.mp ht))
            · rcases htl with rfl | ht
              · exact Or.inl rfl
              · exact Or.inr (congrArg r (mem_singleton_iff.mp ht))
          · rintro z ⟨hzk,hzl⟩
            constructor
            · rcases hzk with rfl | hzk
              · exact left_mem_affineSegment ℝ _ _
              · rw [mem_singleton_iff.mp hzk]
                exact right_mem_affineSegment ℝ _ _
            · rcases hzl with rfl | hzl
              · exact left_mem_affineSegment ℝ _ _
              · rw [mem_singleton_iff.mp hzl]
                exact right_mem_affineSegment ℝ _ _
        have hCaimage : Ca ∈ (fun z : ℂ ↦ connectedComponentIn (A.boundary ℝ)ᶜ z) ''
            (A.boundary ℝ)ᶜ := by rw [ha6]; exact Or.inl rfl
        have hCbimage : Cb ∈ (fun z : ℂ ↦ connectedComponentIn (B.boundary ℝ)ᶜ z) ''
            (B.boundary ℝ)ᶜ := by rw [hb6]; exact Or.inl rfl
        obtain ⟨ua,hua,hCaeq⟩ := hCaimage
        obtain ⟨ub,hub,hCbeq⟩ := hCbimage
        obtain ⟨a',rfl⟩ : ∃ k,a=k+2 := ⟨a-2,by omega⟩
        obtain ⟨b',rfl⟩ : ∃ k,b=k+2 := ⟨b-2,by omega⟩
        have hamalg := cairns_polygon_opposite_cells_ambient_amalgamation A B
          hAc.2.1 hAc.2.2.1 (hexact A hAc.2.1 hAc.2.2.2)
          hBc.2.1 hBc.2.2.1 (hexact B hBc.2.1 hBc.2.2.2)
          ⟨Ha,hHa⟩ ⟨Hb,hHb⟩ ua ub hua hub Ca Cb hCaeq.symm hCbeq.symm
          ha11 hb11 (p i) (p j) hpij hAB hclosed hopposite
        let βouter : ↥((A.boundary ℝ ∪ B.boundary ℝ) \ d) ≃ₜ sphere (0:ℂ) 1 :=
          (Homeomorph.setCongr houter).trans β
        obtain ⟨H,hHD,hH⟩ := hamalg.2.2 βouter
        refine ⟨H,subset_antisymm ?_ ?_⟩
        · rintro z ⟨w,hw,rfl⟩
          let w' : ↥((A.boundary ℝ ∪ B.boundary ℝ) \ d) := ⟨w,houter.symm ▸ hw⟩
          have heq := hH w'
          exact heq.symm ▸ (βouter w').property
        · intro z hz
          let w := βouter.symm ⟨z,hz⟩
          refine ⟨w,houter ▸ w.property,?_⟩
          exact (hH w).trans (congrArg Subtype.val (βouter.apply_symm_apply ⟨z,hz⟩))

end HolomorphicAnosov

