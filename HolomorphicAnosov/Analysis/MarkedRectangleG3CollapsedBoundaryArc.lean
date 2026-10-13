import HolomorphicAnosov.Analysis.ChordCapClosure
import HolomorphicAnosov.Analysis.ChordCapImageComponent
import HolomorphicAnosov.Analysis.CircleChordArcs
import HolomorphicAnosov.Topology.IntervalLoopCircleEmbedding
import Mathlib.Analysis.InnerProductSpace.Convex
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Topology.Connected.LocallyConnected
import HolomorphicAnosov.Topology.JordanComplementTwoRegions
import Mathlib.Analysis.Complex.UnitDisc.Basic
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Collapse of one circle arc under a boundary collision

Stage 2 statement for `analysis.marked_rectangle_g3_collapsed_boundary_arc`.
Sources: Tao, *246C Notes 2* (2018), §2 Theorem 20, final proof paragraph;
McMullen, *Advanced Complex Analysis*, Theorem 4.5, p.60 (boundary monotonicity
assertion); Cairns, *An Elementary Proof of the Jordan-Schoenflies Theorem* (1951),
main theorem p.860 and Lemma 5.1, pp.866–867 (independent Jordan separation).

The domain and circle types are Mathlib's `Complex.UnitDisc`,
`Complex.UnitClosedDisc`, and `Circle`. A bounded Jordan domain is a bounded
component of the complement of an embedded circle. The two directed arcs are
defined by the two sides of the oriented endpoint chord, not by arbitrary sets.
Only the named theorem is admitted; every definition has actual Mathlib data.
-/

noncomputable section

namespace HolomorphicAnosov.MarkedRectangleG3CollapsedBoundaryArc

open Set
open scoped ComplexConjugate

/-- A bounded Jordan domain: the bounded complementary component of an embedded
circle. Source: Cairns (1951), main theorem p.860; no boundary regularity is assumed. -/
def IsBoundedJordanDomain (Q : Set ℂ) : Prop :=
  ∃ γ : Circle → ℂ, Topology.IsEmbedding γ ∧
    ∃ w : ℂ, w ∉ range γ ∧ Q = connectedComponentIn (range γ)ᶜ w ∧
      Bornology.IsBounded Q

/-- The ordinary inclusion of the open unit disk in the closed disk.
Source: the source disk in Tao's Theorem 20; Mathlib's ball/closed-ball inclusion. -/
def diskInclusion (z : Complex.UnitDisc) : Complex.UnitClosedDisc :=
  ⟨(z : ℂ), Metric.ball_subset_closedBall z.property⟩

/-- The ordinary inclusion of the unit circle in the closed disk.
Source: the source boundary in Tao's Theorem 20; Mathlib's sphere inclusion. -/
def circleInclusion (z : Circle) : Complex.UnitClosedDisc :=
  ⟨(z : ℂ), Metric.sphere_subset_closedBall z.property⟩

/-- The counterclockwise closed circle arc from `ζ` to `ω`, when they are distinct.
It lies on the right side of the directed chord `ζ → ω`. Reversing the endpoints
gives the complementary closed arc. Source: the two chord caps in Tao's final
Theorem 20 paragraph, expanded in step 7 of the DAG proof. -/
def closedDirectedArc (ζ ω : Circle) : Set Circle :=
  {z | (conj ((ω : ℂ) - ζ) * ((z : ℂ) - ζ)).im ≤ 0}

/-- The relative interior of the directed closed arc, with both endpoints deleted.
Source: the strict chord-cap inequality in step 7 of the same source proof. -/
def openDirectedArc (ζ ω : Circle) : Set Circle :=
  {z | (conj ((ω : ℂ) - ζ) * ((z : ℂ) - ζ)).im < 0}

/-- Boundary values of a closed-disk map, viewed in the ambient complex plane.
Source: the literal boundary restriction of `F` in Tao's Theorem 20. -/
def boundaryValue {Q : Set ℂ} (F : Complex.UnitClosedDisc → closure Q)
    (z : Circle) : ℂ :=
  (F (circleInclusion z) : ℂ)

/-- If two distinct circle points have the same boundary image under a continuous
closed-disk extension of an interior homeomorphism onto a bounded Jordan domain,
one of their two closed joining arcs is constant at that image. Its open arc is
nonempty, relatively open in the circle, and constant at the same value.

Sources: Tao, *246C Notes 2*, §2 Theorem 20, final proof paragraph (local text
line 269); McMullen, Theorem 4.5, p.60, corroborates monotonicity but does not
prove it. Independent arbitrary-Jordan separation is Cairns (1951), main theorem
p.860 and Lemma 5.1, pp.866–867. Complete natural-language proof:

1. Parametrize the endpoint chord by c(t)=(1-t)ζ+tω. Its squared norm is
   1-t(1-t)|ζ-ω|², so its open part lies in the disk and is injectively mapped
   into Q by the interior homeomorphism. Its endpoint images both equal p,
   which belongs to the frontier of Q and cannot equal an interior image.
2. Identify the chord endpoints using [0,1] → S¹, t ↦ exp(2πit). The continuous
   chord image descends through this compact-to-Hausdorff quotient. Interior
   injectivity makes the resulting circle map injective; the continuous
   compact-to-Hausdorff equivalence makes it an embedding. Its image J is
   the open chord image together with p, and J meets the frontier of Q only at p.
   Dependencies: compact_hausdorff_surjection_quotient_g8 and
   continuous_homeoOfEquivCompactToT2_g8 (both Mathlib DAG leaves).
3. Apply the independent Jordan separation theorem to J and the boundary of Q.
   Write V,W for the bounded/unbounded components of the complement of J and
   E for the exterior of Q. Their frontiers are their respective Jordan curves;
   closure V = V ∪ J. Dependency: marked_rectangle_g3_jordan_separation_schoenflies.
4. E is connected, unbounded and disjoint from J, hence lies in W. Every point
   of the frontier of Q lies in closure E, so none lies in the open set V.
   The plane partition now gives V ⊆ Q and closure V ∩ frontier Q = {p}.
   Dependency: the same independent Jordan separation theorem.
5. The chord divides the disk into two nonempty convex open caps, specified by
   the strict signs of its affine normal functional. They are connected and
   relatively clopen in the disk minus the chord, hence are its two components.
   Dependency: preconnected_subset_component_in_leaf_g2.
6. The interior homeomorphism maps these components to the two components of
   Q minus the open chord image. V is a nonempty connected relatively clopen
   subset of that complement; inside its component the clopen theorem forces
   equality. Therefore V is the image of one of the two source caps.
   Dependencies: Homeomorph.image_connectedComponentIn, the preceding component
   leaf, nonempty_clopen_eq_univ_g8, and independent Jordan separation.
7. The corresponding closed circle arc is the circle intersected with the
   nonstrict side of the chord. These are exactly closedDirectedArc ζ ω and
   closedDirectedArc ω ζ; the determinant sign fixes their directions. Distinct
   endpoints make both strict circle arcs nonempty and relatively open, also
   when the endpoints are antipodal. Every x of the selected closed arc is
   approached through its cap by (1-ε)x+εa₀ for a fixed cap point a₀ and ε→0+.
   Strict convexity keeps these points inside the disk and on the proper side.
8. Their images lie in V, so continuity puts F(x) in closure V. The boundary
   hypothesis puts it in frontier Q. The intersection in step 4 is {p}, so
   F(x)=p on the entire selected closed arc and on its nonempty open interior.
   Dependency: independent Jordan separation. No holomorphicity, boundary
   injectivity, or smoothness/rectifiability of the target boundary is used.
-/
theorem collapsed_boundary_arc
    {Q : Set ℂ} (hQ : IsBoundedJordanDomain Q)
    (F : Complex.UnitClosedDisc → closure Q) (hF : Continuous F)
    (e : Complex.UnitDisc ≃ₜ Q)
    (hInterior : ∀ z : Complex.UnitDisc, (F (diskInclusion z) : ℂ) = (e z : ℂ))
    (hBoundary : ∀ z : Circle, boundaryValue F z ∈ frontier Q)
    (ζ ω : Circle) (hDistinct : ζ ≠ ω) (p : ℂ)
    (hζ : boundaryValue F ζ = p) (hω : boundaryValue F ω = p) :
    ((∀ z ∈ closedDirectedArc ζ ω, boundaryValue F z = p) ∧
      (openDirectedArc ζ ω).Nonempty ∧ IsOpen (openDirectedArc ζ ω) ∧
      (∀ z ∈ openDirectedArc ζ ω, boundaryValue F z = p)) ∨
    ((∀ z ∈ closedDirectedArc ω ζ, boundaryValue F z = p) ∧
      (openDirectedArc ω ζ).Nonempty ∧ IsOpen (openDirectedArc ω ζ) ∧
      (∀ z ∈ openDirectedArc ω ζ, boundaryValue F z = p)) := by
  have hQopen : IsOpen Q := by
    obtain ⟨γ, hγ, w, hw, rfl, hbounded⟩ := hQ
    exact (isCompact_range hγ.continuous).isClosed.isOpen_compl.connectedComponentIn
  have hpfront : p ∈ frontier Q := hζ ▸ hBoundary ζ
  have hpnot : p ∉ Q := by
    exact fun hp ↦ hpfront.2 (hQopen.interior_eq.symm ▸ hp)
  have hne : (ζ : ℂ) ≠ (ω : ℂ) := fun h ↦ hDistinct (Subtype.ext h)
  let c : ℝ → ℂ := AffineMap.lineMap (ζ : ℂ) (ω : ℂ)
  have hc (t : ℝ) (ht : t ∈ Icc 0 1) : c t ∈ Metric.closedBall (0 : ℂ) 1 := by
    dsimp only [c]
    rw [AffineMap.lineMap_apply_module]
    exact (convex_closedBall (0 : ℂ) 1)
      (Metric.sphere_subset_closedBall ζ.property)
      (Metric.sphere_subset_closedBall ω.property)
      (sub_nonneg.mpr ht.2) ht.1 (by ring)
  have hcinterior (t : ℝ) (ht : t ∈ Ioo 0 1) : c t ∈ Metric.ball (0 : ℂ) 1 := by
    dsimp only [c]
    rw [AffineMap.lineMap_apply_module]
    exact combo_mem_ball_of_ne
      (Metric.sphere_subset_closedBall ζ.property)
      (Metric.sphere_subset_closedBall ω.property) hne
      (sub_pos.mpr ht.2) ht.1 (by ring)
  let φ : Icc (0 : ℝ) 1 → ℂ := fun t ↦ (F ⟨c t, hc t t.property⟩ : ℂ)
  have hφ : Continuous φ := by
    exact continuous_subtype_val.comp (hF.comp
      ((AffineMap.lineMap_continuous.comp continuous_subtype_val).subtype_mk _))
  have hφzero : φ ⟨0, by simp⟩ = p := by
    simpa [φ, c, boundaryValue, circleInclusion] using hζ
  have hφone : φ ⟨1, by simp⟩ = p := by
    simpa [φ, c, boundaryValue, circleInclusion] using hω
  have hφinterior (t : Icc (0 : ℝ) 1) (ht : (t : ℝ) ∈ Ioo 0 1) : φ t ∈ Q := by
    have := hInterior ⟨c t, hcinterior t ht⟩
    change (F (diskInclusion ⟨c t, hcinterior t ht⟩) : ℂ) ∈ Q
    rw [this]
    exact (e ⟨c t, hcinterior t ht⟩).property
  let f : ℝ → ℂ := φ ∘ Set.projIcc 0 1 (by norm_num)
  have hf : Continuous f := hφ.comp continuous_projIcc
  have hft (t : ℝ) (ht : t ∈ Icc 0 1) : f t = φ ⟨t, ht⟩ := by
    simp only [f, Function.comp_apply, Set.projIcc_of_mem (by norm_num) ht]
  have hfend : f 0 = f 1 := by
    rw [hft 0 (by simp), hft 1 (by simp), hφzero, hφone]
  have hfinj : InjOn f (Ico 0 1) := by
    intro t ht s hs heq
    rw [hft t (Ico_subset_Icc_self ht), hft s (Ico_subset_Icc_self hs)] at heq
    by_cases ht0 : t = 0
    · subst t
      by_contra h
      have hs0 : 0 < s := lt_of_le_of_ne hs.1 h
      exact hpnot (hφzero ▸ heq.symm ▸ hφinterior ⟨s, Ico_subset_Icc_self hs⟩ ⟨hs0, hs.2⟩)
    · by_cases hs0 : s = 0
      · subst s
        have ht0' : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
        exact (hpnot (hφzero ▸ heq ▸ hφinterior ⟨t, Ico_subset_Icc_self ht⟩
          ⟨ht0', ht.2⟩)).elim
      · have ht' : t ∈ Ioo 0 1 := ⟨lt_of_le_of_ne ht.1 (Ne.symm ht0), ht.2⟩
        have hs' : s ∈ Ioo 0 1 := ⟨lt_of_le_of_ne hs.1 (Ne.symm hs0), hs.2⟩
        have het := hInterior ⟨c t, hcinterior t ht'⟩
        have hes := hInterior ⟨c s, hcinterior s hs'⟩
        have he : e ⟨c t, hcinterior t ht'⟩ = e ⟨c s, hcinterior s hs'⟩ := by
          apply Subtype.ext
          exact het.symm.trans (heq.trans hes)
        have hc_eq : c t = c s := congrArg Subtype.val (e.injective he)
        exact AffineMap.lineMap_injective ℝ hne hc_eq
  obtain ⟨j, hj, hjrange⟩ :=
    HolomorphicAnosov.Topology.intervalLoop_circle_embedding f hf.continuousOn hfend hfinj
  have hpJ : p ∈ range j := by
    rw [hjrange]
    exact ⟨0, by simp, (hft 0 (by simp)).trans hφzero⟩
  have hJsubset : range j ⊆ Q ∪ {p} := by
    rw [hjrange]
    rintro y ⟨t, ht, rfl⟩
    by_cases ht0 : t = 0
    · subst t
      exact Or.inr ((hft 0 (by simp)).trans hφzero)
    · by_cases ht1 : t = 1
      · subst t
        exact Or.inr ((hft 1 (by simp)).trans hφone)
      · exact Or.inl ((hft t ht).symm ▸ hφinterior ⟨t, ht⟩
          ⟨lt_of_le_of_ne ht.1 (Ne.symm ht0), lt_of_le_of_ne ht.2 ht1⟩)
  have hJfrontier : range j ∩ frontier Q = {p} := by
    ext y
    constructor
    · rintro ⟨hyJ, hyfront⟩
      rcases hJsubset hyJ with hyQ | hyp
      · exact (hyfront.2 (hQopen.interior_eq.symm ▸ hyQ)).elim
      · exact hyp
    · rintro rfl
      exact ⟨hpJ, hpfront⟩
  obtain ⟨V, W, hVne, hWne, hVWne, hVWunion, hVWdisj, hVWcomponents,
    hVconn, hWconn, hVopen, hWopen, hVbounded, hWunbounded,
    hVfront, hWfront, hVclosure⟩ := cairns_jordan_complement_two_regions j hj
  obtain ⟨γ, hγ, w, hw, hQcomponent, hQbounded⟩ := hQ
  obtain ⟨U, E, hUne, hEne, hUEne, hUEunion, hUEdisj, hUEcomponents,
    hUconn, hEconn, hUopen, hEopen, hUbounded, hEunbounded,
    hUfront, hEfront, hUclosure⟩ := cairns_jordan_complement_two_regions γ hγ
  have hQmember : Q ∈ ({U, E} : Set (Set ℂ)) := by
    rw [← hUEcomponents]
    exact ⟨w, hw, hQcomponent.symm⟩
  have hQU : Q = U := by
    rcases hQmember with h | h
    · exact h
    · exact (hEunbounded ((mem_singleton_iff.mp h) ▸ hQbounded)).elim
  subst U
  have hpEfront : p ∈ frontier E := by rwa [hEfront, ← hUfront]
  have hpnotE : p ∉ E := fun hp ↦ hpEfront.2 (hEopen.interior_eq.symm ▸ hp)
  have hEdisjJ : Disjoint E (range j) := by
    apply disjoint_left.mpr
    intro x hxE hxJ
    rcases hJsubset hxJ with hxQ | hxp
    · exact disjoint_left.mp hUEdisj hxQ hxE
    · exact hpnotE (mem_singleton_iff.mp hxp ▸ hxE)
  have hEsubset : E ⊆ V ∪ W := by
    rw [hVWunion]
    exact fun x hx ↦ disjoint_left.mp hEdisjJ hx
  have hEW : E ⊆ W := by
    rcases hEconn.isPreconnected.subset_or_subset hVopen hWopen hVWdisj hEsubset with h | h
    · exact (hEunbounded (hVbounded.subset h)).elim
    · exact h
  have hfrontQclosureE : frontier Q ⊆ closure E := by
    rw [hUfront, ← hEfront]
    exact frontier_subset_closure
  have hVdisjE : Disjoint V E := hVWdisj.mono_right hEW
  have hVdisjFrontQ : Disjoint V (frontier Q) := by
    apply disjoint_left.mpr
    intro x hxV hxfront
    have hxE := hfrontQclosureE hxfront
    rcases (mem_closure_iff_nhds.mp hxE) V (hVopen.mem_nhds hxV) with ⟨y, hyV, hyE⟩
    exact disjoint_left.mp hVdisjE hyV hyE
  have hVQ : V ⊆ Q := by
    intro x hxV
    have hxnotγ : x ∉ range γ := by
      rw [← hUfront]
      exact disjoint_left.mp hVdisjFrontQ hxV
    have hxQE : x ∈ Q ∪ E := by rwa [hUEunion]
    exact hxQE.resolve_right (disjoint_left.mp hVdisjE hxV)
  have hclosureVfrontQ : closure V ∩ frontier Q = {p} := by
    rw [hVclosure, union_inter_distrib_right, hJfrontier,
      disjoint_iff_inter_eq_empty.mp hVdisjFrontQ, empty_union]
  have hVsubsetS : V ⊆ Q \ range j := by
    intro x hx
    refine ⟨hVQ hx, ?_⟩
    have hxVW : x ∈ V ∪ W := Or.inl hx
    rw [hVWunion] at hxVW
    exact hxVW
  have hVcomponent (v : ℂ) (hv : v ∈ V) :
      connectedComponentIn (Q \ range j) v = V := by
    apply subset_antisymm
    · have hcover : connectedComponentIn (Q \ range j) v ⊆ V ∪ W := by
        rw [hVWunion]
        exact fun x hx ↦ (connectedComponentIn_subset _ _ hx).2
      rcases isPreconnected_connectedComponentIn.subset_or_subset
          hVopen hWopen hVWdisj hcover with h | h
      · exact h
      · exact (disjoint_left.mp hVWdisj hv
          (h (mem_connectedComponentIn (hVsubsetS hv)))).elim
    · exact hVconn.isPreconnected.subset_connectedComponentIn hv hVsubsetS
  have hcollapse_of_closure (z : Circle)
      (hz : circleInclusion z ∈ closure {w : Complex.UnitClosedDisc | (F w : ℂ) ∈ V}) :
      boundaryValue F z = p := by
    have hmaps : MapsTo (fun w : Complex.UnitClosedDisc ↦ (F w : ℂ))
        {w | (F w : ℂ) ∈ V} V := fun _ hw ↦ hw
    have hzV := hmaps.closure (continuous_subtype_val.comp hF) hz
    have hzfront : boundaryValue F z ∈ closure V ∩ frontier Q := ⟨hzV, hBoundary z⟩
    simpa only [hclosureVfrontQ, mem_singleton_iff] using hzfront
  -- Package the strict-side conclusion once a closed arc has been collapsed.
  suffices hclosed :
      (∀ z ∈ closedDirectedArc ζ ω, boundaryValue F z = p) ∨
      (∀ z ∈ closedDirectedArc ω ζ, boundaryValue F z = p) by
    have finish (u v : Circle) (hne : u ≠ v)
        (hc : ∀ z ∈ closedDirectedArc u v, boundaryValue F z = p) :
        (∀ z ∈ closedDirectedArc u v, boundaryValue F z = p) ∧
        (openDirectedArc u v).Nonempty ∧ IsOpen (openDirectedArc u v) ∧
        (∀ z ∈ openDirectedArc u v, boundaryValue F z = p) := by
      refine ⟨hc, HolomorphicAnosov.Analysis.circle_chord_strict_side_nonempty hne, ?_, ?_⟩
      · apply isOpen_lt
        · exact Complex.continuous_im.comp
            (continuous_const.mul (continuous_subtype_val.sub continuous_const))
        · exact continuous_const
      · intro z hz
        apply hc z
        exact (show (conj ((v : ℂ) - u) * ((z : ℂ) - u)).im < 0 from hz).le
    exact hclosed.elim (fun hc => Or.inl (finish ζ ω hDistinct hc))
      (fun hc => Or.inr (finish ω ζ hDistinct.symm hc))
  -- Tao's final chord-cap argument: the remaining geometric step chooses a side.
  suffices hcap :
      (∃ b : Complex.UnitDisc,
        (conj ((ω : ℂ) - ζ) * ((b : ℂ) - ζ)).im < 0 ∧
        ∀ z : Complex.UnitDisc,
          (conj ((ω : ℂ) - ζ) * ((z : ℂ) - ζ)).im < 0 → (e z : ℂ) ∈ V) ∨
      (∃ b : Complex.UnitDisc,
        (conj ((ζ : ℂ) - ω) * ((b : ℂ) - ω)).im < 0 ∧
        ∀ z : Complex.UnitDisc,
          (conj ((ζ : ℂ) - ω) * ((z : ℂ) - ω)).im < 0 → (e z : ℂ) ∈ V) by
    have finishCap (u v : Circle) (b : Complex.UnitDisc)
        (hb : (conj ((v : ℂ) - u) * ((b : ℂ) - u)).im < 0)
        (hmap : ∀ z : Complex.UnitDisc,
          (conj ((v : ℂ) - u) * ((z : ℂ) - u)).im < 0 → (e z : ℂ) ∈ V) :
        ∀ z ∈ closedDirectedArc u v, boundaryValue F z = p := by
      intro z hz
      apply hcollapse_of_closure
      apply closure_mono _ (HolomorphicAnosov.Analysis.chordCap_closure
        (u : ℂ) (v : ℂ) b hb (circleInclusion z) hz)
      intro w hw
      obtain ⟨hwball, hwside⟩ := hw
      have hval := hInterior (⟨(w : ℂ), hwball⟩ : Complex.UnitDisc)
      change (F w : ℂ) ∈ V
      change (F w : ℂ) = (e ⟨(w : ℂ), hwball⟩ : ℂ) at hval
      rw [hval]
      exact hmap ⟨(w : ℂ), hwball⟩ hwside
    exact hcap.elim
      (fun ⟨b, hb, hmap⟩ ↦ Or.inl (finishCap ζ ω b hb hmap))
      (fun ⟨b, hb, hmap⟩ ↦ Or.inr (finishCap ω ζ b hb hmap))
  exact HolomorphicAnosov.Analysis.chord_cap_image_component Q V e j ζ ω hDistinct
    f hcinterior hjrange (by
      intro t ht
      rw [hft t (Ioo_subset_Icc_self ht)]
      exact hInterior ⟨c t, hcinterior t ht⟩)
    ⟨by rw [hft 0 (by simp), hφzero]; exact hpnot,
      by rw [hft 1 (by simp), hφone]; exact hpnot⟩ hVne hVcomponent

end HolomorphicAnosov.MarkedRectangleG3CollapsedBoundaryArc
