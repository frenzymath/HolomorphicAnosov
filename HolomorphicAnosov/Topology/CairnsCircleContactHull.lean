import HolomorphicAnosov.Topology.CompactConvexHullFiniteDimensional
import HolomorphicAnosov.Analysis.UnitCircleChordBoundaryZeroDeterminant
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Convex.Combination
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Analysis.Convex.GaugeRescale
import Mathlib.Analysis.Normed.Module.Convex

namespace HolomorphicAnosov
open Set
open scoped ComplexConjugate

/-- A nonzero real functional has at most two points in any of its level sets
on the unit circle. Write the functional in real and imaginary coordinates;
two equalities imply that the third point lies on the line through the first
two. The circle-chord zero-determinant identity finishes the argument. -/
theorem circle_functional_level_two_points (f : ℂ →L[ℝ] ℝ) (hf : f ≠ 0)
    (p q z : ℂ) (hp : ‖p‖ = 1) (hq : ‖q‖ = 1) (hz : ‖z‖ = 1)
    (hpq : p ≠ q) (heq : f p = f q) (hez : f z = f p) : z = p ∨ z = q := by
  have hfcoord (w : ℂ) : f w = w.re * f 1 + w.im * f Complex.I := by
    have hw : w = w.re • (1 : ℂ) + w.im • Complex.I := by
      apply Complex.ext <;> simp [Complex.real_smul]
    rw [hw, map_add, map_smul, map_smul]
    simp only [smul_eq_mul]
    congr 1 <;> congr 1 <;> simp [Complex.real_smul]
  have hnonzero : f 1 ≠ 0 ∨ f Complex.I ≠ 0 := by
    by_contra hh
    push Not at hh
    apply hf
    ext w
    change f w = 0
    rw [hfcoord w, hh.1, hh.2]
    simp
  apply Analysis.unit_circle_chord_boundary_zero_determinant p q z hpq hp hq hz
  rw [hfcoord p, hfcoord q] at heq
  rw [hfcoord z, hfcoord p] at hez
  simp only [Complex.mul_im, Complex.conj_re, Complex.conj_im,
    Complex.sub_re, Complex.sub_im]
  rcases hnonzero with hA | hB
  · apply (mul_eq_zero.mp (show f 1 * ((q.re-p.re)*(z.im-p.im) +
        -(q.im-p.im)*(z.re-p.re)) = 0 by
      linear_combination (p.im-z.im)*heq + (p.im-q.im)*hez)).resolve_left hA
  · apply (mul_eq_zero.mp (show f Complex.I * ((q.re-p.re)*(z.im-p.im) +
        -(q.im-p.im)*(z.re-p.re)) = 0 by
      linear_combination (z.re-p.re)*heq + (q.re-p.re)*hez)).resolve_left hB

/-- A supporting face of a convex hull is the hull of the original points on
that supporting line. In a positive finite convex combination attaining the
upper bound, every summand attains it. This is the finite-combination form of
the supporting-face argument used for Cairns's target contact hulls. -/
theorem mem_convexHull_supporting_face {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (S : Set E)
    (f : E →L[ℝ] ℝ) (u : ℝ) (hbound : ∀ z ∈ S, f z ≤ u)
    {x : E} (hx : x ∈ convexHull ℝ S) (hfx : f x = u) :
    x ∈ convexHull ℝ {z ∈ S | f z = u} := by
  classical
  obtain ⟨ι, _, z, w, hz, _, hw, hsum, hxsum⟩ :=
    eq_pos_convex_span_of_mem_convexHull hx
  have heq : (∑ i, w i * f (z i)) = ∑ i, w i * u := by
    rw [← Finset.sum_mul, hsum, one_mul]
    simpa only [map_sum, map_smul, smul_eq_mul, hfx] using congrArg f hxsum
  have heachi : ∀ i, f (z i) = u := by
    intro i
    have hh := (Finset.sum_eq_sum_iff_of_le (fun j (_ : j ∈ Finset.univ) ↦
      mul_le_mul_of_nonneg_left (hbound _ (hz (mem_range_self j))) (hw j).le)).mp heq i
      (Finset.mem_univ i)
    exact (mul_left_cancel₀ (hw i).ne' hh)
  rw [← hxsum]
  exact (convex_convexHull ℝ _).sum_mem (fun i _ ↦ (hw i).le) hsum
    (fun i _ ↦ subset_convexHull ℝ _ ⟨hz (mem_range_self i), heachi i⟩)

/-- Every boundary point of a compact circle-contact hull lies on a chord of
retained contacts, possibly a degenerate chord at a contact. A supporting
functional exists because the hull has interior. Its circle level set has at
most two points; the supporting-face lemma places the boundary point in their
segment. No Jordan separation theorem enters this convex argument. -/
theorem circle_contact_hull_frontier_chord (S : Set ℂ) (hS : IsCompact S)
    (hcircle : ∀ z ∈ S, ‖z‖ = 1) (hint : (interior (convexHull ℝ S)).Nonempty)
    {x : ℂ} (hx : x ∈ frontier (convexHull ℝ S)) :
    ∃ p ∈ S, ∃ q ∈ S, x ∈ segment ℝ p q ∧
      ∃ f : ℂ →L[ℝ] ℝ, f ≠ 0 ∧ f p = f q ∧ f x = f p ∧
        ∀ z ∈ S, f z ≤ f p := by
  classical
  obtain ⟨f, hf, hbound⟩ := geometric_hahn_banach_of_nonempty_interior_point
    (convex_convexHull ℝ S) hx.2 hint
  have hxHull : x ∈ convexHull ℝ S :=
    (isCompact_convexHull_finiteDimensional hS).isClosed.closure_eq ▸ hx.1
  let F : Set ℂ := {z ∈ S | f z = f x}
  have hxF : x ∈ convexHull ℝ F := mem_convexHull_supporting_face S f (f x)
    (fun z hz ↦ hbound z (subset_convexHull ℝ S hz)) hxHull rfl
  have hFne : F.Nonempty := by
    by_contra hh
    rw [Set.not_nonempty_iff_eq_empty.mp hh, convexHull_empty] at hxF
    exact hxF
  obtain ⟨p, hp⟩ := hFne
  by_cases hall : ∀ q ∈ F, q = p
  · have hxP : x = p := by
      have hh := convexHull_mono (show F ⊆ {p} from fun z hz ↦ hall z hz) hxF
      simpa using hh
    subst x
    exact ⟨p, hp.1, p, hp.1, left_mem_segment ℝ p p,
      f, hf, rfl, rfl, fun z hz ↦ hbound z (subset_convexHull ℝ S hz)⟩
  · push Not at hall
    obtain ⟨q,hq,hqp⟩ := hall
    have hFsub : F ⊆ {p,q} := by
      intro z hz
      exact circle_functional_level_two_points f hf p q z (hcircle p hp.1)
        (hcircle q hq.1) (hcircle z hz.1) hqp.symm (hp.2.trans hq.2.symm)
        (hz.2.trans hp.2.symm)
    have hxseg : x ∈ segment ℝ p q := by
      simpa only [convexHull_pair] using convexHull_mono hFsub hxF
    exact ⟨p,hp.1,q,hq.1,hxseg,f,hf,hp.2.trans hq.2.symm,hp.2.symm,
      fun z hz ↦ (hbound z (subset_convexHull ℝ S hz)).trans_eq hp.2.symm⟩

/-- An open part of a convex body whose frontier stays on the body's frontier
fills its interior. The interior of the body is connected; the open part is
also relatively closed there, since no point of its frontier is in that
interior. This identifies Cairns's glued target region with its contact hull. -/
theorem open_eq_convex_interior_of_frontier_subset {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (U C : Set E)
    (hU : IsOpen U) (hne : U.Nonempty) (hsub : U ⊆ C)
    (hC : Convex ℝ C) (hfront : frontier U ⊆ frontier C) : U = interior C := by
  have hui : U ⊆ interior C := interior_maximal hsub hU
  apply Subset.antisymm hui
  apply hC.interior.isPreconnected.subset_of_closure_inter_subset hU
  · obtain ⟨x,hx⟩ := hne
    exact ⟨x,hui hx,hx⟩
  · intro x hx
    by_contra hn
    have hfu : x ∈ frontier U := by
      rw [hU.frontier_eq]
      exact ⟨hx.1,hn⟩
    exact (hfront hfu).2 hx.2

/-- The preceding identification also supplies the open disk chart and the
circle frontier chart. The bounded convex-body gauge theorem gives an ambient
homeomorphism, which restricts to the interior and the frontier. -/
theorem open_convex_body_disk_charts (U C : Set ℂ) (hU : IsOpen U)
    (hne : U.Nonempty) (hsub : U ⊆ C) (hC : Convex ℝ C)
    (hbounded : Bornology.IsBounded C) (_hclosed : IsClosed C)
    (hfront : frontier U ⊆ frontier C) :
    Nonempty (U ≃ₜ Metric.ball (0 : ℂ) 1) ∧
      Nonempty (frontier U ≃ₜ Metric.sphere (0 : ℂ) 1) := by
  have heq := open_eq_convex_interior_of_frontier_subset U C hU hne hsub hC hfront
  have hint : (interior C).Nonempty := heq ▸ hne
  obtain ⟨H,hi,hcl,hf⟩ :=
    exists_homeomorph_image_interior_closure_frontier_eq_unitBall hC hint hbounded
  have hfU : frontier U = frontier C := by
    rw [heq, frontier, interior_interior,
      hC.closure_interior_eq_closure_of_nonempty_interior hint]
    rfl
  constructor
  · exact ⟨(Homeomorph.setCongr heq).trans ((H.image _).trans (Homeomorph.setCongr hi))⟩
  · exact ⟨(Homeomorph.setCongr hfU).trans ((H.image _).trans (Homeomorph.setCongr hf))⟩

/-- A bounded plane region lies in every nonempty closed convex set containing
its frontier. Otherwise a separating functional has a larger value at an
interior point than on the frontier. Its maximum on the compact closure is on
the frontier, since a nonzero linear functional is open, a contradiction. -/
theorem bounded_subset_closed_convex_of_frontier (U C : Set ℂ)
    (hbounded : Bornology.IsBounded U) (hC : Convex ℝ C) (hclosed : IsClosed C)
    (hCne : C.Nonempty) (hfront : frontier U ⊆ C) : U ⊆ C := by
  intro x hx
  by_contra hxc
  obtain ⟨f,u,hsep,hfx⟩ := geometric_hahn_banach_closed_point hC hclosed hxc
  have hfnz : f ≠ 0 := by
    intro hf
    obtain ⟨z,hz⟩ := hCne
    have hh := hsep z hz
    simp only [hf,zero_apply] at hh hfx
    linarith
  obtain ⟨y,hy,hmax⟩ := hbounded.isCompact_closure.exists_isMaxOn
    ⟨x,subset_closure hx⟩ f.continuous.continuousOn
  have hyfront : y ∈ frontier U := by
    refine ⟨hy,?_⟩
    intro hyint
    have hs : f '' interior U ⊆ Iic (f y) := by
      rintro _ ⟨z,hz,rfl⟩
      exact hmax (subset_closure (interior_subset hz))
    have hh := interior_maximal hs (f.isOpenMap_of_ne_zero hfnz _ isOpen_interior)
      (mem_image_of_mem f hyint)
    rw [interior_Iic] at hh
    exact lt_irrefl _ (show f y < f y from hh)
  exact (hsep y (hfront hyfront)).not_ge (hfx.le.trans (hmax (subset_closure hx)))

/-- A nonzero functional taking the same value at two distinct circle points
has a strictly larger value somewhere on the circle. Otherwise the entire
closed disk lies below that level by convexity. The midpoint of the two points
is in the open disk, contradicting openness of the functional at that level. -/
theorem circle_functional_equal_pair_not_upper_bound (f : ℂ →L[ℝ] ℝ) (hf : f ≠ 0)
    (p q : ℂ) (hp : ‖p‖ = 1) (hq : ‖q‖ = 1) (hpq : p ≠ q) (heq : f p = f q) :
    ∃ z : ℂ, ‖z‖ = 1 ∧ f p < f z := by
  by_contra hn
  push Not at hn
  have hsphere : Metric.sphere (0 : ℂ) 1 ⊆ {z | f z ≤ f p} := by
    intro z hz
    exact hn z (by simpa only [Metric.mem_sphere,dist_zero_right] using hz)
  have hball : Metric.closedBall (0 : ℂ) 1 ⊆ {z | f z ≤ f p} := by
    rw [← convexHull_sphere_eq_closedBall (0 : ℂ) (by norm_num : (0 : ℝ) ≤ 1)]
    exact convexHull_min hsphere ((convex_Iic _).linear_preimage f.toLinearMap)
  let m : ℂ := (1 / 2 : ℝ) • (p+q)
  have hm : m ∈ Metric.ball (0 : ℂ) 1 := by
    have hh := (norm_midpoint_lt_iff (hp.trans hq.symm)).mpr hpq
    simpa only [Metric.mem_ball,dist_zero_right,hp] using hh
  have hfm : f m = f p := by
    dsimp only [m]
    rw [map_smul,map_add,← heq]
    simp only [smul_eq_mul]
    ring
  have himage : f '' Metric.ball (0 : ℂ) 1 ⊆ Iic (f p) := by
    rintro _ ⟨z,hz,rfl⟩
    exact hball (Metric.ball_subset_closedBall hz)
  have hh := interior_maximal himage (f.isOpenMap_of_ne_zero hf _ Metric.isOpen_ball)
    (mem_image_of_mem f hm)
  rw [interior_Iic,hfm] at hh
  exact lt_irrefl _ (show f p < f p from hh)

/-- Circle-contact hulls on opposite sides of a common endpoint chord meet
exactly on that chord. A point in both hulls is on the supporting level. The
supporting-face lemma reduces it to circle contacts on that line, which are
exactly the two endpoints. -/
theorem opposite_circle_contact_hulls_intersection (S T : Set ℂ)
    (f : ℂ →L[ℝ] ℝ) (hf : f ≠ 0) (p q : ℂ)
    (hp : ‖p‖ = 1) (hq : ‖q‖ = 1) (hpq : p ≠ q) (heq : f p = f q)
    (hpS : p ∈ S) (hqS : q ∈ S) (hpT : p ∈ T) (hqT : q ∈ T)
    (hnorm : ∀ z ∈ T, ‖z‖ = 1)
    (hS : ∀ z ∈ S, f p ≤ f z) (hT : ∀ z ∈ T, f z ≤ f p) :
    convexHull ℝ S ∩ convexHull ℝ T = segment ℝ p q := by
  have hHS : convexHull ℝ S ⊆ {z | f p ≤ f z} :=
    convexHull_min hS ((convex_Ici _).linear_preimage f.toLinearMap)
  have hHT : convexHull ℝ T ⊆ {z | f z ≤ f p} :=
    convexHull_min hT ((convex_Iic _).linear_preimage f.toLinearMap)
  apply Subset.antisymm
  · intro z hz
    have hfz : f z = f p := le_antisymm (hHT hz.2) (hHS hz.1)
    have hface := mem_convexHull_supporting_face T f (f p) hT hz.2 hfz
    have hsub : {w ∈ T | f w = f p} ⊆ {p,q} := by
      intro w hw
      exact circle_functional_level_two_points f hf p q w hp hq (hnorm w hw.1) hpq heq hw.2
    simpa only [convexHull_pair] using convexHull_mono hsub hface
  · intro z hz
    exact ⟨(convex_convexHull ℝ S).segment_subset
      (subset_convexHull ℝ S hpS) (subset_convexHull ℝ S hqS) hz,
      (convex_convexHull ℝ T).segment_subset
      (subset_convexHull ℝ T hpT) (subset_convexHull ℝ T hqT) hz⟩

end HolomorphicAnosov
