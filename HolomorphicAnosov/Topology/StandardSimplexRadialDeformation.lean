import HolomorphicAnosov.Topology.StandardSimplexRelativeGenerator
import HolomorphicAnosov.Topology.Homotopy.StrongDeformationRetract
import Mathlib.Topology.Order.Lattice

/-! # Radial deformation of a punctured simplex
Source: Hatcher, Algebraic Topology, pp.233–234, radial local-homology comparison.
The finite-coordinate formulas below are an explicit agent-written expansion for simplices.
DAG node: `topo.standard_simplex_radial_deformation_g20`.
-/
noncomputable section
open Convexity
namespace HolomorphicAnosov

namespace SimplexRadial

variable {n : ℕ}
/-- The standard simplex with n+2 vertices; Hatcher p.103. -/
abbrev Δ (n : ℕ) := StdSimplex ℝ (Fin (n + 2))

/-- Avoiding every facet forces every barycentric coordinate to be positive.
A zero coordinate lets the remaining coordinates define a point in that facet.
Source: Hatcher p.103, barycentric coordinates and faces. -/
theorem weights_pos (t : Δ n)
    (hfaces : ∀ (i : Fin (n + 2)) (u : StdSimplex ℝ (Fin (n + 1))),
      t ≠ StdSimplex.map i.succAbove u) (i : Fin (n + 2)) : 0 < t.weights i := by
  apply lt_of_le_of_ne (t.weights_nonneg i)
  intro hi
  let u : StdSimplex ℝ (Fin (n + 1)) := {
    weights := Finsupp.equivFunOnFinite.symm (fun j ↦ t.weights (i.succAbove j))
    nonneg := fun j ↦ t.weights_nonneg _
    total := by
      rw [Finsupp.sum_fintype _ _ (by simp)]
      change ∑ j, t.weights (i.succAbove j) = 1
      have ht := t.total_of_fintype
      rw [Fin.sum_univ_succAbove _ i, ← hi, zero_add] at ht
      exact ht }
  apply hfaces i u
  ext j
  rcases Fin.eq_self_or_eq_succAbove i j with rfl | ⟨j, rfl⟩
  · rw [StdSimplex.weights_map, Finsupp.mapDomain_of_notMem_range _ _ (by simp)]
    exact hi.symm
  · simp [StdSimplex.weights_map, Finsupp.mapDomain_apply_of_injective
      Fin.succAbove_right_injective, u]

/-- Maximum normalized displacement toward a face.
Source: explicit simplex-coordinate expansion of Hatcher pp.233–234. -/
def scale (t x : Δ n) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun i ↦ (t.weights i - x.weights i) / t.weights i)

/-- Each normalized coordinate displacement is bounded by its finite maximum.
Source: the radial coordinate formula, Hatcher pp.233–234. -/
lemma ratio_le_scale (t x : Δ n) (i : Fin (n + 2)) :
    (t.weights i - x.weights i) / t.weights i ≤ scale t x :=
  Finset.le_sup' (fun i ↦ (t.weights i - x.weights i) / t.weights i) (Finset.mem_univ i)

/-- Nonnegative simplex coordinates bound the radial scale by one.
Source: the radial coordinate formula, Hatcher pp.233–234. -/
lemma scale_le_one (t x : Δ n) (ht : ∀ i, 0 < t.weights i) : scale t x ≤ 1 := by
  apply Finset.sup'_le
  intro i _
  apply (div_le_iff₀ (ht i)).2
  have := x.weights_nonneg i
  linarith

/-- The radial scale is positive away from the center: otherwise all coordinates
of the center are bounded by those of x, so their equal sums force x=t.
Source: explicit radial argument underlying Hatcher pp.233–234. -/
lemma scale_pos (t x : Δ n) (ht : ∀ i, 0 < t.weights i) (hx : x ≠ t) :
    0 < scale t x := by
  by_contra! h
  have hle (i) : t.weights i ≤ x.weights i := by
    have hh := (ratio_le_scale t x i).trans h
    have hh' := (div_le_iff₀ (ht i)).1 hh
    linarith
  have heq := (Finset.sum_eq_sum_iff_of_le (fun i (_ : i ∈ Finset.univ) ↦ hle i)).1
    (t.total_of_fintype.trans x.total_of_fintype.symm)
  apply hx
  ext i
  exact (heq i (Finset.mem_univ i)).symm

/-- A zero coordinate realizes scale one on the boundary.
Source: the radial coordinate formula, Hatcher pp.233–234. -/
lemma scale_eq_one (t x : Δ n) (ht : ∀ i, 0 < t.weights i)
    (hx : x ∈ standardSimplexBoundary n) : scale t x = 1 := by
  apply le_antisymm (scale_le_one t x ht)
  obtain ⟨i, hi⟩ := hx
  have h := ratio_le_scale t x i
  simpa [hi, ne_of_gt (ht i)] using h

/-- The radial scale is a finite maximum of continuous coordinate functions.
Source: explicit radial argument underlying Hatcher pp.233–234. -/
lemma continuous_scale (t : Δ n) : Continuous (scale t) := by
  apply Continuous.finset_sup'_apply
  intro i _
  exact (continuous_const.sub (StdSimplex.continuous_weights_apply ℝ i)).div_const _

/-- Radial projection to the boundary, given by t+(x-t)/m(x).
The finite maximum ensures nonnegative coordinates, and their sum remains one.
Source: explicit simplex expansion of Hatcher pp.233–234. -/
def radial (t : Δ n) (ht : ∀ i, 0 < t.weights i) (x : Δ n) (hx : x ≠ t) : Δ n where
  weights := Finsupp.equivFunOnFinite.symm
    (fun i ↦ t.weights i + (x.weights i - t.weights i) / scale t x)
  nonneg i := by
    change 0 ≤ t.weights i + (x.weights i - t.weights i) / scale t x
    have hs := scale_pos t x ht hx
    have hr := (div_le_iff₀ (ht i)).1 (ratio_le_scale t x i)
    have hd : -(t.weights i) ≤ (x.weights i - t.weights i) / scale t x :=
      (le_div_iff₀ hs).2 (by nlinarith)
    linarith
  total := by
    rw [Finsupp.sum_fintype _ _ (by simp)]
    change ∑ i, (t.weights i + (x.weights i - t.weights i) / scale t x) = 1
    simp_rw [div_eq_mul_inv]
    rw [Finset.sum_add_distrib, ← Finset.sum_mul, Finset.sum_sub_distrib,
      t.total_of_fintype, x.total_of_fintype]
    norm_num

/-- A coordinate attaining the maximum is zero after radial projection.
Source: explicit simplex expansion of Hatcher pp.233–234. -/
lemma radial_boundary (t : Δ n) (ht : ∀ i, 0 < t.weights i) (x : Δ n) (hx : x ≠ t) :
    radial t ht x hx ∈ standardSimplexBoundary n := by
  obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
    (fun i ↦ (t.weights i - x.weights i) / t.weights i)
  refine ⟨i, ?_⟩
  change t.weights i + (x.weights i - t.weights i) / scale t x = 0
  have hs := ne_of_gt (scale_pos t x ht hx)
  have he : scale t x * t.weights i = t.weights i - x.weights i := by
    rw [scale, hi]
    exact div_mul_cancel₀ _ (ne_of_gt (ht i))
  have hd : (x.weights i - t.weights i) / scale t x = -(t.weights i) :=
    (div_eq_iff hs).2 (by nlinarith)
  rw [hd]
  ring

/-- The scale equals one on the boundary, so radial projection fixes it.
Source: explicit simplex expansion of Hatcher pp.233–234. -/
lemma radial_fix (t : Δ n) (ht : ∀ i, 0 < t.weights i) (x : Δ n) (hx : x ≠ t)
    (hb : x ∈ standardSimplexBoundary n) : radial t ht x hx = x := by
  ext i
  change t.weights i + (x.weights i - t.weights i) / scale t x = x.weights i
  rw [scale_eq_one t x ht hb, div_one]
  ring

/-- Radial projection is continuous on the punctured simplex, where its
denominator is strictly positive. Source: Hatcher pp.233–234, radial comparison. -/
lemma continuous_radial (t : Δ n) (ht : ∀ i, 0 < t.weights i) :
    Continuous (fun x : {x : Δ n // x ≠ t} ↦ radial t ht x.val x.property) := by
  apply (StdSimplex.isEmbedding_toFun_comp_weights ℝ _).continuous_iff.2
  apply continuous_pi
  intro i
  change Continuous (fun x : {x : Δ n // x ≠ t} ↦
    t.weights i + (x.val.weights i - t.weights i) / scale t x.val)
  exact continuous_const.add
    (((StdSimplex.continuous_weights_apply ℝ i).comp continuous_subtype_val).sub
      continuous_const |>.div ((continuous_scale t).comp continuous_subtype_val)
      (fun x ↦ ne_of_gt (scale_pos t x.val ht x.property)))

/-- Linear interpolation between a punctured point and its radial boundary point.
Nonnegative convex coefficients preserve the simplex. Source: Hatcher pp.2–3 and 233–234. -/
def interpolate (t : Δ n) (ht : ∀ i, 0 < t.weights i)
    (s : unitInterval) (x : Δ n) (hx : x ≠ t) : Δ n where
  weights := Finsupp.equivFunOnFinite.symm
    (fun i ↦ (1 - (s : ℝ)) * x.weights i + s * (radial t ht x hx).weights i)
  nonneg i := add_nonneg
    (mul_nonneg (sub_nonneg.mpr s.property.2) (x.weights_nonneg i))
    (mul_nonneg s.property.1 ((radial t ht x hx).weights_nonneg i))
  total := by
    rw [Finsupp.sum_fintype _ _ (by simp)]
    change ∑ i, ((1 - (s : ℝ)) * x.weights i + s * (radial t ht x hx).weights i) = 1
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      x.total_of_fintype, (radial t ht x hx).total_of_fintype]
    ring

/-- A coordinate that vanishes at the radial endpoint stays strictly below the
positive center coordinate throughout the homotopy. Source: radial argument, Hatcher pp.233–234. -/
lemma interpolate_ne (t : Δ n) (ht : ∀ i, 0 < t.weights i)
    (s : unitInterval) (x : Δ n) (hx : x ≠ t) : interpolate t ht s x hx ≠ t := by
  obtain ⟨i, hi⟩ := radial_boundary t ht x hx
  have hr : t.weights i + (x.weights i - t.weights i) / scale t x = 0 := hi
  have he : (x.weights i - t.weights i) / scale t x * scale t x =
      x.weights i - t.weights i := div_mul_cancel₀ _ (ne_of_gt (scale_pos t x ht hx))
  have hlt : x.weights i < t.weights i := by
    have hm := mul_pos (ht i) (scale_pos t x ht hx)
    have hd : (x.weights i - t.weights i) / scale t x = -t.weights i := by linarith
    rw [hd] at he
    nlinarith
  intro hh
  have hh' := congrArg (fun y : Δ n ↦ y.weights i) hh
  change (1 - (s : ℝ)) * x.weights i + s * (radial t ht x hx).weights i = t.weights i at hh'
  rw [hi, mul_zero, add_zero] at hh'
  have hprod := mul_nonneg s.property.1 (x.weights_nonneg i)
  nlinarith

/-- The radial interpolation is jointly continuous in time and position.
Source: explicit simplex expansion of Hatcher pp.233–234. -/
lemma continuous_interpolate (t : Δ n) (ht : ∀ i, 0 < t.weights i) :
    Continuous (fun p : unitInterval × {x : Δ n // x ≠ t} ↦
      interpolate t ht p.1 p.2.val p.2.property) := by
  apply (StdSimplex.isEmbedding_toFun_comp_weights ℝ _).continuous_iff.2
  apply continuous_pi
  intro i
  change Continuous (fun p : unitInterval × {x : Δ n // x ≠ t} ↦
    (1 - (p.1 : ℝ)) * p.2.val.weights i +
      p.1 * (radial t ht p.2.val p.2.property).weights i)
  exact ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).mul
    ((StdSimplex.continuous_weights_apply ℝ i).comp
      (continuous_subtype_val.comp continuous_snd))).add
    ((continuous_subtype_val.comp continuous_fst).mul
      ((StdSimplex.continuous_weights_apply ℝ i).comp ((continuous_radial t ht).comp
        continuous_snd)))

/-- A positive-coordinate point lies off the barycentric boundary.
Source: Hatcher p.103, simplex faces. -/
lemma boundary_subset (t : Δ n) (ht : ∀ i, 0 < t.weights i) :
    standardSimplexBoundary n ⊆ ({t} : Set (Δ n))ᶜ := by
  rintro x ⟨i, hi⟩ hx
  have hx' : x = t := hx
  subst x
  exact (ne_of_gt (ht i)) hi

end SimplexRadial

/-- Radial projection from an interior point strongly deformation retracts the
punctured simplex onto its boundary. Source: Hatcher pp.233–234.
Write m(x)=max_i (t_i-x_i)/t_i. The coordinate sums imply m>0 away from t,
nonnegative x_i imply m≤1, and boundary points have m=1. The point
r_i=t_i+(x_i-t_i)/m lies in the simplex and a maximizing coordinate is zero.
It depends continuously on x and fixes the boundary. Linear interpolation
between x and r(x) stays away from t: a maximizing coordinate remains below
the positive corresponding coordinate of t. This interpolation fixes the boundary. -/
def standardSimplexRadialDeformation (n : ℕ) (t : SimplexRadial.Δ n)
    (ht : ∀ i, 0 < t.weights i) :
    Topology.Homotopy.StrongDeformationRetract (standardSimplexBoundary n)
      ({t} : Set (SimplexRadial.Δ n))ᶜ (SimplexRadial.boundary_subset t ht) where
  retraction := ⟨fun x ↦ ⟨SimplexRadial.radial t ht x.val x.property,
      SimplexRadial.radial_boundary t ht x.val x.property⟩,
    (SimplexRadial.continuous_radial t ht).subtype_mk _⟩
  retraction_inclusion := by
    ext x : 2
    exact SimplexRadial.radial_fix t ht x.val
      (SimplexRadial.boundary_subset t ht x.property) x.property
  homotopy := {
    toFun := fun p ↦ ⟨SimplexRadial.interpolate t ht p.1 p.2.val p.2.property,
      SimplexRadial.interpolate_ne t ht p.1 p.2.val p.2.property⟩
    continuous_toFun := (SimplexRadial.continuous_interpolate t ht).subtype_mk _
    map_zero_left := by
      intro x
      apply Subtype.ext
      ext i
      simp [SimplexRadial.interpolate]
    map_one_left := by
      intro x
      apply Subtype.ext
      ext i
      simp [SimplexRadial.interpolate]
      rfl
    prop' := by
      intro s x hx
      apply Subtype.ext
      ext i
      change (1 - (s : ℝ)) * x.val.weights i +
        s * (SimplexRadial.radial t ht x.val x.property).weights i = x.val.weights i
      rw [SimplexRadial.radial_fix t ht x.val x.property hx]
      ring }

/-- The punctured standard simplex strongly deformation retracts onto its boundary.
Source: Hatcher pp.233–234; the explicit barycentric radial construction above
proves existence, including its continuous homotopy fixing the boundary. -/
theorem standardSimplex_radial_deformation (n : ℕ) (t : SimplexRadial.Δ n)
    (ht : ∀ i, 0 < t.weights i) :
    Nonempty (Topology.Homotopy.StrongDeformationRetract (standardSimplexBoundary n)
      ({t} : Set (SimplexRadial.Δ n))ᶜ (SimplexRadial.boundary_subset t ht)) :=
  ⟨standardSimplexRadialDeformation n t ht⟩

end HolomorphicAnosov

