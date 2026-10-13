import HolomorphicAnosov.Analysis.MarkedRectangleG3AdjacentBoundaryPhase
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Separation.Hausdorff

open Set Filter
open scoped Topology _root_.Topology
noncomputable section
namespace HolomorphicAnosov.Analysis.MarkedRectangle

/-- On either exterior real ray the four-factor branch has zero real part.
Source: Bak--Newman, pp.189--190. The number of factors with negative real
argument is zero or four, so the fixed prefactor -i gives a purely imaginary
value in both cases. -/
theorem schwarzChristoffel_outer_integrand_re_zero (x : Fin 4 → ℝ) {u : ℝ}
    (hout : (∀ j, u < x j) ∨ (∀ j, x j < u)) :
    (-Complex.I * ∏ j : Fin 4,
      Complex.exp (-Complex.log ((u : ℂ) - (x j : ℂ)) / 2)).re = 0 := by
  classical
  have hne (j : Fin 4) : u ≠ x j := by
    rcases hout with h | h
    · exact (h j).ne
    · exact (h j).ne.symm
  have hneC (j : Fin 4) : (u : ℂ) ≠ (x j : ℂ) := by exact_mod_cast hne j
  have hp := (schwarzChristoffel_boundary_branch x).2 u hne
  rw [((schwarzChristoffel_boundary_branch x).1 (u : ℂ) (by simp) hneC).2] at hp
  rw [hp]
  have hcast : (∏ j : Fin 4, (Real.exp (-Real.log |u - x j| / 2) : ℂ)) =
      ((∏ j : Fin 4, Real.exp (-Real.log |u - x j| / 2) : ℝ) : ℂ) := by simp
  rw [hcast]
  generalize (∏ j : Fin 4, Real.exp (-Real.log |u - x j| / 2) : ℝ) = r
  rcases hout with h | h
  · have hc : (Finset.univ.filter (fun j : Fin 4 ↦ u < x j)).card = 4 := by simp [h]
    rw [hc]
    norm_num [pow_succ, mul_assoc, Complex.I_mul_I, Complex.mul_re]
  · have hc : (Finset.univ.filter (fun j : Fin 4 ↦ u < x j)).card = 0 := by
      simp [fun j ↦ not_lt.mpr (h j).le]
    rw [hc]
    simp [Complex.mul_re]

/-- Exterior boundary increments have zero real part. Source: the primitive
increment formula in Bak--Newman p.189 and its exterior phases on p.190. -/
theorem schwarzChristoffel_outer_increment_re (x : Fin 4 → ℝ) {a b : ℝ}
    (hab : a ≤ b) (hout : (∀ j, b < x j) ∨ (∀ j, x j < a))
    (Wbar : ℂ → ℂ)
    (hinc : Wbar (b : ℂ) - Wbar (a : ℂ) = ∫ t in a..b,
      -Complex.I * ∏ j : Fin 4,
        Complex.exp (-Complex.log ((t : ℂ) - (x j : ℂ)) / 2)) :
    (Wbar (b : ℂ)).re = (Wbar (a : ℂ)).re := by
  let f : ℝ → ℂ := fun t ↦ -Complex.I * ∏ j : Fin 4,
    Complex.exp (-Complex.log ((t : ℂ) - (x j : ℂ)) / 2)
  have havoid (j : Fin 4) : x j ∉ Icc a b := by
    intro ht
    rcases hout with h | h
    · exact (h j).not_ge ht.2
    · exact (h j).not_ge ht.1
  have hint : IntervalIntegrable f MeasureTheory.volume a b :=
    (schwarzChristoffel_integrand_continuousOn_interval x havoid).intervalIntegrable_of_Icc hab
  have hre : (∫ t in a..b, f t).re = ∫ t in a..b, (f t).re :=
    (Complex.reCLM.intervalIntegral_comp_comm hint).symm
  have hzero : (∫ t in a..b, (f t).re) = 0 := by
    calc
      _ = ∫ t in a..b, (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro t ht
        have ht' : t ∈ Icc a b := by simpa [uIcc_of_le hab] using ht
        apply schwarzChristoffel_outer_integrand_re_zero
        rcases hout with h | h
        · exact Or.inl (fun j ↦ ht'.2.trans_lt (h j))
        · exact Or.inr (fun j ↦ (h j).trans_le ht'.1)
      _ = 0 := by simp
  have hR := congrArg Complex.re hinc
  change (Wbar (b : ℂ)).re - (Wbar (a : ℂ)).re = (∫ t in a..b, f t).re at hR
  rw [hre, hzero] at hR
  exact sub_eq_zero.mp hR

/-- The real coordinate at a finite end of a constant-coordinate ray equals
its limit at infinity. The two applications express the endpoint alignment in
Bak--Newman p.190 once the shared limit at the two real infinities is known.
Continuity extends the equality from each open ray to its finite endpoint. -/
theorem outer_real_coordinates_eq_shared_limit {a b L : ℝ} (f : ℝ → ℝ)
    (hc : Continuous f) (htop : Tendsto f atTop (𝓝 L))
    (hbot : Tendsto f atBot (𝓝 L))
    (hleft : ∀ u v, u ≤ v → v < a → f u = f v)
    (hright : ∀ u v, u ≤ v → b < u → f u = f v) :
    f a = L ∧ f b = L := by
  have hleftEq : EqOn f (fun _ ↦ L) (Iio a) := by
    intro t ht
    have hevent : f =ᶠ[atBot] (fun _ ↦ f t) := by
      filter_upwards [eventually_le_atBot t] with u hu
      exact hleft u t hu ht
    exact (tendsto_nhds_unique_of_eventuallyEq hbot tendsto_const_nhds hevent).symm
  have hrightEq : EqOn f (fun _ ↦ L) (Ioi b) := by
    intro t ht
    have hevent : f =ᶠ[atTop] (fun _ ↦ f t) := by
      filter_upwards [eventually_ge_atTop t] with u hu
      exact (hright t u hu ht).symm
    exact (tendsto_nhds_unique_of_eventuallyEq htop tendsto_const_nhds hevent).symm
  have hlclosed : EqOn f (fun _ ↦ L) (Iic a) :=
    hleftEq.of_subset_closure hc.continuousOn continuousOn_const Iio_subset_Iic_self
      (by rw [closure_Iio])
  have hrclosed : EqOn f (fun _ ↦ L) (Ici b) :=
    hrightEq.of_subset_closure hc.continuousOn continuousOn_const Ioi_subset_Ici_self
      (by rw [closure_Ioi])
  exact ⟨hlclosed (by simp), hrclosed (by simp)⟩

/-- The two outer prevertices of a Schwarz--Christoffel primitive have equal
real coordinate when its two real infinities have the same finite limit.
Source: Bak--Newman p.190, closed boundary rectangle argument. The exterior
phases force real-coordinate constancy on both rays; the common limit and
finite boundary continuity identify their values at the two prevertices. -/
theorem schwarzChristoffel_outer_prevertices_aligned (x : Fin 4 → ℝ)
    (hx : StrictMono x) (Wbar : ℂ → ℂ) (L : ℂ)
    (hc : Continuous (fun t : ℝ ↦ Wbar (t : ℂ)))
    (htop : Tendsto (fun t : ℝ ↦ Wbar (t : ℂ)) atTop (𝓝 L))
    (hbot : Tendsto (fun t : ℝ ↦ Wbar (t : ℂ)) atBot (𝓝 L))
    (hinc : ∀ a b : ℝ, a ≤ b → (∀ j, x j ∉ Icc a b) →
      Wbar (b : ℂ) - Wbar (a : ℂ) = ∫ t in a..b,
        -Complex.I * ∏ j : Fin 4,
          Complex.exp (-Complex.log ((t : ℂ) - (x j : ℂ)) / 2)) :
    (Wbar (x 0 : ℂ)).re = L.re ∧ (Wbar (x 3 : ℂ)).re = L.re := by
  apply outer_real_coordinates_eq_shared_limit
    (a := x 0) (b := x 3) (fun t : ℝ ↦ (Wbar (t : ℂ)).re)
    (Complex.continuous_re.comp hc)
    (Complex.continuous_re.continuousAt.tendsto.comp htop)
    (Complex.continuous_re.continuousAt.tendsto.comp hbot)
  · intro u v huv hva
    have hbound (j : Fin 4) : v < x j := hva.trans_le (hx.monotone (Fin.zero_le j))
    have havoid (j : Fin 4) : x j ∉ Icc u v := fun hj ↦ (hbound j).not_ge hj.2
    exact (schwarzChristoffel_outer_increment_re x huv (Or.inl hbound) Wbar
      (hinc u v huv havoid)).symm
  · intro u v huv hbu
    have hbound (j : Fin 4) : x j < u := (hx.monotone (Fin.le_last j)).trans_lt hbu
    have havoid (j : Fin 4) : x j ∉ Icc u v := fun hj ↦ (hbound j).not_ge hj.1
    exact (schwarzChristoffel_outer_increment_re x huv (Or.inr hbound) Wbar
      (hinc u v huv havoid)).symm

end HolomorphicAnosov.Analysis.MarkedRectangle

