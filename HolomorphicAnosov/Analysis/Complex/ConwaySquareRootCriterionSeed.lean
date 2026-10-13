import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Neighborhoods

namespace HolomorphicAnosov

open Function Filter Metric Set
open scoped Topology _root_.Topology

/-- The initial square-root and reciprocal construction in Conway VII.4.3. It gives an
injective holomorphic map from U into the unit disk with nonzero derivative. -/
theorem conway_square_root_criterion_seed
    {U : Set ℂ} (hUopen : IsOpen U) (hUconnected : IsConnected U)
    (hUproper : U ≠ Set.univ)
    (hsqrt : ∀ f : ℂ → ℂ, DifferentiableOn ℂ f U → (∀ z ∈ U, f z ≠ 0) →
      ∃ g : ℂ → ℂ, DifferentiableOn ℂ g U ∧ ∀ z ∈ U, (g z) ^ 2 = f z) :
    ∃ f : ℂ → ℂ, DifferentiableOn ℂ f U ∧ Set.InjOn f U ∧
      Set.MapsTo f U (Metric.ball 0 1) ∧ ∀ z ∈ U, deriv f z ≠ 0 := by
  have hseed : ∃ g : ℂ → ℂ, DifferentiableOn ℂ g U ∧ Set.InjOn g U ∧
      ¬Dense (g '' U) ∧ ∀ z ∈ U, deriv g z ≠ 0 := by
    rw [Set.ne_univ_iff_exists_notMem] at hUproper
    obtain ⟨b, hb⟩ := hUproper
    obtain ⟨g, hg, hsq⟩ := hsqrt (fun z ↦ z - b)
      (differentiableOn_id.sub_const b)
      (fun z hz ↦ sub_ne_zero.mpr (ne_of_mem_of_not_mem hz hb))
    have hg0 : ∀ z ∈ U, g z ≠ 0 := by
      intro z hz he
      have h := hsq z hz
      simp only [he, zero_pow (by decide : 2 ≠ 0)] at h
      exact (sub_ne_zero.mpr (ne_of_mem_of_not_mem hz hb)) h.symm
    have hginj : Set.InjOn g U := by
      intro z hz w hw he
      have h : z - b = w - b := (hsq z hz).symm.trans
        ((congrArg (fun t : ℂ ↦ t ^ 2) he).trans (hsq w hw))
      exact sub_left_injective (b := b) h
    have hstrict : ∀ z ∈ U, HasStrictDerivAt g (2 * g z)⁻¹ z := by
      intro z hz
      apply HasStrictDerivAt.of_local_left_inverse
      · exact hg.continuousOn.continuousAt (hUopen.mem_nhds hz)
      · have hpoly : HasStrictDerivAt (fun q : ℂ ↦ q ^ 2 + b) (2 * g z) (g z) := by
          simpa using (hasStrictDerivAt_pow 2 (g z)).add_const b
        exact hpoly
      · simpa using hg0 z hz
      · filter_upwards [hUopen.mem_nhds hz] with w hw
        rw [hsq w hw]
        ring
    refine ⟨g, hg, hginj, ?_, fun z hz ↦ ?_⟩
    · simp only [Dense, not_forall, mem_closure_iff_frequently, not_frequently]
      obtain ⟨x, hx⟩ := hUconnected.nonempty
      use -g x
      have him : g '' U ∈ 𝓝 (g x) := by
        rw [← (hstrict x hx).map_nhds_eq (by simpa using hg0 x hx)]
        exact Filter.image_mem_map (hUopen.mem_nhds hx)
      rw [nhds_neg, eventually_neg]
      filter_upwards [him]
      rintro _ ⟨a₁, ha₁, rfl⟩ ⟨a₂, ha₂, hac⟩
      have he : a₁ = a₂ := by
        have hsqeq : a₁ - b = a₂ - b := by
          calc
            a₁ - b = (g a₁) ^ 2 := (hsq a₁ ha₁).symm
            _ = (-g a₂) ^ 2 := by rw [hac]; simp
            _ = (g a₂) ^ 2 := neg_sq _
            _ = a₂ - b := hsq a₂ ha₂
        exact sub_left_injective (b := b) hsqeq
      subst a₂
      apply hg0 a₁ ha₁
      have hzero : g a₁ + g a₁ = 0 := eq_neg_iff_add_eq_zero.mp hac
      linear_combination hzero / 2
    · simpa [(hstrict z hz).hasDerivAt.deriv] using hg0 z hz
  obtain ⟨g, hg, hginj, hgdense, hgd⟩ := hseed
  obtain ⟨x, ε, hε, hdist⟩ : ∃ (x : ℂ) (ε : ℝ), 0 < ε ∧
      ∀ z ∈ U, ε < dist (g z) x := by
    simpa [Dense, mem_closure_iff_nhds_basis Metric.nhds_basis_closedBall] using hgdense
  have hgne : ∀ z ∈ U, g z ≠ x := fun z hz ↦ by
    simpa using hε.trans (hdist z hz)
  refine ⟨fun z ↦ (ε : ℂ) / (g z - x), ?_, ?_, ?_, ?_⟩
  · exact (differentiableOn_const (c := (ε : ℂ))).fun_div (hg.sub_const x)
      (fun z hz ↦ sub_ne_zero.mpr (hgne z hz))
  · intro z hz w hw he
    apply hginj hz hw
    have hεc : (ε : ℂ) ≠ 0 := by exact_mod_cast hε.ne'
    have heq : g z - x = g w - x := by
      exact inv_injective ((mul_left_cancel₀ hεc) (by simpa [div_eq_mul_inv] using he))
    exact sub_left_injective heq
  · intro z hz
    rw [mem_ball_zero_iff, norm_div, Complex.norm_real, Real.norm_of_nonneg hε.le,
      div_lt_one₀]
    · simpa [dist_eq_norm] using hdist z hz
    · exact norm_pos_iff.mpr (sub_ne_zero.mpr (hgne z hz))
  · intro z hz
    have hdz := (hg z hz).differentiableAt (hUopen.mem_nhds hz)
    rw [((hasDerivAt_const z (ε : ℂ)).fun_div
      (hdz.hasDerivAt.sub_const x) (sub_ne_zero.mpr (hgne z hz))).deriv]
    simp [hε.ne', hgd z hz, sub_ne_zero.mpr (hgne z hz)]


end HolomorphicAnosov
