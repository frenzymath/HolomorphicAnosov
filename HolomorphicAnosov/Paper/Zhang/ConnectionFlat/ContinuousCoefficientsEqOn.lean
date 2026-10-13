import HolomorphicAnosov.Analysis.Distribution.HolomorphicSectionCriterion

open Filter MeasureTheory TopologicalSpace Set
noncomputable section
namespace HolomorphicAnosov
namespace ConnectionFlatEstimates

/-- Two continuous coefficients representing the same current agree pointwise on the smaller open
set. -/
theorem continuous_coefficients_eqOn_of_current {n : ℕ}
    (Ω V : Opens (Fin n → ℂ)) (hVΩ : V ≤ Ω)
    (a h : (Fin n → ℂ) → ℂ) (ha : ContinuousOn a V) (hh : ContinuousOn h V)
    (T : TestFunction Ω ℂ ⊤ →L[ℂ] ℂ)
    (hregular : ∀ φ : TestFunction Ω ℂ ⊤,
      T φ = ∫ z in (Ω : Set (Fin n → ℂ)), a z * φ z ∂volume)
    (hrep : ∀ φ : TestFunction Ω ℂ ⊤,
      tsupport (φ : (Fin n → ℂ) → ℂ) ⊆ (V : Set (Fin n → ℂ)) →
        T φ = ∫ z in (V : Set (Fin n → ℂ)), h z * φ z ∂volume) :
    EqOn a h V := by
  have haV := ha.locallyIntegrableOn V.isOpen.measurableSet (μ := volume)
  have hhV := hh.locallyIntegrableOn V.isOpen.measurableSet (μ := volume)
  have hae : ∀ᵐ z ∂volume, z ∈ V → a z - h z = 0 := by
    apply V.isOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero (haV.sub hhV)
    intro g hg hgc hgs
    let ψ : TestFunction V ℝ ⊤ := ⟨g, hg, hgc, hgs⟩
    let φ : TestFunction Ω ℂ ⊤ :=
      ⟨fun z ↦ (g z : ℂ), Complex.ofRealCLM.contDiff.comp hg,
        hgc.comp_left (g := Complex.ofReal) (by simp),
        ((tsupport_comp_subset (g := Complex.ofReal) (by simp) g).trans hgs).trans hVΩ⟩
    have hφsupport : tsupport (φ : (Fin n → ℂ) → ℂ) ⊆ (V : Set _) :=
      (tsupport_comp_subset (g := Complex.ofReal) (by simp) g).trans hgs
    have hzero (W : Opens (Fin n → ℂ)) (hVW : V ≤ W) (b : (Fin n → ℂ) → ℂ) :
        (∫ z in (W : Set (Fin n → ℂ)), b z * φ z ∂volume) =
          ∫ z, g z • b z ∂volume := by
      rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
      · congr 1
        funext z
        change b z * (g z : ℂ) = g z • b z
        simp only [Complex.real_smul, mul_comm]
      · intro z hz
        rw [image_eq_zero_of_notMem_tsupport
          (fun ht ↦ hz (hVW (hφsupport ht))), mul_zero]
    have heq : (∫ z, g z • a z ∂volume) = ∫ z, g z • h z ∂volume := by
      have he := (hregular φ).symm.trans (hrep φ hφsupport)
      simpa only [hzero Ω hVΩ a, hzero V le_rfl h] using he
    change (∫ z, g z • (a z - h z) ∂volume) = 0
    simp_rw [smul_sub]
    rw [integral_sub (show Integrable (fun z ↦ g z • a z) volume from ψ.integrable_smul haV)
      (show Integrable (fun z ↦ g z • h z) volume from ψ.integrable_smul hhV), heq, sub_self]
  apply Measure.eqOn_open_of_ae_eq (μ := volume) _ V.isOpen ha hh
  change ∀ᵐ z ∂volume.restrict (V : Set (Fin n → ℂ)), a z = h z
  rw [ae_restrict_iff' V.isOpen.measurableSet]
  filter_upwards [hae] with z hz hzV
  exact sub_eq_zero.mp (hz hzV)

end ConnectionFlatEstimates
end HolomorphicAnosov
