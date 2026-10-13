import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import HolomorphicAnosov.Analysis.Distribution.ScalarDbarTest
import HolomorphicAnosov.Analysis.Distribution.ScalarDbarTestApply
import HolomorphicAnosov.Analysis.Distribution.LocalAntiholomorphicIntegrationByParts

open MeasureTheory TopologicalSpace

namespace HolomorphicAnosov

open Set
open scoped ContDiff Topology _root_.Topology

/-- The complete Step 5 implication for the scalar Demailly argument: any
smooth local representative of the given closed current has vanishing
antiholomorphic derivatives pointwise. This is the agent-written expansion of
Demailly I (2.5)–(2.6), p.15, used in the scalar specialization of (3.29)(a),
pp.28–29. The proof extends tests, not the representative, applies compact-test
integration by parts, and then uses smooth-test uniqueness and continuity.
It adds no smooth-representative premise to the public theorem: constructing
that representative remains Steps 1–4 of its existing proof obligation. -/
theorem smooth_representative_antiholomorphicPartial_eq_zero {n : ℕ}
    (U V : Opens (Fin n → ℂ)) (hVU : V ≤ U)
    (T : TestFunction U ℂ ⊤ →L[ℂ] ℂ)
    (hT : ∀ j φ, -T (scalarDbarTest U j φ) = 0)
    (g : (Fin n → ℂ) → ℂ) (hg : ContDiffOn ℝ ∞ g (V : Set _))
    (hrepr : ∀ φ : TestFunction U ℂ ⊤,
      tsupport (φ : (Fin n → ℂ) → ℂ) ⊆ (V : Set _) →
        T φ = ∫ x in (V : Set _), g x * φ x) :
    ∀ j x, x ∈ V → Analysis.antiholomorphicPartial g j x = 0 := by
  have hweak (j : Fin n) (φ : TestFunction V ℂ ⊤) :
      (∫ x, Analysis.antiholomorphicPartial g j x * φ x) = 0 := by
    let φU : TestFunction U ℂ ⊤ :=
      ⟨φ, φ.contDiff, φ.hasCompactSupport, φ.tsupport_subset.trans hVU⟩
    let ψ := scalarDbarTest V j φ
    let ψU : TestFunction U ℂ ⊤ :=
      ⟨ψ, ψ.contDiff, ψ.hasCompactSupport, ψ.tsupport_subset.trans hVU⟩
    have hcomm : scalarDbarTest U j φU = ψU := by
      ext x
      rw [scalarDbarTest_apply]
      change Analysis.antiholomorphicPartial φ j x = scalarDbarTest V j φ x
      exact (scalarDbarTest_apply V j φ x).symm
    have hz := hT j φU
    rw [hcomm, hrepr ψU ψ.tsupport_subset] at hz
    have hset : (∫ x in (V : Set _), g x * ψ x) = ∫ x, g x * ψ x :=
      setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx ↦ by
        rw [show ψ x = 0 from image_eq_zero_of_notMem_tsupport (fun hx' ↦ hx (ψ.tsupport_subset hx')), mul_zero]
    change -(∫ x in (V : Set _), g x * ψ x) = 0 at hz
    rw [hset] at hz
    exact (local_antiholomorphic_integration_by_parts V g hg j φ).trans hz
  intro j
  have hdc : ContinuousOn (Analysis.antiholomorphicPartial g j) (V : Set _) := by
    have hd := hg.continuousOn_fderiv_of_isOpen V.isOpen (by simp)
    exact ((hd.clm_apply continuousOn_const).add
      (continuousOn_const.mul (hd.clm_apply continuousOn_const))).div_const 2
  have hae : ∀ᵐ x ∂volume, x ∈ (V : Set _) →
      Analysis.antiholomorphicPartial g j x = 0 := by
    apply V.isOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero
      (hdc.locallyIntegrableOn V.isOpen.measurableSet)
    intro f hf hs hsub
    let φ : TestFunction V ℂ ⊤ :=
      ⟨fun x ↦ (f x : ℂ), Complex.ofRealCLM.contDiff.comp hf,
        hs.comp_left (g := Complex.ofReal) (by simp),
        (tsupport_comp_subset (g := Complex.ofReal) (by simp) f).trans hsub⟩
    convert hweak j φ using 1
    congr 1
    funext x
    change f x • Analysis.antiholomorphicPartial g j x =
      Analysis.antiholomorphicPartial g j x * (f x : ℂ)
    simp [Complex.real_smul, mul_comm]
  exact MeasureTheory.Measure.eqOn_open_of_ae_eq
    ((ae_restrict_iff' V.isOpen.measurableSet).mpr hae) V.isOpen hdc continuousOn_const


end HolomorphicAnosov
