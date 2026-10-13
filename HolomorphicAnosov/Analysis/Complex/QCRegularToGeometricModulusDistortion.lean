import HolomorphicAnosov.Analysis.Complex.QCRegularEnergyArea
import HolomorphicAnosov.Analysis.Complex.QCMarkedRectangleEnergyBridge

/-!
# Regular planar quasiconformal maps distort marked modulus

Source: Lehto–Virtanen, *Quasiconformal Mappings in the Plane*, second edition
(1973), Chapter I §3.3 and Theorem 3.1, printed pp.17–19, especially equations
(3.1)–(3.4).
-/

namespace HolomorphicAnosov.Analysis

open Set Filter _root_.Topology MarkedRectangle
open scoped ContDiff

/-- A sense-preserving regular planar map distorts marked modulus by at most K. -/
theorem qc_regular_to_geometric_modulus_distortion
    (U V : Set ℂ) (hU_open : IsOpen U) (hV_open : IsOpen V)
    (hU_connected : IsConnected U) (hV_connected : IsConnected V)
    (f : OpenPartialHomeomorph ℂ ℂ)
    (hf_source : f.source = U) (hf_target : f.target = V)
    (hC1 : ContDiffOn ℝ 1 (f : ℂ → ℂ) U)
    (hderiv : ∀ z ∈ U, ∃ A : ℂ ≃L[ℝ] ℂ,
      HasFDerivAt (f : ℂ → ℂ) (A : ℂ →L[ℝ] ℂ) z ∧ 0 < (A : ℂ →L[ℝ] ℂ).det)
    (K : ℝ)
    (hDistortion : ∀ z ∈ U, ∀ v w : ℂ, ‖v‖ = 1 → ‖w‖ = 1 →
      ‖fderiv ℝ (f : ℂ → ℂ) z v‖ ≤ K * ‖fderiv ℝ (f : ℂ → ℂ) z w‖)
    (Q : Set ℂ) (p : Fin 4 → ℂ) (m m' : ℝ)
    (hQcompact : IsCompact (closure Q)) (hQinside : closure Q ⊆ U)
    (hQmod : HasMarkedConformalModulus Q p m)
    (hImageMod : HasMarkedConformalModulus (f '' Q) (fun i ↦ f (p i)) m') :
    m' ≤ K * m := by
  have hK : 1 ≤ K := by
    obtain ⟨z, hz⟩ := hU_connected.nonempty
    obtain ⟨A, hA, _⟩ := hderiv z hz
    have hn : 0 < ‖A 1‖ := norm_pos_iff.mpr (by
      intro he
      exact one_ne_zero (A.injective (he.trans A.map_zero.symm)))
    have hd := hDistortion z hz 1 1 (by simp) (by simp)
    rw [hA.fderiv] at hd
    change ‖A 1‖ ≤ K * ‖A 1‖ at hd
    nlinarith
  have hEnergy (S : Set ℂ) (hS : MeasurableSet S) (hSU : S ⊆ U) :
      (∫⁻ z in S, ENNReal.ofReal (‖fderiv ℝ (f : ℂ → ℂ) z 1‖ ^ 2)) ≤
        ENNReal.ofReal K * MeasureTheory.volume (f '' S) := by
    apply HolomorphicAnosov.qc_regular_energy_le_image_area hS
      (f.injOn.mono (hf_source.symm ▸ hSU)) (zero_le_one.trans hK)
    · exact fun z hz ↦ hderiv z (hSU hz)
    · exact fun z hz ↦ hDistortion z (hSU hz)
  exact qc_marked_rectangle_energy_bridge U V hU_open hV_open hU_connected hV_connected
    f hf_source hf_target hC1 hderiv K hK hDistortion Q p m m' hQcompact hQinside hQmod
    hImageMod hEnergy

end HolomorphicAnosov.Analysis

