import HolomorphicAnosov.Analysis.Complex.QCRegularRectangleDistortion
import HolomorphicAnosov.Analysis.Complex.QCMarkedRectangleConjugation

/-!
# The regular rectangle energy bridge for marked modulus

This is the missing analytic bridge in the regular-to-geometric quasiconformal
modulus proof.  It is isolated so its source obligation remains explicit.
-/

namespace HolomorphicAnosov.Analysis

open Set Filter _root_.Topology MarkedRectangle
open scoped ContDiff

/--
Lehto–Virtanen I.§3.3, equations (3.1)–(3.4), supplies the rectangle-model
energy argument needed after the Jacobian estimate.  Given the same regular
orientation-preserving partial homeomorphism and its two marked conformal
modulus witnesses as the parent theorem, and given the already established
image-area estimate for the horizontal derivative, the canonical conformal
rectangle models can be normalized to height one.  Similarity invariance
transports the directional bound, the positive determinant gives
`‖W_x‖² ≤ K det(DW)`, and change of variables plus Tonelli yields the total
horizontal energy bound `∫ ‖W_x‖² ≤ K m'`.  The slice endpoint estimate and
Holder inequality then give `m'² ≤ K m m'`; positivity of the image modulus
allows cancellation and yields `m' ≤ K*m`.

The source proof uses boundary-continuous conformal models and interior
derivatives only.  The literal rectangle energy argument is now proved by
`qc_regular_rectangle_distortion`, using the horizontal slice and Jacobian
providers. The proved `qc_marked_rectangle_conjugation` supplies the
boundary-continuous conformal conjugation with positive derivative, preserved
distortion, and horizontal endpoint separation. The complete bridge uses only
standard axioms.
Source: Lehto–Virtanen, *Quasiconformal Mappings in the Plane* (1973),
Chapter I §3.3 and Theorem 3.1, pp.17–19.
-/
theorem qc_marked_rectangle_energy_bridge
    (U V : Set ℂ) (_hU_open : IsOpen U) (_hV_open : IsOpen V)
    (_hU_connected : IsConnected U) (_hV_connected : IsConnected V)
    (f : OpenPartialHomeomorph ℂ ℂ)
    (hf_source : f.source = U) (hf_target : f.target = V)
    (hC1 : ContDiffOn ℝ 1 (f : ℂ → ℂ) U)
    (hderiv : ∀ z ∈ U, ∃ A : ℂ ≃L[ℝ] ℂ,
      HasFDerivAt (f : ℂ → ℂ) (A : ℂ →L[ℝ] ℂ) z ∧ 0 < (A : ℂ →L[ℝ] ℂ).det)
    (K : ℝ) (hK : 1 ≤ K)
    (hDistortion : ∀ z ∈ U, ∀ v w : ℂ, ‖v‖ = 1 → ‖w‖ = 1 →
      ‖fderiv ℝ (f : ℂ → ℂ) z v‖ ≤ K * ‖fderiv ℝ (f : ℂ → ℂ) z w‖)
    (Q : Set ℂ) (p : Fin 4 → ℂ) (m m' : ℝ)
    (hQcompact : IsCompact (closure Q)) (hQinside : closure Q ⊆ U)
    (hQmod : HasMarkedConformalModulus Q p m)
    (hImageMod : HasMarkedConformalModulus (f '' Q) (fun i ↦ f (p i)) m')
    (_hEnergy : ∀ (S : Set ℂ), MeasurableSet S → S ⊆ U →
      (∫⁻ z in S, ENNReal.ofReal (‖fderiv ℝ (f : ℂ → ℂ) z 1‖ ^ 2)) ≤
        ENNReal.ofReal K * MeasureTheory.volume (f '' S)) :
    m' ≤ K * m := by
  obtain ⟨a, b, A, B, ha, hb, hA, hB, rfl, rfl, F, G, W,
    _hF, _hFbij, _hG, _hGbij, _hWcomp, hWc, hW1, hWbij, hWd, hWdist, hWsep⟩ :=
    qc_marked_rectangle_conjugation U V f hf_source hf_target hC1 hderiv K
      hDistortion Q p m m' hQcompact hQinside hQmod hImageMod
  exact qc_regular_rectangle_distortion ha hb hA hB (zero_le_one.trans hK)
    hWc hW1 hWbij hWd hWdist hWsep

end HolomorphicAnosov.Analysis

