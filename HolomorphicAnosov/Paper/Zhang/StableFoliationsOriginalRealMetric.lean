import HolomorphicAnosov.Geometry.HermitianTangentMetric
import HolomorphicAnosov.Geometry.BiholomorphToReal
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Geometry.Manifold.Riemannian.Basic
import HolomorphicAnosov.Paper.Zhang.StableFoliationsRealPairingPos
import HolomorphicAnosov.Paper.Zhang.StableFoliationsRealPairingSymm
import HolomorphicAnosov.Paper.Zhang.StableFoliationsPositiveFormUnitSublevelBounded
import HolomorphicAnosov.Paper.Zhang.StableFoliationsOriginalRealBilinear
import HolomorphicAnosov.Paper.Zhang.StableFoliationsOriginalRealBilinearApply

noncomputable section
open scoped ContDiff Manifold Topology
open Filter Set _root_.Topology
universe u
namespace HolomorphicAnosov
attribute [local instance] complex_isManifold_real
namespace StableFoliationsSupport

set_option maxHeartbeats 800000 in
/-- The Riemannian metric on the real tangent bundle induced by the real part of the Hermitian
pairing. -/
noncomputable def originalRealMetric {d : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (ComplexModel d) M] [IsManifold (complexModel d) ∞ M] (h : HermitianTangentMetricCore d M) :
    Bundle.RiemannianMetric (fun x : M ↦ TangentSpace (realModel d) x) := by
  let inn : (x : M) → TangentSpace (realModel d) x →L[ℝ] TangentSpace (realModel d) x →L[ℝ] ℝ := originalRealBilinear h
  have hb (x : M) : Bornology.IsVonNBounded ℝ {v : TangentSpace (realModel d) x | inn x v v < 1} := by
    let e := tangentSpaceCastModel (realModel d) x
    let b : ComplexModel d →ₗ[ℝ] ComplexModel d →ₗ[ℝ] ℝ :=
      LinearMap.mk₂ ℝ (fun v w ↦ inn x (e.symm v) (e.symm w))
        (by intros; simp) (by intros; simp) (by intros; simp) (by intros; simp)
    let c := (LinearMap.toContinuousLinearMap (𝕜 := ℝ)
      (E := ComplexModel d) (F' := ℝ)).toLinearMap.comp b
    let B : ComplexModel d →L[ℝ] ComplexModel d →L[ℝ] ℝ := LinearMap.toContinuousLinearMap c
    have hB : ∀ v w, B v w = inn x (e.symm v) (e.symm w) := by intros; rfl
    have hpB (v : ComplexModel d) (hv : v ≠ 0) : 0 < B v v := by
      rw [hB]
      change 0 < originalRealBilinear h x (e.symm v) (e.symm v)
      rw [originalRealBilinear_apply]
      apply real_pairing_pos h x
      exact fun hz ↦ hv (e.symm.injective (by simpa using hz))
    have hbB := (positive_form_unit_sublevel_bounded B hpB).image e.symm.toContinuousLinearMap
    convert hbB using 1
    ext v
    constructor
    · intro hv
      exact ⟨e v, by simpa [hB] using hv, by simp⟩
    · rintro ⟨w, hw, rfl⟩
      simpa [hB] using hw
  have hc (x : M) : ContinuousAt (fun v : TangentSpace (realModel d) x ↦ inn x v v) 0 := by
    let e := tangentSpaceCastModel (realModel d) x
    let b : ComplexModel d →ₗ[ℝ] ComplexModel d →ₗ[ℝ] ℝ :=
      LinearMap.mk₂ ℝ (fun v w ↦ inn x (e.symm v) (e.symm w))
        (by intros; simp) (by intros; simp) (by intros; simp) (by intros; simp)
    let c := (LinearMap.toContinuousLinearMap (𝕜 := ℝ)
      (E := ComplexModel d) (F' := ℝ)).toLinearMap.comp b
    let B : ComplexModel d →L[ℝ] ComplexModel d →L[ℝ] ℝ := LinearMap.toContinuousLinearMap c
    have hcB : Continuous (fun v : ComplexModel d ↦ B v v) := B.continuous.clm_apply continuous_id
    exact (hcB.comp e.continuous).continuousAt
  exact {
  inner := inn
  symm x v w := by
    change originalRealBilinear h x v w = originalRealBilinear h x w v
    simp only [originalRealBilinear_apply]
    exact real_pairing_symm h x v w
  pos x v hv := by
    change 0 < originalRealBilinear h x v v
    rw [originalRealBilinear_apply]
    exact real_pairing_pos h x v hv
  continuousAt := hc
  isVonNBounded := hb }

end StableFoliationsSupport
end HolomorphicAnosov
