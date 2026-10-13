import HolomorphicAnosov.Geometry.HermitianTangentMetric
import HolomorphicAnosov.Geometry.BiholomorphToReal
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Topology.Algebra.Module.FiniteDimension

noncomputable section
open scoped ContDiff Manifold Topology
open Filter Set _root_.Topology
universe u
namespace HolomorphicAnosov
attribute [local instance] complex_isManifold_real
namespace StableFoliationsSupport

/-- The real Hermitian pairing on each tangent fibre is a continuous real bilinear form. -/
theorem real_pairing_continuous_bilinear {d : ℕ} {M : Type u}
    [TopologicalSpace M] [ChartedSpace (ComplexModel d) M]
    (h : HermitianTangentMetricCore d M) (x : M) :
    ∃ B : TangentSpace (realModel d) x →L[ℝ]
      TangentSpace (realModel d) x →L[ℝ] ℝ,
      ∀ v w, B v w = hermitianTangentRealPairing h x v w := by
  let : InnerProductSpace.Core ℂ (TangentSpace (complexModel d) x) := h x
  let : Inner ℂ (TangentSpace (complexModel d) x) := (h x).toInner
  let b : TangentSpace (realModel d) x →ₗ[ℝ]
      TangentSpace (realModel d) x →ₗ[ℝ] ℝ :=
    LinearMap.mk₂ ℝ (hermitianTangentRealPairing h x)
      (by intros; simp [hermitianTangentRealPairing, hermitianTangentPairing,
        InnerProductSpace.Core.inner_add_right])
      (by
        intro c m n
        simp only [hermitianTangentRealPairing, hermitianTangentPairing,
          map_smul]
        rw [← algebraMap_smul ℂ c]
        rw [InnerProductSpace.Core.inner_smul_ofReal_right]
        simp [mul_comm])
      (by intros; simp [hermitianTangentRealPairing, hermitianTangentPairing,
        InnerProductSpace.Core.inner_add_left])
      (by
        intro c m n
        simp only [hermitianTangentRealPairing, hermitianTangentPairing,
          map_smul]
        rw [← algebraMap_smul ℂ c]
        rw [InnerProductSpace.Core.inner_smul_ofReal_left]
        simp [mul_comm])
  let c := (LinearMap.toContinuousLinearMap (𝕜 := ℝ)
    (E := TangentSpace (realModel d) x) (F' := ℝ)).toLinearMap.comp b
  exact ⟨LinearMap.toContinuousLinearMap c, fun _ _ ↦ rfl⟩

end StableFoliationsSupport
end HolomorphicAnosov
