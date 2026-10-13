import HolomorphicAnosov.Geometry.ComplexModel
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.Finite

open Set Filter
open scoped ContDiff Manifold

namespace HolomorphicAnosov.SingleBundleHolomorphicBox

/-- At one point, a finite-dimensional complex subspace has a complementary frame of the required dimension. -/
theorem exists_complementary_frame {d r c : ℕ} (hdim : d = r + c)
    (N : (Fin r → ℂ) →L[ℂ] ComplexModel d) (hN : Function.Injective N) :
    ∃ A : (Fin c → ℂ) →L[ℂ] ComplexModel d, Function.Injective A ∧
      IsCompl (LinearMap.range N.toLinearMap) (LinearMap.range A.toLinearMap) := by
  classical
  obtain ⟨T, hT⟩ := (LinearMap.range N.toLinearMap).exists_isCompl
  have hdimT : Module.finrank ℂ T = c := by
    have h := Submodule.finrank_add_eq_of_isCompl hT
    rw [LinearMap.finrank_range_of_inj hN] at h
    have hleft : Module.finrank ℂ (Fin r → ℂ) = r := Module.finrank_fin_fun ℂ
    have hright : Module.finrank ℂ (ComplexModel d) = d := Module.finrank_fin_fun ℂ
    rw [hleft, hright] at h
    omega
  let e : (Fin c → ℂ) ≃L[ℂ] T := ContinuousLinearEquiv.ofFinrankEq (by simp [hdimT])
  let A : (Fin c → ℂ) →L[ℂ] ComplexModel d := T.subtypeL.comp e.toContinuousLinearMap
  have hA : Function.Injective A := Subtype.val_injective.comp e.injective
  have hAr : LinearMap.range A.toLinearMap = T := by
    ext v
    constructor
    · rintro ⟨w, rfl⟩
      exact (e w).property
    · intro hv
      obtain ⟨w, hw⟩ := e.surjective ⟨v, hv⟩
      exact ⟨w, congrArg Subtype.val hw⟩
  exact ⟨A, hA, hAr ▸ hT⟩



end HolomorphicAnosov.SingleBundleHolomorphicBox

