import HolomorphicAnosov.Geometry.ComplexTangent
import HolomorphicAnosov.Geometry.BiholomorphToReal
import HolomorphicAnosov.Paper.Zhang.ComplexManifold
import HolomorphicAnosov.Paper.Zhang.Anosov
import HolomorphicAnosov.Geometry.Manifold.VectorBundle.ComplexTangentRankOne

namespace HolomorphicAnosov

universe u

open Set Bundle
open scoped ContDiff Manifold _root_.Topology Bundle

attribute [local instance] complex_isManifold_real

/-- Complementarity of complex submodules follows from complementarity after canonical realification. (Demailly, §3.C) -/
theorem isCompl_of_realifications
    {V W : Type*} [AddCommGroup V] [Module ℂ V] [Module ℝ V]
    [IsScalarTower ℝ ℂ V] [AddCommGroup W] [Module ℝ W]
    (e : V ≃ₗ[ℝ] W) (S U : Submodule ℂ V)
    (h : IsCompl ((S.restrictScalars ℝ).map e.toLinearMap)
      ((U.restrictScalars ℝ).map e.toLinearMap)) : IsCompl S U := by
  apply (Submodule.isCompl_restrictScalars_iff ℝ).mp
  have h' := Submodule.isCompl_map e.symm h
  simpa [← Submodule.map_comp] using h'

/-- Canonical realification is injective on complex submodules. (Demailly, §3.C) -/
theorem eq_of_realifications
    {V W : Type*} [AddCommGroup V] [Module ℂ V] [Module ℝ V]
    [IsScalarTower ℝ ℂ V] [AddCommGroup W] [Module ℝ W]
    (e : V ≃ₗ[ℝ] W) (S U : Submodule ℂ V)
    (h : (S.restrictScalars ℝ).map e.toLinearMap =
      (U.restrictScalars ℝ).map e.toLinearMap) : S = U := by
  apply Submodule.restrictScalars_injective ℝ ℂ V
  exact Submodule.map_injective_of_injective e.injective h


/-- Derivative invariance of the realified submodules transfers to the complex submodules. (Zhang, p. 1) -/
theorem complex_map_of_original_map {d : ℕ} {X : Type u}
    [TopologicalSpace X] [ChartedSpace (ComplexModel d) X]
    [IsCompactComplexManifold d X]
    (f : Biholomorph d d X X) (x : X)
    (S : Submodule ℂ (TangentSpace (complexModel d) x))
    (T : Submodule ℂ (TangentSpace (complexModel d) (f x)))
    (P : Submodule ℝ (TangentSpace (realModel d) x))
    (Q : Submodule ℝ (TangentSpace (realModel d) (f x)))
    (hS : (S.restrictScalars ℝ).map (complexTangentToReal d x).toLinearEquiv.toLinearMap = P)
    (hT : (T.restrictScalars ℝ).map
      (complexTangentToReal d (f x)).toLinearEquiv.toLinearMap = Q)
    (hP : P.map (mfderiv (realModel d) (realModel d) f.toReal x).toLinearMap = Q) :
    S.map (mfderiv (complexModel d) (complexModel d) f x).toLinearMap = T := by
  apply eq_of_realifications (complexTangentToReal d (f x)).toLinearEquiv
  rw [Submodule.restrictScalars_map, ← Submodule.map_comp]
  have hd : (complexTangentToReal d (f x)).toLinearEquiv.toLinearMap.comp
      ((mfderiv (complexModel d) (complexModel d) f x).toLinearMap.restrictScalars ℝ) =
      (mfderiv (realModel d) (realModel d) f.toReal x).toLinearMap.comp
        (complexTangentToReal d x).toLinearEquiv.toLinearMap := by
    ext v
    exact (Biholomorph.real_mfderiv_realification f x v).symm
  rw [hd]
  erw [Submodule.map_comp]
  rw [hS]
  exact hP.trans hT.symm



end HolomorphicAnosov
