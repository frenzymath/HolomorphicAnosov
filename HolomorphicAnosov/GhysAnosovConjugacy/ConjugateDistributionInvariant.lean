import HolomorphicAnosov.Geometry.BiholomorphToReal
import HolomorphicAnosov.Paper.Zhang.Anosov
import HolomorphicAnosov.GhysAnosovConjugacy.ConjugateIterateDerivative

open scoped ContDiff Manifold
namespace HolomorphicAnosov.GhysAnosovConjugacy
noncomputable section
universe u v
variable {d : ℕ} {X : Type u} {Y : Type v}
  [TopologicalSpace X] [TopologicalSpace Y]
  [ChartedSpace (ComplexModel d) X] [ChartedSpace (ComplexModel d) Y]
  [IsManifold (complexModel d) ∞ X] [IsManifold (complexModel d) ∞ Y]

attribute [local instance] complex_isManifold_real

set_option backward.isDefEq.respectTransparency false in
omit [IsManifold (complexModel d) ∞ X] [IsManifold (complexModel d) ∞ Y] in
/-- The derivative of the conjugacy maps an invariant distribution to the corresponding transported distribution. -/
theorem conjugate_distribution_invariant
    (h : Biholomorph d d X Y) (f : Biholomorph d d X X)
    (P : RealTangentDistribution (realModel d) X)
    (hP : ∀ x, (P x).map (mfderiv (realModel d) (realModel d) f x).toLinearMap = P (f x)) :
    let Q := fun y : Y ↦ (P (h.symm y)).map
      (mfderiv (realModel d) (realModel d) h (h.symm y)).toLinearMap
    ∀ y, (Q y).map (mfderiv (realModel d) (realModel d)
      ((h.symm.trans f).trans h) y).toLinearMap = Q (((h.symm.trans f).trans h) y) := by
  intro Q y
  have hc := conjugate_iterate_derivative h f 1 (h.symm y)
  change (mfderiv (realModel d) (realModel d) ((h.symm.trans f).trans h)
      (h (h.symm y))).comp (mfderiv (realModel d) (realModel d) h (h.symm y)) =
    (mfderiv (realModel d) (realModel d) h (f (h.symm y))).comp
      (mfderiv (realModel d) (realModel d) f (h.symm y)) at hc
  rw [h.apply_symm_apply] at hc
  have hi : h.symm (((h.symm.trans f).trans h) y) = f (h.symm y) := by
    change h.symm (h (f (h.symm y))) = _
    exact h.symm_apply_apply _
  change ((P (h.symm y)).map _).map _ = (P (h.symm _)).map _
  rw [hi, ← Submodule.map_comp]
  have hclin := congrArg ContinuousLinearMap.toLinearMap hc
  change (mfderiv (realModel d) (realModel d) ((h.symm.trans f).trans h) y).toLinearMap.comp
      (mfderiv (realModel d) (realModel d) h (h.symm y)).toLinearMap =
    (mfderiv (realModel d) (realModel d) h (f (h.symm y))).toLinearMap.comp
      (mfderiv (realModel d) (realModel d) f (h.symm y)).toLinearMap at hclin
  rw [hclin, Submodule.map_comp, hP]


end
end HolomorphicAnosov.GhysAnosovConjugacy
