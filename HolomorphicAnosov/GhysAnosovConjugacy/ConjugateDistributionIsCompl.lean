import HolomorphicAnosov.Geometry.BiholomorphToReal
import HolomorphicAnosov.Paper.Zhang.Anosov

open scoped ContDiff Manifold
namespace HolomorphicAnosov.GhysAnosovConjugacy
noncomputable section
universe u v
variable {d : ℕ} {X : Type u} {Y : Type v}
  [TopologicalSpace X] [TopologicalSpace Y]
  [ChartedSpace (ComplexModel d) X] [ChartedSpace (ComplexModel d) Y]
  [IsManifold (complexModel d) ∞ X] [IsManifold (complexModel d) ∞ Y]

attribute [local instance] complex_isManifold_real

omit [IsManifold (complexModel d) ∞ X] [IsManifold (complexModel d) ∞ Y] in
/-- An invertible derivative maps complementary stable and unstable subspaces to complementary subspaces. -/
theorem conjugate_distribution_isCompl
    (h : Biholomorph d d X Y)
    (P Q : RealTangentDistribution (realModel d) X)
    (hPQ : ∀ x, IsCompl (P x) (Q x)) (y : Y) :
    IsCompl ((P (h.symm y)).map
      (mfderiv (realModel d) (realModel d) h (h.symm y)).toLinearMap)
      ((Q (h.symm y)).map
      (mfderiv (realModel d) (realModel d) h (h.symm y)).toLinearMap) := by
  exact Submodule.isCompl_map
    (h.toReal.mfderivToContinuousLinearEquiv (by simp) (h.symm y)).toLinearEquiv
    (hPQ (h.symm y))


end
end HolomorphicAnosov.GhysAnosovConjugacy
