import HolomorphicAnosov.Geometry.BiholomorphToReal
import HolomorphicAnosov.Paper.Zhang.ComplexManifold
import Mathlib.Geometry.Manifold.LocalDiffeomorph

namespace HolomorphicAnosov

universe u

open Set Bundle
open scoped ContDiff Manifold _root_.Topology Bundle
attribute [local instance] complex_isManifold_real

variable {d : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel d) X]

/-- The original inverse derivative cancels the original derivative after the endpoint transport justified by g(g⁻¹x)=x (Ghys Proposition 2.2 and its surface remark pp.589–590).-/
theorem inverse_derivative_comp
    (g : Diffeomorph (realModel d) (realModel d) X X ∞) (x : X) :
    (mfderiv (realModel d) (realModel d) g.symm x).comp
      ((tangentSpaceCast (realModel d) (g (g.symm x)) x).toContinuousLinearMap.comp
        (mfderiv (realModel d) (realModel d) g (g.symm x))) =
      ContinuousLinearMap.id ℝ (TangentSpace (realModel d) (g.symm x)) := by
  have hc := mfderiv_comp (g.symm x)
    (g.symm.contMDiff.mdifferentiableAt (by simp))
    (g.contMDiff.mdifferentiableAt (by simp))
  have hid : (g.symm : X → X) ∘ g = id := by
    funext y
    exact g.symm_apply_apply y
  rw [hid, mfderiv_id] at hc
  change _ = _ at hc
  have heq : mfderiv (realModel d) (realModel d) g.symm (g (g.symm x)) =
      mfderiv (realModel d) (realModel d) g.symm x := by
    rw [g.apply_symm_apply]
  rw [heq] at hc
  exact hc.symm


end HolomorphicAnosov
