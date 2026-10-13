import HolomorphicAnosov.Geometry.ComplexModel
import HolomorphicAnosov.Geometry.ComplexTangent
import HolomorphicAnosov.Geometry.Manifold.VectorBundle.RealTangentDistribution
import Mathlib.Algebra.Module.Submodule.RestrictScalars
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.Finite

/-! # Complex lines in real tangent distributions Source: Zhang, *Codimension-one holomorphic Anosov diffeomorphisms*, p.2, defines complex codimension one by complex dimension one of the stable or unstable distribution. This module defines the condition for one actual real tangent distribution, using the genuine complex tangent scalar action and the canonical same-chart complex-to-real fibre equivalence. -/

namespace HolomorphicAnosov

universe u

/-- Every fibre of `S` is exactly the underlying real space of a complex line (Zhang, p.2). -/
def HasComplexRankOne {d : ℕ} {X : Type u}
    [TopologicalSpace X] [ChartedSpace (ComplexModel d) X]
    (S : RealTangentDistribution (realModel d) X) : Prop :=
  ∀ x : X, ∃ K : Submodule ℂ (TangentSpace (complexModel d) x),
    Module.finrank ℂ K = 1 ∧
      (K.restrictScalars ℝ).map
        (complexTangentToReal d x).toLinearEquiv.toLinearMap = S x


end HolomorphicAnosov
