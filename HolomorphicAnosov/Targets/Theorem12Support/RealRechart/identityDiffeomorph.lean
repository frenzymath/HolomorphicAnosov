import HolomorphicAnosov.Geometry.ComplexModel
import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import HolomorphicAnosov.Targets.Theorem12Support.RealRechart.coordinates
import HolomorphicAnosov.Targets.Theorem12Support.RealRechart
import HolomorphicAnosov.Targets.Theorem12Support.RealRechart.Recharted
import HolomorphicAnosov.Targets.Theorem12Support.RealRechart.copiedCharts
import HolomorphicAnosov.Targets.Theorem12Support.RealRechart.copyHomeomorph
import HolomorphicAnosov.Targets.Theorem12Support.RealRechart.identity_smooth_forward
import HolomorphicAnosov.Targets.Theorem12Support.RealRechart.identity_smooth_backward
import HolomorphicAnosov.Targets.Theorem12Support.RealRechart.copied_isManifold

open scoped ContDiff Manifold Topology _root_.Topology
open Set
namespace HolomorphicAnosov.Theorem12SupportW2
noncomputable section
universe u

variable {d n : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel d) X]
  (B : ComplexModel d ≃L[ℝ] EuclideanSpace ℝ (Fin n))

/-- The identity diffeomorphism from `X` with its original real model to `Recharted X` with the
atlas postcomposed by `B`. (Zhang, §3, p. 11) -/

def identityDiffeomorph :
    letI := copiedCharts (X := X) B
    Diffeomorph (realModel d) 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      X (Recharted X) ∞ :=
  letI := copiedCharts (X := X) B
  { toEquiv := (copyHomeomorph (X := X)).toEquiv
    contMDiff_toFun := identity_smooth_forward B
    contMDiff_invFun := identity_smooth_backward B }

end
end HolomorphicAnosov.Theorem12SupportW2
