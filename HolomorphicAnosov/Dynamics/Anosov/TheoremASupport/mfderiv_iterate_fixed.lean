import HolomorphicAnosov.Geometry.Manifold.ComplexTorus.Quotient
import HolomorphicAnosov.Paper.Zhang.CodimensionOne
import HolomorphicAnosov.Paper.Zhang.ComplexManifold
import HolomorphicAnosov.Paper.Zhang.Anosov
import HolomorphicAnosov.Geometry.Manifold.VectorBundle.ComplexTangentRankOne
import HolomorphicAnosov.Paper.Zhang.TorusModel
import HolomorphicAnosov.Topology.HomotopyTorusRigidity
import HolomorphicAnosov.Geometry.BiholomorphToReal
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Projection
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Topology.Algebra.Module.Equiv
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import HolomorphicAnosov.Geometry.ComplexModel
import Mathlib.Topology.Algebra.Module.PerfectSpace
import Mathlib.Geometry.Manifold.Riemannian.Basic
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Order.Compact
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.Compactness.Compact

namespace HolomorphicAnosov.TheoremAProof
open scoped ContDiff Bundle
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {X : Type*} [TopologicalSpace X] [ChartedSpace H X]

attribute [local instance] complex_isManifold_real

theorem mfderiv_iterate_fixed (g : Diffeomorph I I X X ∞) (x : X)
    (hx : g x = x) (n : ℕ) :
    (show TangentSpace I x →L[ℝ] TangentSpace I x from
      mfderiv I I ((g : X → X)^[n]) x) =
      (show TangentSpace I x →L[ℝ] TangentSpace I x from mfderiv I I g x) ^ n := by
  induction n with
  | zero => simp only [Function.iterate_zero, mfderiv_id, pow_zero]; rfl
  | succ n ih =>
    rw [Function.iterate_succ, mfderiv_comp x
      ((g.contMDiff.iterate n).mdifferentiableAt (by simp))
      (g.contMDiff.mdifferentiableAt (by simp))]
    erw [hx]
    change (show TangentSpace I x →L[ℝ] TangentSpace I x from
        mfderiv I I ((g : X → X)^[n]) x).comp
      (show TangentSpace I x →L[ℝ] TangentSpace I x from mfderiv I I g x) = _
    erw [ih, pow_succ]
    rfl


end
end HolomorphicAnosov.TheoremAProof
