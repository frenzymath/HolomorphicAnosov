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

namespace HolomorphicAnosov.TheoremAProof.FixedPointConjugacy
open scoped ContDiff

variable {d : ℕ} {X : Type*} [TopologicalSpace X] [ChartedSpace (ComplexModel d) X]
  {L : FullComplexLattice d} (A : LatticeLinearEquiv L)
  (f : Biholomorph d d X X) (h : Biholomorph d d X (ComplexTorus L))
  (hc : Function.Semiconj (fun x ↦ h x) (fun x ↦ f x)
    (fun t ↦ quotientLinearEquiv A t))

include hc in

/-- The real differential of `h.toReal` at `h.symm 0`, as a continuous linear equivalence to the
tangent space at the torus origin. -/
noncomputable def tangentEquiv :
    TangentSpace (realModel d) (h.symm 0) ≃L[ℝ]
      TangentSpace (realModel d) (0 : ComplexTorus L) :=
  (h.toReal.toOpenPartialHomeomorph_mdifferentiable (by simp)).mfderiv
    (x := h.symm 0) (by trivial)


end HolomorphicAnosov.TheoremAProof.FixedPointConjugacy
