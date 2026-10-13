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
import HolomorphicAnosov.Geometry.Manifold.ComplexTorus.TheoremASupport.mfderiv_real_quotient
import HolomorphicAnosov.Geometry.Manifold.ComplexTorus.TheoremASupport.tangent_square
import HolomorphicAnosov.Geometry.Manifold.ComplexTorus.TheoremASupport.tangentEquiv
import HolomorphicAnosov.Geometry.Manifold.ComplexTorus.TheoremASupport.realLinearEquiv

namespace HolomorphicAnosov.TheoremAProof.FixedPointConjugacy
open scoped ContDiff

variable {d : ℕ} {X : Type*} [TopologicalSpace X] [ChartedSpace (ComplexModel d) X]
  {L : FullComplexLattice d} (A : LatticeLinearEquiv L)
  (f : Biholomorph d d X X) (h : Biholomorph d d X (ComplexTorus L))
  (hc : Function.Semiconj (fun x ↦ h x) (fun x ↦ f x)
    (fun t ↦ quotientLinearEquiv A t))

include hc in

include hc in
theorem intertwining_apply (v : TangentSpace (realModel d) (h.symm 0)) :
    realLinearEquiv h (mfderiv (realModel d) (realModel d) f.toReal (h.symm 0) v) =
      (A.linear.toContinuousLinearEquiv.toContinuousLinearMap.restrictScalars ℝ)
        (realLinearEquiv h v) := by
  have hv := congrArg (fun k ↦ tangentSpaceCastModel (realModel d)
    (0 : ComplexTorus L) (k v)) (tangent_square A f h hc)
  rw [QuotientCalculus.mfderiv_real_quotient] at hv
  change tangentSpaceCastModel (realModel d) (0 : ComplexTorus L)
      (tangentEquiv h (mfderiv (realModel d) (realModel d) f.toReal (h.symm 0) v)) =
    tangentSpaceCastModel (realModel d) (0 : ComplexTorus L)
      ((tangentSpaceCastModel (realModel d) (quotientLinearEquiv A 0)).symm
        ((A.linear.toContinuousLinearEquiv.toContinuousLinearMap.restrictScalars ℝ)
          (tangentSpaceCastModel (realModel d) (0 : ComplexTorus L) (tangentEquiv h v)))) at hv
  rw [map_zero (quotientLinearEquiv A), ContinuousLinearEquiv.apply_symm_apply] at hv
  exact hv


end HolomorphicAnosov.TheoremAProof.FixedPointConjugacy
