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
import HolomorphicAnosov.Geometry.Manifold.ComplexTorus.TheoremASupport.chart_quotient_eventually_affine

namespace HolomorphicAnosov.TheoremAProof.QuotientCalculus
open Filter _root_.Topology
noncomputable section

/-- The real derivative of the quotient automorphism's chart expression at the chart representative
of the origin is the scalar restriction of `A.linear`. -/
theorem hasFDerivAt_real_chart_quotient {d : ℕ} {L : FullComplexLattice d}
    (A : LatticeLinearEquiv L) :
    let e := chartAt (ComplexModel d) (0 : ComplexTorus L)
    HasFDerivAt (fun z : ComplexModel d => e (quotientLinearEquiv A (e.symm z)))
      (A.linear.toContinuousLinearEquiv.toContinuousLinearMap.restrictScalars ℝ) (e 0) := by
  let e := chartAt (ComplexModel d) (0 : ComplexTorus L)
  exact ((A.linear.toContinuousLinearEquiv.toContinuousLinearMap.restrictScalars ℝ).hasFDerivAt.add_const
    (e 0 - A.linear (e 0))).congr_of_eventuallyEq (chart_quotient_eventually_affine A)



end
end HolomorphicAnosov.TheoremAProof.QuotientCalculus
