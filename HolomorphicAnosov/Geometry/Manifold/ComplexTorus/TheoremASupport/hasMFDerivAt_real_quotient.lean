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
import HolomorphicAnosov.Geometry.Manifold.ComplexTorus.TheoremASupport.hasFDerivAt_real_chart_quotient
import HolomorphicAnosov.Geometry.Manifold.ComplexTorus.TheoremASupport.continuous_quotient_linear

namespace HolomorphicAnosov.TheoremAProof.QuotientCalculus
open Filter _root_.Topology
noncomputable section

/-- The quotient automorphism has real manifold derivative at the origin given by the scalar
restriction of `A.linear`, transported through the tangent-to-model equivalences. -/
theorem hasMFDerivAt_real_quotient {d : ℕ} {L : FullComplexLattice d}
    (A : LatticeLinearEquiv L) :
    HasMFDerivAt (realModel d) (realModel d) (quotientLinearEquiv A) 0
      ((tangentSpaceCastModel (realModel d) (quotientLinearEquiv A 0)).symm.toContinuousLinearMap.comp
        ((A.linear.toContinuousLinearEquiv.toContinuousLinearMap.restrictScalars ℝ).comp
          (tangentSpaceCastModel (realModel d) (0 : ComplexTorus L)).toContinuousLinearMap)) := by
  constructor
  · exact (continuous_quotient_linear A).continuousAt
  · simp only [writtenInExtChartAt, mfld_simps, map_zero]
    have heq :
        ((tangentSpaceCastModel (realModel d) (quotientLinearEquiv A 0)).toContinuousLinearMap.comp
          (((tangentSpaceCastModel (realModel d) (quotientLinearEquiv A 0)).symm.toContinuousLinearMap.comp
            ((A.linear.toContinuousLinearEquiv.toContinuousLinearMap.restrictScalars ℝ).comp
              (tangentSpaceCastModel (realModel d) (0 : ComplexTorus L)).toContinuousLinearMap)).comp
                (tangentSpaceCastModel (realModel d) (0 : ComplexTorus L)).symm.toContinuousLinearMap)) =
        (A.linear.toContinuousLinearEquiv.toContinuousLinearMap.restrictScalars ℝ) := by
      ext v
      simp
    simp only [ContinuousLinearMap.comp_assoc] at heq ⊢
    rw [heq]
    exact (hasFDerivAt_real_chart_quotient A).hasFDerivWithinAt (s := Set.univ)



end
end HolomorphicAnosov.TheoremAProof.QuotientCalculus
