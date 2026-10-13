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
import HolomorphicAnosov.Geometry.Manifold.ComplexTorus.TheoremASupport.hasMFDerivAt_real_quotient
import HolomorphicAnosov.Geometry.Manifold.ComplexTorus.TheoremASupport.fixed_point

namespace HolomorphicAnosov.TheoremAProof.FixedPointConjugacy
open scoped ContDiff

variable {d : ℕ} {X : Type*} [TopologicalSpace X] [ChartedSpace (ComplexModel d) X]
  {L : FullComplexLattice d} (A : LatticeLinearEquiv L)
  (f : Biholomorph d d X X) (h : Biholomorph d d X (ComplexTorus L))
  (hc : Function.Semiconj (fun x ↦ h x) (fun x ↦ f x)
    (fun t ↦ quotientLinearEquiv A t))

include hc in

include hc in
theorem tangent_square :
    (mfderiv (realModel d) (realModel d) h.toReal (h.symm 0)).comp
        (mfderiv (realModel d) (realModel d) f.toReal (h.symm 0)) =
      (mfderiv (realModel d) (realModel d) (quotientLinearEquiv A) 0).comp
        (mfderiv (realModel d) (realModel d) h.toReal (h.symm 0)) := by
  have eqcomp : (h.toReal : X → ComplexTorus L) ∘ f.toReal =
      (quotientLinearEquiv A : ComplexTorus L → ComplexTorus L) ∘ h.toReal := funext hc
  have hd := mfderiv_congr (I := realModel d) (I' := realModel d)
    (x := h.symm 0) eqcomp
  have hq : MDifferentiableAt (realModel d) (realModel d) (quotientLinearEquiv A)
      (h.toReal (h.symm 0)) := by
    change MDifferentiableAt (realModel d) (realModel d) (quotientLinearEquiv A)
      (h (h.symm 0))
    rw [h.apply_symm_apply]
    exact (QuotientCalculus.hasMFDerivAt_real_quotient A).mdifferentiableAt
  rw [mfderiv_comp _ ((h.toReal.mdifferentiable (by simp)) _)
      ((f.toReal.mdifferentiable (by simp)) _),
    mfderiv_comp _ hq
      ((h.toReal.mdifferentiable (by simp)) _)] at hd
  rw [fixed_point A f h hc] at hd
  change _ = (mfderiv (realModel d) (realModel d) (quotientLinearEquiv A)
    (h (h.symm 0))).comp _ at hd
  rw [h.apply_symm_apply] at hd
  exact hd


end HolomorphicAnosov.TheoremAProof.FixedPointConjugacy
