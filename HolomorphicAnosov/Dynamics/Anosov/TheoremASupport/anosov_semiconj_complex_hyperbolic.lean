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
import HolomorphicAnosov.Geometry.Manifold.ComplexTorus.TheoremASupport.fixed_point
import HolomorphicAnosov.Geometry.Manifold.ComplexTorus.TheoremASupport.realLinearEquiv
import HolomorphicAnosov.Geometry.Manifold.ComplexTorus.TheoremASupport.intertwining_apply
import HolomorphicAnosov.Geometry.Manifold.ComplexTorus.TheoremASupport.intertwining
import HolomorphicAnosov.Dynamics.Anosov.TheoremASupport.fixed_anosov_blocks
import HolomorphicAnosov.Linear.TheoremASupport.split_conjugate_complex_hyperbolic

namespace HolomorphicAnosov.TheoremAProof.FixedPointSpectrum
open scoped Bundle ContDiff
attribute [local instance] complex_isManifold_real


/-- Zhang's strict original-metric Anosov blocks rule out a unit-modulus eigenvalue
of the actual lattice automorphism. The fixed point is the original preimage of
the quotient origin. The native real derivative square and its true coordinate
identification give the one-step intertwining. Its k-th power is the actual
Anosov iterate derivative. The metric is retained on that fibre; the coordinate
linear equivalence is merely rebuilt as a continuous equivalence in its finite
-dimensional normed spaces, not asserted to be an isometry. The complementary
contracting blocks then annihilate every bounded two-sided orbit. -/
theorem anosov_semiconj_complex_hyperbolic {d : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (ComplexModel d) X]
    [IsManifold (complexModel d) ∞ X]
    {L : FullComplexLattice d} (A : LatticeLinearEquiv L)
    (f : Biholomorph d d X X) (a : AnosovDatum f)
    (h : Biholomorph d d X (ComplexTorus L))
    (hc : Function.Semiconj (fun x ↦ h x) (fun x ↦ f x)
      (fun t ↦ quotientLinearEquiv A t)) :
    ComplexLinearHyperbolic A.linear.toLinearMap := by
  let : Bundle.RiemannianBundle (fun y : X ↦ TangentSpace (realModel d) y) :=
    ⟨a.metric.toRiemannianMetric⟩
  let x := h.symm (0 : ComplexTorus L)
  have hx : f x = x := FixedPointConjugacy.fixed_point A f h hc
  obtain ⟨T, TS, TU, hSU, hSM, hUM, hS, hU, hs, hu, hT⟩ :=
    fixed_anosov_blocks f a x hx
  let e : TangentSpace (realModel d) x ≃L[ℝ] ComplexModel d :=
    (FixedPointConjugacy.realLinearEquiv h).toLinearEquiv.toContinuousLinearEquiv
  let D : TangentSpace (realModel d) x →L[ℝ] TangentSpace (realModel d) x :=
    mfderiv (realModel d) (realModel d) f.toReal x
  have he1 : Function.Semiconj e D A.linear.toLinearMap := by
    intro v
    exact FixedPointConjugacy.intertwining_apply A f h hc v
  have he : ∀ v, e (T v) = (A.linear.toLinearMap ^ a.k) (e v) := by
    intro v
    have hp := he1.iterate_right a.k v
    have hDp : (D ^ a.k) v = (D : TangentSpace (realModel d) x → TangentSpace (realModel d) x)^[a.k] v :=
      congrFun (FunLike.coe_pow_eq_iterate D a.k) v
    have hAp := Module.End.pow_apply A.linear.toLinearMap a.k (e v)
    rw [← hDp, ← hAp] at hp
    change T.toContinuousLinearMap = D ^ a.k at hT
    rw [← hT] at hp
    exact hp
  exact split_conjugate_complex_hyperbolic _ _ hSU T TS TU
    (fun v ↦ (hS v).symm) (fun v ↦ (hU v).symm) hs hu
    A.linear.toContinuousLinearEquiv e a.k he


end HolomorphicAnosov.TheoremAProof.FixedPointSpectrum
