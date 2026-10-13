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
import HolomorphicAnosov.Linear.TheoremASupport.contraction_bounded_inverse_eq_zero
import HolomorphicAnosov.Linear.TheoremASupport.projection_semiconj

namespace HolomorphicAnosov.TheoremAProof
open Filter _root_.Topology

lemma split_bounded_orbit_eq_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (S U : Submodule ℝ E) (hSU : IsCompl S U)
    (T : E ≃L[ℝ] E) (TS : S ≃L[ℝ] S) (TU : U ≃L[ℝ] U)
    (hS : ∀ s : S, T (s : E) = (TS s : E))
    (hU : ∀ u : U, T (u : E) = (TU u : E))
    (hs : ‖TS.toContinuousLinearMap‖ < 1)
    (hu : ‖TU.symm.toContinuousLinearMap‖ < 1)
    (x : E) (C : ℝ)
    (hfwd : ∀ n : ℕ, ‖(T : E → E)^[n] x‖ ≤ C)
    (hbwd : ∀ n : ℕ, ‖(T.symm : E → E)^[n] x‖ ≤ C) : x = 0 := by
  let PS : E →L[ℝ] S := (S.projectionOnto U hSU).toContinuousLinearMap
  let PU : E →L[ℝ] U := (U.projectionOnto S hSU.symm).toContinuousLinearMap
  have hPS : Function.Semiconj PS T TS := projection_semiconj S U hSU T TS TU hS hU
  have hPU : Function.Semiconj PU T TU := projection_semiconj U S hSU.symm T TU TS hU hS
  have hPSinv : Function.Semiconj PS T.symm TS.symm := by
    intro y
    apply TS.injective
    rw [← hPS, T.apply_symm_apply, TS.apply_symm_apply]
  have hzS : PS x = 0 := contraction_bounded_inverse_eq_zero TS hs (PS x) (‖PS‖ * C) (by
    intro n
    rw [← hPSinv.iterate_right n x]
    exact (PS.le_opNorm _).trans (mul_le_mul_of_nonneg_left (hbwd n) (norm_nonneg PS)))
  have hzU : PU x = 0 := contraction_bounded_inverse_eq_zero TU.symm hu (PU x) (‖PU‖ * C) (by
    intro n
    simp only [ContinuousLinearEquiv.symm_symm]
    rw [← hPU.iterate_right n x]
    exact (PU.le_opNorm _).trans (mul_le_mul_of_nonneg_left (hfwd n) (norm_nonneg PU)))
  have hdecomp := Submodule.projection_add_projection_eq_self hSU x
  change (PS x : E) + (PU x : E) = x at hdecomp
  simpa [hzS, hzU] using hdecomp.symm


end HolomorphicAnosov.TheoremAProof
