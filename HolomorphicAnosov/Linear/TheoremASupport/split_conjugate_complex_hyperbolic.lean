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
import HolomorphicAnosov.Linear.TheoremASupport.split_bounded_orbit_eq_zero

namespace HolomorphicAnosov.TheoremAProof
open Filter _root_.Topology

lemma split_conjugate_complex_hyperbolic
    {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup V] [NormedSpace ℂ V]
    (S U : Submodule ℝ E) (hSU : IsCompl S U)
    (T : E ≃L[ℝ] E) (TS : S ≃L[ℝ] S) (TU : U ≃L[ℝ] U)
    (hS : ∀ s : S, T (s : E) = (TS s : E))
    (hU : ∀ u : U, T (u : E) = (TU u : E))
    (hs : ‖TS.toContinuousLinearMap‖ < 1)
    (hu : ‖TU.symm.toContinuousLinearMap‖ < 1)
    (A : V ≃L[ℂ] V) (e : E ≃L[ℝ] V) (k : ℕ)
    (he : ∀ x, e (T x) = (A.toLinearMap ^ k) (e x)) :
    ∀ μ : ℂ, Module.End.HasEigenvalue A.toLinearMap μ → ‖μ‖ ≠ 1 := by
  intro μ hμ hnorm
  obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
  have hμ0 : μ ≠ 0 := by intro h; simp [h] at hnorm
  have hAi : A.symm v = μ⁻¹ • v := by
    apply A.injective
    have hav : A v = μ • v := hv.apply_eq_smul
    rw [A.apply_symm_apply, map_smul, hav, smul_smul, inv_mul_cancel₀ hμ0, one_smul]
  have hvI : Module.End.HasEigenvector A.symm.toLinearMap μ⁻¹ v :=
    ⟨Module.End.mem_eigenspace_iff.mpr hAi, hv.2⟩
  let w := e.symm v
  have heF : Function.Semiconj e T (fun z => (A.toLinearMap ^ k) z) := he
  have heI : Function.Semiconj e T.symm (fun z => (A.symm.toLinearMap ^ k) z) := by
    intro y
    apply Module.End.iterate_injective A.injective k
    rw [← he, T.apply_symm_apply]
    simp only [Module.End.pow_apply]
    exact ((show Function.LeftInverse (A : V → V) (A.symm : V → V) from A.apply_symm_apply).iterate k (e y)).symm
  have hnormF (n : ℕ) : ‖e ((T : E → E)^[n] w)‖ = ‖v‖ := by
    rw [heF.iterate_right n w]
    have hew : e w = v := e.apply_symm_apply v
    rw [hew]
    change ‖(fun z => (A.toLinearMap ^ k) z)^[n] v‖ = ‖v‖
    rw [← Module.End.pow_apply, ← pow_mul, hv.pow_apply, norm_smul, norm_pow, hnorm]
    simp
  have hnormI (n : ℕ) : ‖e ((T.symm : E → E)^[n] w)‖ = ‖v‖ := by
    rw [heI.iterate_right n w]
    have hew : e w = v := e.apply_symm_apply v
    rw [hew]
    change ‖(fun z => (A.symm.toLinearMap ^ k) z)^[n] v‖ = ‖v‖
    rw [← Module.End.pow_apply, ← pow_mul, hvI.pow_apply, norm_smul, norm_pow, norm_inv, hnorm]
    simp
  have hfwd (n : ℕ) : ‖(T : E → E)^[n] w‖ ≤ ‖e.symm.toContinuousLinearMap‖ * ‖v‖ := by
    calc
      ‖(T : E → E)^[n] w‖ = ‖e.symm (e ((T : E → E)^[n] w))‖ := by rw [e.symm_apply_apply]
      _ ≤ ‖e.symm.toContinuousLinearMap‖ * ‖e ((T : E → E)^[n] w)‖ := e.symm.toContinuousLinearMap.le_opNorm _
      _ = ‖e.symm.toContinuousLinearMap‖ * ‖v‖ := by rw [hnormF]
  have hbwd (n : ℕ) : ‖(T.symm : E → E)^[n] w‖ ≤ ‖e.symm.toContinuousLinearMap‖ * ‖v‖ := by
    calc
      ‖(T.symm : E → E)^[n] w‖ = ‖e.symm (e ((T.symm : E → E)^[n] w))‖ := by rw [e.symm_apply_apply]
      _ ≤ ‖e.symm.toContinuousLinearMap‖ * ‖e ((T.symm : E → E)^[n] w)‖ := e.symm.toContinuousLinearMap.le_opNorm _
      _ = ‖e.symm.toContinuousLinearMap‖ * ‖v‖ := by rw [hnormI]
  have hw : w = 0 := split_bounded_orbit_eq_zero S U hSU T TS TU hS hU hs hu w _ hfwd hbwd
  apply hv.2
  have := congrArg e hw
  simpa [w] using this


end HolomorphicAnosov.TheoremAProof
