import HolomorphicAnosov.Geometry.Biholomorph
import HolomorphicAnosov.Geometry.Manifold.ComplexTorus.LatticeLinearEquiv
import HolomorphicAnosov.Geometry.Manifold.ComplexTorus.Quotient
import Mathlib.Algebra.Group.Units.Equiv
import HolomorphicAnosov.Geometry.Manifold.ComplexTorus.Charts
import HolomorphicAnosov.Geometry.Manifold.ComplexTorus.LinearMap
import HolomorphicAnosov.Paper.Zhang.Anosov
import Mathlib.LinearAlgebra.Eigenspace.Basic
import HolomorphicAnosov.Paper.Zhang.FixedBlockUniformAnosovEstimates
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Complex.Basic
import HolomorphicAnosov.Paper.Ghys.QuotientAffineEquiv
import HolomorphicAnosov.Paper.Ghys.QuotientProjectionSmooth
import HolomorphicAnosov.Paper.Ghys.QuotientProjectionDerivative

namespace HolomorphicAnosov

open scoped ContDiff Topology _root_.Topology Manifold Bundle
open IsManifold
attribute [local instance] complexTorus_isManifold complex_isManifold_real
set_option backward.isDefEq.respectTransparency false

theorem affine_derivative {d : ℕ} {L : FullComplexLattice d}
    (A : LatticeLinearEquiv L) (b : ComplexModel d)
    (f : Biholomorph d d (ComplexTorus L) (ComplexTorus L))
    (hf : ∀ x, f x = quotientAffineEquiv A b x) (x : ComplexTorus L) :
    mfderiv (realModel d) (realModel d) f x =
      A.linear.toContinuousLinearEquiv.toContinuousLinearMap.restrictScalars ℝ := by
  obtain ⟨z, rfl⟩ := (torus_quotient_covering L).surjective x
  let q := (QuotientAddGroup.mk : ComplexModel d → ComplexTorus L)
  let α : ComplexModel d → ComplexModel d := fun z ↦ A.linear z + b
  have hα : ContDiff ℂ ∞ α :=
    A.linear.toContinuousLinearEquiv.contDiff.add contDiff_const
  have hαR : ContDiff ℝ ∞ α := hα.restrict_scalars ℝ
  have hqR : ContMDiff (realModel d) (realModel d) ∞ q :=
    contMDiff_complex_to_real (quotient_projection_smooth L)
  have heq : (f ∘ q) = q ∘ α := by
    funext w
    rw [Function.comp_apply, hf]
    rfl
  have hd : mfderiv (realModel d) (realModel d) (f ∘ q) z =
      mfderiv (realModel d) (realModel d) (q ∘ α) z := by rw [heq]
  erw [mfderiv_comp z (f.toReal.contMDiff.mdifferentiableAt (by simp))
      (hqR.mdifferentiableAt (by simp)),
    mfderiv_comp z (hqR.mdifferentiableAt (by simp))
      (hαR.contMDiff.mdifferentiableAt (by simp))] at hd
  erw [quotient_projection_derivative L z, quotient_projection_derivative L (α z),
    ContinuousLinearMap.comp_id, ContinuousLinearMap.id_comp] at hd
  erw [hd, mfderiv_eq_fderiv]
  exact (((A.linear.toContinuousLinearEquiv.toContinuousLinearMap.hasFDerivAt
    (x := z)).restrictScalars ℝ).add_const b).fderiv

end HolomorphicAnosov
