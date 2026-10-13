import HolomorphicAnosov.Topology.ENRRetractionRepresentation
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# A Euclidean neighborhood retraction of the finite torus

Source: Dold, *Fixed point index and fixed point theorem for Euclidean
neighborhood retracts* (1965), definition (2.1), p.3. The representation below
uses the standard product-circle embedding and radial normalization.
DAG node: `topo.franks_torus_enr_g2`.
-/

noncomputable section
namespace HolomorphicAnosov.FranksTorusENR
open FixedPointIndexInterface
set_option backward.isDefEq.respectTransparency false

/-- Radial normalization gives the literal Euclidean neighborhood retraction
of a product of circles. Zero-dimensional products are included.

Source: Dold (1965), definition (2.1), p.3, applied to the standard circle
embedding. Identify each additive circle with the complex unit circle and
identify the finite real vector space of complex coordinates with Euclidean
space. The locus where all coordinates are nonzero is open. Embed the torus
using its unit coordinates, and retract by dividing each coordinate by its
norm before applying the inverse circle homeomorphism. These maps are
continuous, and normalization fixes unit coordinates. For zero coordinates,
all coordinate conditions are vacuous, giving the singleton representation. -/
def torusENR (n : ℕ) : ENRRepresentation (UnitAddTorus (Fin n)) := by
  let d := Module.finrank ℝ (Fin n → ℂ)
  let e : (Fin n → ℂ) ≃L[ℝ] Euclidean d :=
    ContinuousLinearEquiv.ofFinrankEq (by simp [d, Euclidean])
  let c := AddCircle.homeomorphCircle (show (1 : ℝ) ≠ 0 by norm_num)
  let U : Set (Euclidean d) := {v | ∀ i, e.symm v i ≠ 0}
  have hU : IsOpen U := by
    change IsOpen {v | ∀ i, e.symm v i ≠ 0}
    simp only [Set.ofPred_forall]
    exact isOpen_iInter_of_finite fun i ↦
      isOpen_compl_singleton.preimage ((continuous_apply i).comp e.symm.continuous)
  let s : C(UnitAddTorus (Fin n), U) :=
    ⟨fun x ↦ ⟨e (fun i ↦ (c (x i) : ℂ)), by
      intro i
      simp only [ContinuousLinearEquiv.symm_apply_apply]
      exact Circle.coe_ne_zero _⟩,
      (e.continuous.comp (continuous_pi fun i ↦
        continuous_subtype_val.comp (c.continuous.comp (continuous_apply i)))).subtype_mk
        (by intro x i; simpa only [Function.comp_apply, ContinuousLinearEquiv.symm_apply_apply]
            using Circle.coe_ne_zero (c (x i)))⟩
  let r : C(U, UnitAddTorus (Fin n)) :=
    ⟨fun v i ↦ c.symm ⟨‖e.symm v.val i‖⁻¹ • e.symm v.val i, by
      apply mem_sphere_zero_iff_norm.mpr
      rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_norm, inv_mul_cancel₀]
      exact norm_ne_zero_iff.mpr (v.property i)⟩, by
      apply continuous_pi
      intro i
      apply c.symm.continuous.comp
      apply Continuous.subtype_mk
      have hv : Continuous (fun v : U ↦ e.symm v.val i) :=
        (continuous_apply i).comp (e.symm.continuous.comp continuous_subtype_val)
      exact (hv.norm.inv₀ (fun v ↦ norm_ne_zero_iff.mpr (v.property i))).smul hv⟩
  refine ⟨d, U, hU, s, r, ?_⟩
  intro x
  funext i
  change c.symm ⟨_, _⟩ = x i
  refine (congrArg c.symm ?_).trans (c.symm_apply_apply (x i))
  apply Circle.ext
  simp [s]

end HolomorphicAnosov.FranksTorusENR
