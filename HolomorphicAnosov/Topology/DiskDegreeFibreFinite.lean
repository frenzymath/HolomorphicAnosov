import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.LinearAlgebra.Determinant
import Mathlib.Topology.IsLocalHomeomorph

noncomputable section
open Set Metric
namespace HolomorphicAnosov.Topology

/-- A positive-determinant C¹ plane map has finite fibres in a closed disk avoiding the boundary.

Source: the finite-fibre input to Hatcher, *Algebraic Topology*, §2.2,
Proposition 2.30, p.136. This proof supplies the compactness argument omitted in
that input: the fibre is closed in the compact disk. At a fibre point, the nonzero
determinant gives an invertible derivative; the C¹ inverse-function theorem gives
a neighborhood on which the map is injective. The fibre therefore is discrete,
and compactness makes it finite. This includes empty fibres and nonpositive radii. -/
theorem disk_degree_fibre_finite
    (c : EuclideanSpace ℝ (Fin 2)) (r : ℝ)
    (O : Set (EuclideanSpace ℝ (Fin 2))) (hO : IsOpen O) (hBO : closedBall c r ⊆ O)
    (g : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)) (hg : ContDiffOn ℝ 1 g O)
    (hdet : ∀ z ∈ O, 0 < LinearMap.det (fderiv ℝ g z).toLinearMap)
    (w : EuclideanSpace ℝ (Fin 2))
    (_hboundary : ∀ z ∈ sphere c r, g z ≠ w) :
    {z : EuclideanSpace ℝ (Fin 2) | z ∈ closedBall c r ∧ g z = w}.Finite := by
  let S : Set (EuclideanSpace ℝ (Fin 2)) := {z | z ∈ closedBall c r ∧ g z = w}
  have hclosed : IsClosed S :=
    (hg.continuousOn.mono hBO).preimage_isClosed_of_isClosed
      isClosed_closedBall isClosed_singleton
  have hcompact : IsCompact S :=
    (isCompact_closedBall c r).of_isClosed_subset hclosed (fun _ hz ↦ hz.1)
  have hdiscrete : IsDiscrete S := by
    have hlocal : IsLocalHomeomorphOn g S := by
      apply IsLocalHomeomorphOn.mk g S
      intro z hz
      have hzO := hBO hz.1
      have hgz : ContDiffAt ℝ 1 g z := hg.contDiffAt (hO.mem_nhds hzO)
      let A : EuclideanSpace ℝ (Fin 2) ≃L[ℝ] EuclideanSpace ℝ (Fin 2) :=
        ((fderiv ℝ g z).toLinearMap.equivOfIsUnitDet
          (isUnit_iff_ne_zero.mpr (ne_of_gt (hdet z hzO)))).toContinuousLinearEquiv
      have hA : (A : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2)) =
          fderiv ℝ g z := by
        ext v
        simp [A]
      have hderiv : HasFDerivAt g (A : EuclideanSpace ℝ (Fin 2) →L[ℝ]
          EuclideanSpace ℝ (Fin 2)) z := by
        rw [hA]
        exact (hgz.differentiableAt one_ne_zero).hasFDerivAt
      let e := hgz.toOpenPartialHomeomorph g hderiv one_ne_zero
      exact ⟨e, hgz.mem_toOpenPartialHomeomorph_source hderiv one_ne_zero,
        fun _ _ ↦ rfl⟩
    have himage : g '' S ⊆ ({w} : Set (EuclideanSpace ℝ (Fin 2))) := by
      rintro y ⟨x, hx, rfl⟩
      exact Set.mem_singleton_iff.mpr hx.2
    exact hlocal.isDiscrete_of_image ((Set.subsingleton_singleton.isDiscrete).mono himage)
  exact hcompact.finite hdiscrete


end HolomorphicAnosov.Topology
