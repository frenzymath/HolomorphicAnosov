import HolomorphicAnosov.Geometry.ComplexHolomorphicCompatibility
import HolomorphicAnosov.Geometry.Manifold.OneParameterSmoothGenerator
import HolomorphicAnosov.Geometry.Manifold.VectorActionSpatialDerivativesContinuous
import HolomorphicAnosov.Geometry.Biholomorph
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.Geometry.Manifold.MFDeriv.Tangent
import HolomorphicAnosov.Geometry.BiholomorphToReal
import HolomorphicAnosov.Geometry.ComplexToRealManifold

universe u v
namespace HolomorphicAnosov.Paper.Zhang
open scoped ContDiff Topology _root_.Topology
open Set Filter

/-- A function on an open set is smooth if its derivative is `B ∘ f` for a smooth coefficient map
`B` on an open set containing its image. (Bochner–Montgomery, eq. (27), p. 692) -/
theorem smooth_of_smooth_derivative_coefficients
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {s : Set E} {t : Set F} {f : E → F} {B : F → E →L[ℝ] F}
    (hs : IsOpen s) (_ht : IsOpen t) (hmap : MapsTo f s t)
    (hB : ContDiffOn ℝ ∞ B t)
    (hdf : ∀ x ∈ s, HasFDerivAt f (B (f x)) x) : ContDiffOn ℝ ∞ f s := by
  have hd : DifferentiableOn ℝ f s := fun x hx ↦ (hdf x hx).differentiableAt.differentiableWithinAt
  have hc : ∀ n : ℕ, ContDiffOn ℝ n f s := by
    intro n
    induction n with
    | zero => exact contDiffOn_zero.mpr hd.continuousOn
    | succ n ih =>
      rw [Nat.cast_add, Nat.cast_one]
      apply (contDiffOn_succ_iff_fderiv_of_isOpen hs).mpr
      refine ⟨hd, ?_, ?_⟩
      · intro hn
        simp at hn
      · have hcomp := (hB.of_le (by simp)).comp ih hmap
        exact hcomp.congr (fun x hx ↦ (hdf x hx).fderiv)
  exact contDiffOn_infty.mpr hc


end HolomorphicAnosov.Paper.Zhang
