import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import HolomorphicAnosov.Geometry.Manifold.CompactVolumeJacobianIntegral.CoordinateMapDifferentiable
import Mathlib.MeasureTheory.Function.Jacobian

/-! Coordinate formulas for integrating a smooth volume form and its Jacobian on a finite oriented chart presentation. (Zhang, Lemma 4.3; Demailly, I §1.C.) -/

open scoped Manifold ContDiff ENNReal
open Set MeasureTheory
noncomputable section
namespace HolomorphicAnosov.VolumePrototype

universe u
variable {n : ℕ} {M : Type u} [TopologicalSpace M] [ChartedSpace (CoordinateSpace n) M]
  [IsManifold 𝓘(ℝ, CoordinateSpace n) ∞ M] [CompactSpace M] [T2Space M]
  [MeasurableSpace M] [BorelSpace M]


omit [CompactSpace M] [T2Space M] [MeasurableSpace M] [BorelSpace M] in
/-- For the coordinate map `ψ ∘ F ∘ φ⁻¹`, the integral over its target equals the integral over its source weighted by the absolute Jacobian determinant. -/
lemma coordinate_change_integral (o : OrientedAtlas (n := n) (M := M))
    (F : Diffeomorph 𝓘(ℝ, CoordinateSpace n) 𝓘(ℝ, CoordinateSpace n) M M ∞)
    (φ ψ : OpenPartialHomeomorph M (CoordinateSpace n))
    (hφ : φ ∈ o.charts) (hψ : ψ ∈ o.charts) (g : CoordinateSpace n → ℝ) :
    let t := φ.symm.trans (F.toHomeomorph.toOpenPartialHomeomorph.trans ψ)
    (∫ w in t.target, g w) =
      ∫ z in t.source,
        |LinearMap.det (fderiv ℝ (fun z ↦ ψ (F (φ.symm z))) z).toLinearMap| *
          g (ψ (F (φ.symm z))) := by
  dsimp only
  apply integral_target_eq_integral_abs_det_fderiv_smul volume
    (f' := fun z ↦ fderiv ℝ (fun z ↦ ψ (F (φ.symm z))) z)
  intro z hz
  have hz' : z ∈ φ.target ∧ F (φ.symm z) ∈ ψ.source := by
    simpa only [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source,
      Homeomorph.toOpenPartialHomeomorph_source, Set.preimage_inter,
      Set.preimage_univ, Set.inter_univ, Set.mem_inter_iff, Set.mem_preimage,
      Set.mem_univ, true_and, Diffeomorph.coe_toHomeomorph,
      Homeomorph.toOpenPartialHomeomorph_apply] using hz
  exact (coordinate_map_differentiable o F φ ψ hφ hψ hz'.1 hz'.2).hasFDerivAt



end HolomorphicAnosov.VolumePrototype
