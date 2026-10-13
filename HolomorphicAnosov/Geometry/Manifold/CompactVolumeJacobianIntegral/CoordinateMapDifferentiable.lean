import HolomorphicAnosov.Geometry.Manifold.RealVolumeJacobian
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import HolomorphicAnosov.Geometry.Manifold.OrientedRealTopForm
import Mathlib.Geometry.Manifold.ContMDiff.Atlas

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
/-- The coordinate representation `ψ ∘ F ∘ φ⁻¹` is differentiable at every point where it is defined. -/
lemma coordinate_map_differentiable (o : OrientedAtlas (n := n) (M := M))
    (F : Diffeomorph 𝓘(ℝ, CoordinateSpace n) 𝓘(ℝ, CoordinateSpace n) M M ∞)
    (φ ψ : OpenPartialHomeomorph M (CoordinateSpace n))
    (hφ : φ ∈ o.charts) (hψ : ψ ∈ o.charts)
    {z : CoordinateSpace n} (hz : z ∈ φ.target) (hFz : F (φ.symm z) ∈ ψ.source) :
    DifferentiableAt ℝ (fun w ↦ ψ (F (φ.symm w))) z := by
  have hc := (contMDiffAt_of_mem_maximalAtlas (o.compatible ψ hψ) hFz).comp z
    (F.contMDiff.contMDiffAt.comp z
      (contMDiffAt_symm_of_mem_maximalAtlas (o.compatible φ hφ) hz))
  have hd := hc.mdifferentiableAt (by simp)
  exact hd.differentiableAt



end HolomorphicAnosov.VolumePrototype
