import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import HolomorphicAnosov.Geometry.PositiveVolumeFormCoordinateIdentities

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
/-- In oriented coordinates, the volume-form density times the Jacobian of `F` equals the target density times the determinant of the coordinate derivative. -/
lemma jacobian_weight_coordinate (o : OrientedAtlas (n := n) (M := M))
    (ν : PositiveVolumeForm o)
    (F : Diffeomorph 𝓘(ℝ, CoordinateSpace n) 𝓘(ℝ, CoordinateSpace n) M M ∞)
    (φ ψ : OpenPartialHomeomorph M (CoordinateSpace n))
    (hφ : φ ∈ o.charts) (hψ : ψ ∈ o.charts)
    {z : CoordinateSpace n} (hz : z ∈ φ.target) (hFz : F (φ.symm z) ∈ ψ.source) :
    chartDensity ν.form φ z * jacobian ν F (φ.symm z) =
      chartDensity ν.form ψ (ψ (F (φ.symm z))) *
        LinearMap.det (fderiv ℝ (fun w ↦ ψ (F (φ.symm w))) z).toLinearMap := by
  have hr := (positiveVolumeForm_coordinateIdentities o ν).2.2.2.1 F φ ψ hφ hψ
    (φ.symm z) (φ.map_target hz) hFz
  rw [φ.right_inv hz] at hr
  rw [hr]
  exact mul_div_cancel₀ _ (ne_of_gt (ν.positive φ hφ z hz))



end HolomorphicAnosov.VolumePrototype
