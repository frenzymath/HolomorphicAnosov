import HolomorphicAnosov.Geometry.Manifold.CompactVolumeJacobianIntegral.JacobianWeightCoordinate
import HolomorphicAnosov.Geometry.Manifold.CompactVolumeJacobianIntegral.CoordinateChangeIntegral

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
/-- For arbitrary weights on the source and target, the coordinate change-of-variables formula includes the volume-form Jacobian. -/
lemma weighted_coordinate_change (o : OrientedAtlas (n := n) (M := M))
    (ν : PositiveVolumeForm o)
    (F : Diffeomorph 𝓘(ℝ, CoordinateSpace n) 𝓘(ℝ, CoordinateSpace n) M M ∞)
    (hF : PreservesOrientation o F)
    (φ ψ : OpenPartialHomeomorph M (CoordinateSpace n))
    (hφ : φ ∈ o.charts) (hψ : ψ ∈ o.charts) (α β : M → ℝ) :
    let t := φ.symm.trans (F.toHomeomorph.toOpenPartialHomeomorph.trans ψ)
    (∫ w in t.target,
      α (F.symm (ψ.symm w)) * β (ψ.symm w) * chartDensity ν.form ψ w) =
    ∫ z in t.source,
      α (φ.symm z) * β (F (φ.symm z)) * chartDensity ν.form φ z *
        jacobian ν F (φ.symm z) := by
  dsimp only
  rw [coordinate_change_integral o F φ ψ hφ hψ]
  apply setIntegral_congr_fun
    (φ.symm.trans (F.toHomeomorph.toOpenPartialHomeomorph.trans ψ)).open_source.measurableSet
  intro z hz
  have hz' : z ∈ φ.target ∧ F (φ.symm z) ∈ ψ.source := by
    simpa only [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source,
      Homeomorph.toOpenPartialHomeomorph_source, Set.preimage_inter,
      Set.preimage_univ, Set.inter_univ, Set.mem_inter_iff, Set.mem_preimage,
      Set.mem_univ, true_and, Diffeomorph.coe_toHomeomorph,
      Homeomorph.toOpenPartialHomeomorph_apply] using hz
  dsimp only
  rw [abs_of_pos (hF φ hφ ψ hψ z hz'.1 hz'.2), ψ.left_inv hz'.2,
    F.symm_apply_apply]
  have hweight := jacobian_weight_coordinate o ν F φ ψ hφ hψ hz'.1 hz'.2
  calc
    _ = (α (φ.symm z) * β (F (φ.symm z))) *
        (chartDensity ν.form ψ (ψ (F (φ.symm z))) *
          LinearMap.det (fderiv ℝ (fun w ↦ ψ (F (φ.symm w))) z).toLinearMap) := by ring
    _ = _ := by rw [← hweight]; ring



end HolomorphicAnosov.VolumePrototype
