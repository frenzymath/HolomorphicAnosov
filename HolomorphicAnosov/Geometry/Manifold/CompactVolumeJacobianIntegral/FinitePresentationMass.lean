import HolomorphicAnosov.Geometry.Manifold.CompactVolumeJacobianIntegral.FiniteChartDensity

/-! Coordinate formulas for integrating a smooth volume form and its Jacobian on a finite oriented chart presentation. (Zhang, Lemma 4.3; Demailly, I §1.C.) -/

open scoped Manifold ContDiff ENNReal
open Set MeasureTheory
noncomputable section
namespace HolomorphicAnosov.VolumePrototype

universe u
variable {n : ℕ} {M : Type u} [TopologicalSpace M] [ChartedSpace (CoordinateSpace n) M]
  [IsManifold 𝓘(ℝ, CoordinateSpace n) ∞ M] [CompactSpace M] [T2Space M]
  [MeasurableSpace M] [BorelSpace M]


omit [T2Space M] in
/-- The measure associated with a finite subordinate chart presentation has finite total mass. -/
lemma finite_presentation_mass (o : OrientedAtlas (n := n) (M := M))
    (ν : PositiveVolumeForm o) (p : FiniteVolumePresentation o) :
    volumePresentationMeasure ν p Set.univ < ⊤ := by
  unfold volumePresentationMeasure CompactVolumeConstruction.partitionChartMeasure
  rw [Measure.finsetSum_apply]
  apply ENNReal.sum_lt_top.mpr
  intro i hi
  rw [Measure.map_apply (CompactVolumeConstruction.chartInverse (p.chart i)).continuous.measurable
    MeasurableSet.univ]
  simp only [Set.preimage_univ, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ]
  exact finite_chart_density o ν p i



end HolomorphicAnosov.VolumePrototype
