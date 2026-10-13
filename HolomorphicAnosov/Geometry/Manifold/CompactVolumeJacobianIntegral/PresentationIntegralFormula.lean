import HolomorphicAnosov.Geometry.Manifold.CompactVolumeJacobianIntegral.FiniteChartDensity
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! Coordinate formulas for integrating a smooth volume form and its Jacobian on a finite oriented chart presentation. (Zhang, Lemma 4.3; Demailly, I §1.C.) -/

open scoped Manifold ContDiff ENNReal
open Set MeasureTheory
noncomputable section
namespace HolomorphicAnosov.VolumePrototype

universe u
variable {n : ℕ} {M : Type u} [TopologicalSpace M] [ChartedSpace (CoordinateSpace n) M]
  [IsManifold 𝓘(ℝ, CoordinateSpace n) ∞ M] [CompactSpace M] [T2Space M]
  [MeasurableSpace M] [BorelSpace M]


/-- The integral of a continuous function against the presentation measure is the finite sum of its weighted coordinate integrals. -/
lemma presentation_integral_formula (o : OrientedAtlas (n := n) (M := M))
    (ν : PositiveVolumeForm o) (p : FiniteVolumePresentation o) (h : M → ℝ)
    (hh : Continuous h) :
    (∫ x, h x ∂volumePresentationMeasure ν p) =
      ∑ i : Fin p.count, ∫ z in (p.chart i).target,
        (p.partition i ((p.chart i).symm z) * chartDensity ν.form (p.chart i) z) *
          h ((p.chart i).symm z) := by
  let μ := fun i : Fin p.count ↦ Measure.map (CompactVolumeConstruction.chartInverse (p.chart i))
    ((volume.comap (Subtype.val : (p.chart i).target → CoordinateSpace n)).withDensity
      (fun z ↦ ENNReal.ofReal (p.partition i ((p.chart i).symm z) *
        chartDensity ν.form (p.chart i) z)))
  have hfinite : ∀ i, μ i Set.univ < ⊤ := by
    intro i
    dsimp [μ]
    rw [Measure.map_apply (CompactVolumeConstruction.chartInverse (p.chart i)).continuous.measurable
      MeasurableSet.univ]
    simpa only [Set.preimage_univ, withDensity_apply _ MeasurableSet.univ,
      Measure.restrict_univ] using finite_chart_density o ν p i
  let : ∀ i, IsFiniteMeasure (μ i) := fun i ↦ ⟨hfinite i⟩
  change (∫ x, h x ∂(∑ i, μ i)) = _
  rw [integral_finsetSum_measure (fun i _ ↦
    integrableOn_univ.mp (hh.continuousOn.integrableOn_compact isCompact_univ))]
  apply Finset.sum_congr rfl
  intro i _
  dsimp [μ]
  rw [integral_map
    (CompactVolumeConstruction.chartInverse (p.chart i)).continuous.measurable.aemeasurable
    hh.aestronglyMeasurable]
  have hw : Continuous (fun z : (p.chart i).target ↦
      p.partition i ((p.chart i).symm z) * chartDensity ν.form (p.chart i) z) := by
    exact ((p.partition i).contMDiff.continuous.comp
      (CompactVolumeConstruction.chartInverse (p.chart i)).continuous).mul
      (continuousOn_iff_continuous_domRestrict.mp
        (ν.smooth _ (o.compatible _ (p.oriented i))).continuousOn)
  rw [integral_withDensity_eq_integral_toReal_smul hw.measurable.ennreal_ofReal
    (Filter.Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top)]
  calc
    _ = ∫ z : (p.chart i).target,
        (p.partition i ((p.chart i).symm z) * chartDensity ν.form (p.chart i) z) *
          h ((p.chart i).symm z)
          ∂(volume.comap (Subtype.val : (p.chart i).target → CoordinateSpace n)) := by
      apply integral_congr_ae
      filter_upwards [] with z
      have hpos : 0 ≤ p.partition i ((p.chart i).symm z) *
          chartDensity ν.form (p.chart i) z :=
        mul_nonneg (p.partition.toPartitionOfUnity.nonneg i _)
          (le_of_lt (ν.positive _ (p.oriented i) _ z.property))
      simp only [ENNReal.toReal_ofReal hpos, smul_eq_mul,
        CompactVolumeConstruction.chartInverse]
      rfl
    _ = _ := integral_subtype_comap (μ := volume) (p.chart i).open_target.measurableSet
      (fun z ↦ (p.partition i ((p.chart i).symm z) * chartDensity ν.form (p.chart i) z) *
        h ((p.chart i).symm z))



end HolomorphicAnosov.VolumePrototype
