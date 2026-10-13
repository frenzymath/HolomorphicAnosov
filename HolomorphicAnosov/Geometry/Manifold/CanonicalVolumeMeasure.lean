import HolomorphicAnosov.Geometry.Manifold.SmoothPositiveRealVolumeForm
import HolomorphicAnosov.Geometry.Manifold.FiniteVolumePresentation
import HolomorphicAnosov.Geometry.Manifold.PartitionChartMeasure

/-! Construction of the canonical measure associated with a positive volume form on a compact manifold. -/

open scoped Manifold ContDiff
open Set MeasureTheory
noncomputable section
namespace HolomorphicAnosov.VolumePrototype

universe u
variable {n : ℕ} {M : Type u} [TopologicalSpace M] [ChartedSpace (CoordinateSpace n) M]
  [IsManifold 𝓘(ℝ, CoordinateSpace n) ∞ M]

/-- Finite oriented charts with a subordinate smooth partition covering the manifold. -/
structure FiniteVolumePresentation (o : OrientedAtlas (n := n) (M := M)) where
  count : ℕ
  chart : Fin count → OpenPartialHomeomorph M (CoordinateSpace n)
  oriented : ∀ i, chart i ∈ o.charts
  partition : SmoothPartitionOfUnity (Fin count) 𝓘(ℝ, CoordinateSpace n) M
  subordinate : partition.IsSubordinate (fun i ↦ (chart i).source)

variable [CompactSpace M] [T2Space M]

/-- A chosen finite oriented chart presentation with a subordinate smooth partition. -/
def chosenVolumePresentation (o : OrientedAtlas (n := n) (M := M)) : FiniteVolumePresentation o :=
  let k := Classical.choose (finiteVolumePresentation_exists o)
  let hk := Classical.choose_spec (finiteVolumePresentation_exists o)
  let charts := Classical.choose hk
  let hcharts := Classical.choose_spec hk
  let χ := Classical.choose hcharts.2.2
  { count := k, chart := charts, oriented := hcharts.1,
    partition := χ, subordinate := Classical.choose_spec hcharts.2.2 }

variable [MeasurableSpace M] [BorelSpace M]

/-- The finite-presentation measure attached to an intrinsic positive volume form. (Demailly, I §1.C (1.16).) -/
def volumePresentationMeasure {o : OrientedAtlas (n := n) (M := M)}
    (ν : PositiveVolumeForm o) (p : FiniteVolumePresentation o) : Measure M :=
  CompactVolumeConstruction.partitionChartMeasure p.chart
    (fun i ↦ chartDensity ν.form (p.chart i)) p.partition p.subordinate
    (fun i ↦ ν.smooth _ (o.compatible _ (p.oriented i)))
    (fun i ↦ ν.positive _ (p.oriented i))

/-- The volume-form measure constructed from a finite chart presentation. (Demailly, I §1.C (1.16).) -/
def volumeFormMeasure {o : OrientedAtlas (n := n) (M := M)}
    (ν : PositiveVolumeForm o) : Measure M :=
  volumePresentationMeasure ν (chosenVolumePresentation o)

end HolomorphicAnosov.VolumePrototype
