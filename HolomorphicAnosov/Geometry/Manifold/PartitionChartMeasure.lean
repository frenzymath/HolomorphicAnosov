import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Measure.Comap
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-! # A finite chart-presentation measure Demailly, *Complex Analytic and Differential Geometry* (June 21, 2012), Chapter I §1.C, printed p.11, equation (1.16) and the following partition-of-unity paragraph. The finite sum below is the actual weighted chart measure. Its identification with a given intrinsic top form and independence from the partition use the density transition law; those are separate propositions. -/

namespace HolomorphicAnosov.CompactVolumeConstruction

open MeasureTheory Set
open scoped Manifold ENNReal ContDiff

noncomputable section

variable {E M : Type*} [TopologicalSpace E] [TopologicalSpace M]

/-- The inverse of an actual chart, restricted to its target, as a continuous map (Demailly, I §1.C, p.11). -/
def chartInverse (e : OpenPartialHomeomorph M E) : C(e.target, M) :=
  ⟨fun z ↦ e.symm z, continuousOn_iff_continuous_domRestrict.mp e.continuousOn_symm⟩

/-- Demailly's partition-of-unity measure construction, §1.C p.11, (1.16). -/
def partitionChartMeasure
    {m : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin m)) M] [MeasurableSpace M] [BorelSpace M]
    {ι : Type*} [Fintype ι]
    (charts : ι → OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin m)))
    (ρ : ι → EuclideanSpace ℝ (Fin m) → ℝ)
    (χ : SmoothPartitionOfUnity ι (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin m))) M)
    (_hχ : χ.IsSubordinate (fun i ↦ (charts i).source))
    (_hρsmooth : ∀ i, ContDiffOn ℝ ∞ (ρ i) (charts i).target)
    (_hρpositive : ∀ i, ∀ z ∈ (charts i).target, 0 < ρ i z) : Measure M :=
  ∑ i, Measure.map (chartInverse (charts i))
    ((volume.comap (Subtype.val : (charts i).target → EuclideanSpace ℝ (Fin m))).withDensity
      (fun z ↦ ENNReal.ofReal (χ i ((charts i).symm z) * ρ i z)))

end
end HolomorphicAnosov.CompactVolumeConstruction
