import Mathlib.Topology.EMetricSpace.BoundedVariation
import Mathlib.Topology.ExtendFrom

open Set Filter
open scoped Topology _root_.Topology

namespace HolomorphicAnosov.Analysis

/-- A continuous curve of bounded variation on a nonempty open real interval extends to the
closed interval with exactly the same variation. This fills the endpoint-completion step in
Tao, 246C Notes 2 (2018), Theorem 20 proof, `literature/Tao-246C-Notes2-2018.txt:267`.
Mathlib's bounded-variation one-sided-limit theorems provide the endpoint values. The canonical
`extendFrom` agrees with the original curve inside and is continuous on the closure. At each
endpoint, Mathlib's continuous endpoint variation identity shows that adjoining that endpoint
does not change variation. Completeness supplies the limits; interior continuity is essential.
The packaging of these Mathlib results is an agent-written proof of the source's omitted step. -/
theorem exists_continuousOn_Icc_eqOn_variation_of_boundedVariationOn
    {E : Type*} [MetricSpace E] [CompleteSpace E] {f : ℝ → E} {a b : ℝ}
    (hab : a < b) (hf : ContinuousOn f (Ioo a b)) (hv : BoundedVariationOn f (Ioo a b)) :
    ∃ g : ℝ → E, ContinuousOn g (Icc a b) ∧ EqOn g f (Ioo a b) ∧
      eVariationOn g (Icc a b) = eVariationOn f (Ioo a b) := by
  let g := extendFrom (Ioo a b) f
  have hlimits : ∀ t ∈ Icc a b, ∃ z, Tendsto f (𝓝[Ioo a b] t) (𝓝 z) := by
    intro t ht
    rcases ht.1.eq_or_lt with hleft | hleft
    · subst t
      simpa only [inter_eq_left.mpr Ioo_subset_Ioi_self] using hv.exists_tendsto_right a
    · rcases ht.2.eq_or_lt with hright | hright
      · subst t
        simpa only [inter_eq_left.mpr Ioo_subset_Iio_self] using hv.exists_tendsto_left b
      · exact ⟨f t, hf t ⟨hleft, hright⟩⟩
  have hg : ContinuousOn g (Icc a b) :=
    continuousOn_extendFrom (by rw [closure_Ioo hab.ne]) hlimits
  have heq : EqOn g f (Ioo a b) := extendFrom_extends hf
  refine ⟨g, hg, heq, ?_⟩
  have hright : eVariationOn g (Ioo a b) = eVariationOn g (Ioc a b) := by
    have hne : (𝓝[Ioi a ∩ Iio b] b).NeBot := by
      simpa only [Ioi_inter_Iio] using right_nhdsWithin_Ioo_neBot hab
    have hc : ContinuousWithinAt g (Ioi a ∩ Iic b) b :=
      (hg _ ⟨hab.le, le_rfl⟩).mono (by rintro t ⟨ht, ht'⟩; exact ⟨ht.le, ht'⟩)
    simpa only [Ioi_inter_Iio, Ioi_inter_Iic] using
      eVariationOn.eVariationOn_inter_Iio_eq_inter_Iic_of_continuousWithinAt hne hc
  have hleft : ContinuousWithinAt g (Ici a) a := by
    have hc := hg _ ⟨le_rfl, hab.le⟩
    simpa only [ContinuousWithinAt, nhdsWithin_Icc_eq_nhdsGE hab] using hc
  rw [← eVariationOn.eVariationOn_Ioc_eq_Icc_of_continuousWithinAt hleft,
    ← hright, eVariationOn.congr heq]


end HolomorphicAnosov.Analysis
