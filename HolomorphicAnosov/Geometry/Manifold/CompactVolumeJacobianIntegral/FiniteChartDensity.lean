import HolomorphicAnosov.Geometry.Manifold.CanonicalVolumeMeasure
import Mathlib.MeasureTheory.Integral.Lebesgue.Map

/-! Coordinate formulas for integrating a smooth volume form and its Jacobian on a finite oriented chart presentation. (Zhang, Lemma 4.3; Demailly, I §1.C.) -/

open scoped Manifold ContDiff ENNReal
open Set MeasureTheory
noncomputable section
namespace HolomorphicAnosov.VolumePrototype

universe u
variable {n : ℕ} {M : Type u} [TopologicalSpace M] [ChartedSpace (CoordinateSpace n) M]
  [IsManifold 𝓘(ℝ, CoordinateSpace n) ∞ M] [CompactSpace M] [T2Space M]
  [MeasurableSpace M] [BorelSpace M]


omit [T2Space M] [MeasurableSpace M] [BorelSpace M] in
/-- Each weighted chart density in a finite subordinate presentation has finite integral. -/
lemma finite_chart_density (o : OrientedAtlas (n := n) (M := M))
    (ν : PositiveVolumeForm o) (p : FiniteVolumePresentation o) (i : Fin p.count) :
    (∫⁻ z : (p.chart i).target,
      ENNReal.ofReal (p.partition i ((p.chart i).symm z) * chartDensity ν.form (p.chart i) z)
      ∂(volume.comap (Subtype.val : (p.chart i).target → CoordinateSpace n))) < ⊤ := by
  let e := p.chart i
  let χ : M → ℝ := p.partition i
  let ρ := chartDensity ν.form e
  let K := e '' tsupport χ
  have hs : tsupport χ ⊆ e.source := p.subordinate i
  have hK : IsCompact K :=
    (isClosed_tsupport χ).isCompact.image_of_continuousOn (e.continuousOn.mono hs)
  have hKt : K ⊆ e.target := by
    rintro _ ⟨x, hx, rfl⟩
    exact e.map_source (hs hx)
  have hc : ContinuousOn (fun z ↦ χ (e.symm z) * ρ z) K := by
    apply ContinuousOn.mul
    · exact (p.partition i).contMDiff.continuous.continuousOn.comp (e.continuousOn_symm.mono hKt)
        (fun _ _ ↦ Set.mem_univ _)
    · exact (ν.smooth e (o.compatible e (p.oriented i))).continuousOn.mono hKt
  obtain ⟨C, hC⟩ := hK.bddAbove_image hc
  have hbound : ∀ z ∈ e.target,
      ENNReal.ofReal (χ (e.symm z) * ρ z) ≤
        K.indicator (fun _ ↦ ENNReal.ofReal C) z := by
    intro z hz
    by_cases hk : z ∈ K
    · rw [Set.indicator_of_mem hk]
      exact ENNReal.ofReal_le_ofReal (hC ⟨z, hk, rfl⟩)
    · rw [Set.indicator_of_notMem hk]
      have hχ : χ (e.symm z) = 0 := by
        by_contra hn
        apply hk
        exact ⟨e.symm z, subset_tsupport χ hn, e.right_inv hz⟩
      simp [hχ]
  change (∫⁻ z : e.target, ENNReal.ofReal (χ (e.symm z) * ρ z)
    ∂(volume.comap (Subtype.val : e.target → CoordinateSpace n))) < ⊤
  rw [lintegral_subtype_comap (μ := volume) e.open_target.measurableSet
    (fun z ↦ ENNReal.ofReal (χ (e.symm z) * ρ z))]
  apply lt_of_le_of_lt (setLIntegral_mono' e.open_target.measurableSet hbound)
  apply lt_of_le_of_lt (MeasureTheory.setLIntegral_le_lintegral _ _)
  rw [lintegral_indicator hK.measurableSet]
  simp only [lintegral_const, Measure.restrict_apply_univ]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hK.measure_lt_top



end HolomorphicAnosov.VolumePrototype
