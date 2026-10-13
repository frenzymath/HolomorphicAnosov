import HolomorphicAnosov.Geometry.Manifold.CompactVolumeJacobianIntegral.WeightedCoordinateChange
import HolomorphicAnosov.Geometry.Manifold.CanonicalVolumeMeasure

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
/-- For each pair of presentation charts, the weighted target integral equals the corresponding source integral with the volume-form Jacobian. -/
lemma paired_chart_integrals (o : OrientedAtlas (n := n) (M := M))
    (ν : PositiveVolumeForm o) (p : FiniteVolumePresentation o)
    (F : Diffeomorph 𝓘(ℝ, CoordinateSpace n) 𝓘(ℝ, CoordinateSpace n) M M ∞)
    (hF : PreservesOrientation o F) (i j : Fin p.count) :
    (∫ w in (p.chart j).target,
      p.partition i (F.symm ((p.chart j).symm w)) * p.partition j ((p.chart j).symm w) *
        chartDensity ν.form (p.chart j) w) =
    ∫ z in (p.chart i).target,
      p.partition i ((p.chart i).symm z) * p.partition j (F ((p.chart i).symm z)) *
        chartDensity ν.form (p.chart i) z * jacobian ν F ((p.chart i).symm z) := by
  let φ := p.chart i
  let ψ := p.chart j
  let t := φ.symm.trans (F.toHomeomorph.toOpenPartialHomeomorph.trans ψ)
  have hsource : t.source = φ.target ∩ (fun z ↦ F (φ.symm z)) ⁻¹' ψ.source := by
    simp only [t, OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source,
      Homeomorph.toOpenPartialHomeomorph_source, Set.univ_inter, Diffeomorph.coe_toHomeomorph,
      Homeomorph.toOpenPartialHomeomorph_apply]
    rfl
  have htarget : t.target = ψ.target ∩ (fun w ↦ F.symm (ψ.symm w)) ⁻¹' φ.source := by
    simp only [t, OpenPartialHomeomorph.trans_target, OpenPartialHomeomorph.symm_target,
      Homeomorph.toOpenPartialHomeomorph_target, Set.preimage_univ, Set.inter_univ,
      OpenPartialHomeomorph.coe_trans_symm]
    rfl
  have ht : ∫ w in ψ.target,
      p.partition i (F.symm (ψ.symm w)) * p.partition j (ψ.symm w) * chartDensity ν.form ψ w =
      ∫ w in t.target,
      p.partition i (F.symm (ψ.symm w)) * p.partition j (ψ.symm w) * chartDensity ν.form ψ w := by
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero ψ.open_target.measurableSet
    · rw [htarget]; exact Set.inter_subset_left
    · intro w hw
      have hn : F.symm (ψ.symm w) ∉ φ.source := by
        intro h
        exact hw.2 (htarget.symm ▸ ⟨hw.1, h⟩)
      have hz : p.partition i (F.symm (ψ.symm w)) = 0 := by
        by_contra h
        exact hn (p.subordinate i (subset_tsupport (p.partition i) h))
      simp [hz]
  have hs : (∫ z in φ.target,
      p.partition i (φ.symm z) * p.partition j (F (φ.symm z)) *
        chartDensity ν.form φ z * jacobian ν F (φ.symm z)) =
      ∫ z in t.source,
      p.partition i (φ.symm z) * p.partition j (F (φ.symm z)) *
        chartDensity ν.form φ z * jacobian ν F (φ.symm z) := by
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero φ.open_target.measurableSet
    · rw [hsource]; exact Set.inter_subset_left
    · intro z hz
      have hn : F (φ.symm z) ∉ ψ.source := by
        intro h
        exact hz.2 (hsource.symm ▸ ⟨hz.1, h⟩)
      have hzero : p.partition j (F (φ.symm z)) = 0 := by
        by_contra h
        exact hn (p.subordinate j (subset_tsupport (p.partition j) h))
      simp [hzero]
  exact ht.trans ((weighted_coordinate_change o ν F hF φ ψ (p.oriented i) (p.oriented j)
    (p.partition i) (p.partition j)).trans hs.symm)



end HolomorphicAnosov.VolumePrototype
