import HolomorphicAnosov.Geometry.Manifold.CompactVolumeJacobianIntegral.FinitePresentationMass
import HolomorphicAnosov.Geometry.Manifold.CompactVolumeJacobianIntegral.PresentationIntegralFormula
import HolomorphicAnosov.Geometry.Manifold.CompactVolumeJacobianIntegral.PairedChartIntegrals

/-! Coordinate formulas for integrating a smooth volume form and its Jacobian on a finite oriented chart presentation. (Zhang, Lemma 4.3; Demailly, I §1.C.) -/

open scoped Manifold ContDiff ENNReal
open Set MeasureTheory
noncomputable section
namespace HolomorphicAnosov.VolumePrototype

universe u
variable {n : ℕ} {M : Type u} [TopologicalSpace M] [ChartedSpace (CoordinateSpace n) M]
  [IsManifold 𝓘(ℝ, CoordinateSpace n) ∞ M] [CompactSpace M] [T2Space M]
  [MeasurableSpace M] [BorelSpace M]


/-- The integral of the volume-form Jacobian of an orientation-preserving self-diffeomorphism equals the total mass of the presentation measure. -/
lemma presentation_jacobian_integral (o : OrientedAtlas (n := n) (M := M))
    (ν : PositiveVolumeForm o) (p : FiniteVolumePresentation o)
    (F : Diffeomorph 𝓘(ℝ, CoordinateSpace n) 𝓘(ℝ, CoordinateSpace n) M M ∞)
    (hF : PreservesOrientation o F) :
    (∫ x, jacobian ν F x ∂volumePresentationMeasure ν p) =
      (volumePresentationMeasure ν p Set.univ).toReal := by
  classical
  let μ := volumePresentationMeasure ν p
  let : IsFiniteMeasure μ := ⟨finite_presentation_mass o ν p⟩
  have hc : Continuous (jacobian ν F) :=
    ((positiveVolumeForm_coordinateIdentities o ν).2.2.2.2 F hF).1.continuous
  have hsum (x : M) : (∑ i : Fin p.count, p.partition i x) = 1 := by
    simpa only [finsum_eq_sum_of_fintype] using p.partition.sum_eq_one (Set.mem_univ x)
  have hsint (j : Fin p.count) : Integrable (fun x ↦ p.partition j (F x) * jacobian ν F x) μ :=
    integrableOn_univ.mp ((((p.partition j).contMDiff.continuous.comp F.contMDiff.continuous).mul
      hc).continuousOn.integrableOn_compact isCompact_univ)
  have htint (i : Fin p.count) : Integrable (fun x ↦ p.partition i (F.symm x)) μ :=
    integrableOn_univ.mp (((p.partition i).contMDiff.continuous.comp
      F.symm.contMDiff.continuous).continuousOn.integrableOn_compact isCompact_univ)
  calc
    (∫ x, jacobian ν F x ∂μ) =
        ∑ j : Fin p.count, ∫ x, p.partition j (F x) * jacobian ν F x ∂μ := by
      rw [← integral_finsetSum Finset.univ (fun j _ ↦ hsint j)]
      apply integral_congr_ae
      filter_upwards [] with x
      rw [← Finset.sum_mul, hsum, one_mul]
    _ = ∑ j : Fin p.count, ∑ i : Fin p.count, ∫ z in (p.chart i).target,
        p.partition i ((p.chart i).symm z) * p.partition j (F ((p.chart i).symm z)) *
          chartDensity ν.form (p.chart i) z * jacobian ν F ((p.chart i).symm z) := by
      apply Finset.sum_congr rfl
      intro j _
      dsimp only [μ]
      rw [presentation_integral_formula o ν p (fun x ↦ p.partition j (F x) * jacobian ν F x)
        (((p.partition j).contMDiff.continuous.comp F.contMDiff.continuous).mul hc)]
      apply Finset.sum_congr rfl
      intro i _
      apply integral_congr_ae
      filter_upwards [] with z
      ring
    _ = ∑ j : Fin p.count, ∑ i : Fin p.count, ∫ w in (p.chart j).target,
        p.partition i (F.symm ((p.chart j).symm w)) * p.partition j ((p.chart j).symm w) *
          chartDensity ν.form (p.chart j) w := by
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro i _
      exact (paired_chart_integrals o ν p F hF i j).symm
    _ = ∑ i : Fin p.count, ∑ j : Fin p.count, ∫ w in (p.chart j).target,
        p.partition i (F.symm ((p.chart j).symm w)) * p.partition j ((p.chart j).symm w) *
          chartDensity ν.form (p.chart j) w := Finset.sum_comm
    _ = ∑ i : Fin p.count, ∫ x, p.partition i (F.symm x) ∂μ := by
      apply Finset.sum_congr rfl
      intro i _
      dsimp only [μ]
      rw [presentation_integral_formula o ν p (fun x ↦ p.partition i (F.symm x))
        ((p.partition i).contMDiff.continuous.comp F.symm.contMDiff.continuous)]
      apply Finset.sum_congr rfl
      intro j _
      apply integral_congr_ae
      filter_upwards [] with w
      ring
    _ = ∫ x, (1 : ℝ) ∂μ := by
      rw [← integral_finsetSum Finset.univ (fun i _ ↦ htint i)]
      apply integral_congr_ae
      filter_upwards [] with x
      exact hsum (F.symm x)
    _ = (μ Set.univ).toReal := by simp [Measure.real]



end HolomorphicAnosov.VolumePrototype
