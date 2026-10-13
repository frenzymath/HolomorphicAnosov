import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Logic.Function.Conjugate
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Tactic.Linarith

/-! Uniform comparison of compatible metrics on compact spaces and transfer of cyclic shadowing
(Shub, Thm. 7.8; Petersen, Thm. 5.3.8). -/
namespace HolomorphicAnosov

/-- A sufficiently small closed distance bound in a second compatible metric on a compact space
implies any prescribed closed bound in the original metric. -/
theorem compact_compatible_metric_displacement
    {M : Type*} [d : MetricSpace M] [CompactSpace M]
    (dA : MetricSpace M)
    (hTop : dA.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace =
      d.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ ∀ x y : M, dA.dist x y ≤ η → d.dist x y ≤ ε := by
  have hcompact : @CompactSpace M
      dA.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace := by
    rw [hTop]
    infer_instance
  have hc : @Continuous M M
      dA.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
      d.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace id := by
    rw [hTop]
    exact @continuous_id M d.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
  have hu := @CompactSpace.uniformContinuous_of_continuous M M
    dA.toPseudoMetricSpace.toUniformSpace d.toPseudoMetricSpace.toUniformSpace hcompact id hc
  obtain ⟨η, hη, hb⟩ := (@Metric.uniformContinuous_iff_le M M
    dA.toPseudoMetricSpace d.toPseudoMetricSpace id).mp hu ε hε
  exact ⟨η, hη, fun x y hxy ↦ hb hxy⟩

/-- A sufficiently small closed distance bound in a second compatible metric on a compact space
implies any prescribed strict bound in the original metric. -/
theorem compact_compatible_metric_displacement_strict
    {M : Type*} [d : MetricSpace M] [CompactSpace M]
    (dA : MetricSpace M)
    (hTop : dA.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace =
      d.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ ∀ x y : M, dA.dist x y ≤ η → d.dist x y < ε := by
  obtain ⟨η, hη, hb⟩ := @compact_compatible_metric_displacement M d inferInstance
    dA hTop (ε / 2) (half_pos hε)
  exact ⟨η, hη, fun x y hxy ↦ (hb x y hxy).trans_lt (half_lt_self hε)⟩

/-- A sufficiently small strict distance bound in the original metric implies any prescribed strict
bound in a second compatible metric on a compact space. -/
theorem compact_compatible_metric_error
    {M : Type*} [d : MetricSpace M] [CompactSpace M]
    (dA : MetricSpace M)
    (hTop : dA.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace =
      d.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace)
    (η : ℝ) (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x y : M, d.dist x y < δ → dA.dist x y < η := by
  have hc : @Continuous M M
      d.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
      dA.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace id := by
    rw [hTop]
    exact @continuous_id M d.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
  have hu := @CompactSpace.uniformContinuous_of_continuous M M
    d.toPseudoMetricSpace.toUniformSpace dA.toPseudoMetricSpace.toUniformSpace
    inferInstance id hc
  obtain ⟨δ, hδ, hb⟩ := (@Metric.uniformContinuous_iff M M
    d.toPseudoMetricSpace dA.toPseudoMetricSpace id).mp hu η hη
  exact ⟨δ, hδ, fun x y hxy ↦ hb hxy⟩

/-- Cyclic shadowing with arbitrary prescribed accuracy transfers between compatible metrics on a
compact space. -/
theorem compact_compatible_metric_cyclic_shadowing
    {M : Type*} [d : MetricSpace M] [CompactSpace M]
    (dA : MetricSpace M)
    (hTop : dA.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace =
      d.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace)
    (f : M → M)
    (hshadow : ∀ η : ℝ, 0 < η → ∃ δA : ℝ, 0 < δA ∧
      ∀ (n : ℕ), 0 < n → ∀ q : Fin n → M,
        (∀ i, dA.dist (f (q i)) (q (finRotate n i)) < δA) →
          ∃ j : Fin n → M, Function.Semiconj j (finRotate n) f ∧
            ∀ i, dA.dist (j i) (q i) ≤ η) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ (n : ℕ), 0 < n → ∀ q : Fin n → M,
        (∀ i, d.dist (f (q i)) (q (finRotate n i)) < δ) →
          ∃ j : Fin n → M, Function.Semiconj j (finRotate n) f ∧
            ∀ i, d.dist (j i) (q i) ≤ ε := by
  intro ε hε
  obtain ⟨η, hη, hout⟩ := @compact_compatible_metric_displacement_strict M d inferInstance dA hTop ε hε
  obtain ⟨δA, hδA, hA⟩ := hshadow η hη
  obtain ⟨δ, hδ, hin⟩ := @compact_compatible_metric_error M d inferInstance dA hTop δA hδA
  refine ⟨δ, hδ, ?_⟩
  intro n hn q hq
  obtain ⟨j, hj, hclose⟩ := hA n hn q (fun i ↦ hin _ _ (hq i))
  exact ⟨j, hj, fun i ↦ (hout _ _ (hclose i)).le⟩

end HolomorphicAnosov
