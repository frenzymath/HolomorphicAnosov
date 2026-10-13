import HolomorphicAnosov.Geometry.Manifold.CompactVolumeJacobianIntegral
import HolomorphicAnosov.Paper.Zhang.StableVectorPublic.JacobianDominatedSquareDecay

namespace HolomorphicAnosov
noncomputable section
open scoped ContDiff
open Filter MeasureTheory VolumePrototype in
open scoped Topology Manifold in
/-- An eventual geometric bound by the Jacobians of orientation-preserving diffeomorphisms implies
eventual square integrability and decay to zero of the squared L² integrals and their square
roots. (Zhang, eq. (31)) -/
theorem zhang_volume_jacobian_dominated_square_decay
    {m : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (CoordinateSpace m) M]
    [IsManifold 𝓘(ℝ, CoordinateSpace m) ∞ M] [CompactSpace M] [T2Space M]
    [MeasurableSpace M] [BorelSpace M]
    (o : OrientedAtlas (n := m) (M := M)) (ν : PositiveVolumeForm o)
    (F : ℕ → Diffeomorph 𝓘(ℝ, CoordinateSpace m) 𝓘(ℝ, CoordinateSpace m) M M ∞)
    (hF : ∀ n, PreservesOrientation o (F n))
    (b : ℕ → M → ℝ) (hb : ∀ n, Continuous (b n))
    (C lam : ℝ) (hlam : 1 < lam)
    (hbound : ∀ᶠ n in atTop, ∀ x,
      (b n x) ^ 2 ≤ (C * ((lam ^ n)⁻¹) ^ 2) * jacobian ν (F n) x) :
    (∀ᶠ n in atTop, Integrable (fun x ↦ (b n x) ^ 2) (volumeFormMeasure ν)) ∧
      Tendsto (fun n ↦ ∫ x, (b n x) ^ 2 ∂volumeFormMeasure ν) atTop (𝓝 0) ∧
      Tendsto (fun n ↦ Real.sqrt (∫ x, (b n x) ^ 2 ∂volumeFormMeasure ν))
        atTop (𝓝 0) := by
  have hmass := fun n ↦ compact_volume_jacobian_integral o ν (F n) (hF n)
  have : IsFiniteMeasure (volumeFormMeasure ν) := ⟨(hmass 0).1⟩
  have hJ : ∀ n, Integrable (jacobian ν (F n)) (volumeFormMeasure ν) := by
    intro n
    have hc : Continuous (jacobian ν (F n)) :=
      ((positiveVolumeForm_coordinateIdentities o ν).2.2.2.2 (F n) (hF n)).1.continuous
    exact integrableOn_univ.mp (hc.continuousOn.integrableOn_compact isCompact_univ)
  have hdecay := zhang_jacobian_dominated_square_decay (volumeFormMeasure ν) b
    (fun n ↦ jacobian ν (F n)) C lam hlam (fun n ↦ (hb n).aestronglyMeasurable)
    hJ (fun n ↦ (hmass n).2)
    (hbound.mono fun n hn ↦ Eventually.of_forall hn)
  refine ⟨hdecay.1, hdecay.2, ?_⟩
  simpa only [Real.sqrt_zero, Function.comp_def] using Real.continuous_sqrt.continuousAt.tendsto.comp hdecay.2

end
end HolomorphicAnosov

