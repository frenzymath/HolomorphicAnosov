import HolomorphicAnosov.Dynamics.SmaleOriginalAnosovCyclicShadowingSource

namespace HolomorphicAnosov
open Set Filter
open scoped ContDiff _root_.HolomorphicAnosov.Topology _root_.Topology Bundle
universe u

/-- An Anosov diffeomorphism has cyclic shadowing in its original metric (Shub, Thm. 7.8; Lemmas
7.9–7.10; Thm. 8.13). -/
theorem smale_original_anosov_cyclic_shadowing
    {n : ℕ} {M : Type u} [MetricSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ∞ M]
    [CompactSpace M] [ConnectedSpace M] [Nonempty M] [SecondCountableTopology M]
    (f : Diffeomorph (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) M M ∞)
    (Es Eu : ContinuousRealTangentSubbundle
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) M)
    (metric : Bundle.ContMDiffRiemannianMetric
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ∞
      (EuclideanSpace ℝ (Fin n))
      (fun x : M => TangentSpace (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) x))
    (C lam : ℝ) :
    let I := modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))
    letI : Bundle.RiemannianBundle (fun x : M => TangentSpace I x) :=
      ⟨metric.toRiemannianMetric⟩
    IsRiemannianManifold I M →
    0 < C → 0 < lam → lam < 1 →
    (∀ x, IsCompl (Es.toDistribution x) (Eu.toDistribution x)) →
    (∀ x, (Es.toDistribution x).map (mfderiv I I f x).toLinearMap =
      Es.toDistribution (f x)) →
    (∀ x, (Eu.toDistribution x).map (mfderiv I I f x).toLinearMap =
      Eu.toDistribution (f x)) →
    (∀ x k (v : TangentSpace I x), v ∈ Es.toDistribution x →
      ‖mfderiv I I ((f : M → M)^[k]) x v‖ ≤ C * lam ^ k * ‖v‖) →
    (∀ x k (v : TangentSpace I x), v ∈ Eu.toDistribution x →
      ‖mfderiv I I ((f.symm : M → M)^[k]) x v‖ ≤ C * lam ^ k * ‖v‖) →
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ (n : ℕ), 0 < n → ∀ q : Fin n → M,
        (∀ i, dist (f (q i)) (q (finRotate n i)) < δ) →
          ∃ j : Fin n → M, Function.Semiconj j (finRotate n) f ∧
            ∀ i, dist (j i) (q i) < ε := by
  dsimp only
  intro hR hC hlam hlam1 hcompl hEs hEu hs hu ε hε
  obtain ⟨δ, hδ, hshadow⟩ :=
    smale_original_anosov_cyclic_shadowing_source f Es Eu metric C lam
      hR hC hlam hlam1 hcompl hEs hEu hs hu (ε / 2) (half_pos hε)
  refine ⟨δ, hδ, ?_⟩
  intro n hn q hq
  obtain ⟨j, hsem, hclose⟩ := hshadow n hn q hq
  refine ⟨j, hsem, ?_⟩
  intro k
  exact (hclose k).trans_lt (by linarith)

end HolomorphicAnosov
