import HolomorphicAnosov.Dynamics.SmaleOriginalAnosovTransitiveComponentsSource

namespace HolomorphicAnosov
open Set Filter
open scoped ContDiff _root_.Topology Bundle
universe u

/-- For an Anosov diffeomorphism with cyclic shadowing, the nonwandering set has finitely many
compact invariant transitive components with internal finite shadowing, and each component's
two-sided basin consists of nonwandering points (Shub, Thm. 7.8; Lemmas 7.9–7.10; Thm. 8.13). -/
theorem smale_original_anosov_transitive_components
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
    (∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ (n : ℕ), 0 < n → ∀ q : Fin n → M,
        (∀ i, dist (f (q i)) (q (finRotate n i)) < δ) →
          ∃ j : Fin n → M, Function.Semiconj j (finRotate n) f ∧
            ∀ i, dist (j i) (q i) < ε) →
    let Ω : Set M := {x | ∀ U : Set M, IsOpen U → x ∈ U →
      ∃ k : ℕ, 0 < k ∧ (((f : M → M)^[k]) '' U ∩ U).Nonempty}
    let Ws : Set M → Set M := fun L =>
      {x | Tendsto (fun k : ℕ => Metric.infDist (((f : M → M)^[k]) x) L)
        atTop (𝓝 0)}
    let Wu : Set M → Set M := fun L =>
      {x | Tendsto (fun k : ℕ => Metric.infDist (((f.symm : M → M)^[k]) x) L)
        atTop (𝓝 0)}
    ∃ (b : ℕ) (L : Fin b → Set M), (∀ i, (L i).Nonempty ∧ IsCompact (L i) ∧ f '' L i = L i) ∧
      Pairwise (fun i j => Disjoint (L i) (L j)) ∧
      Ω = ⋃ i, L i ∧
      (∀ i, ∀ U V : Set M, IsOpen U → (U ∩ L i).Nonempty →
        IsOpen V → (V ∩ L i).Nonempty →
        ∃ k : ℕ, ((f : M → M)^[k] '' (U ∩ L i) ∩ V).Nonempty) ∧
      (∀ i, ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
        ∀ (N : ℕ) (q : ℕ → M), (∀ k ≤ N, q k ∈ L i) →
          (∀ k < N, dist (f (q k)) (q (k + 1)) < δ) →
          ∃ a ∈ L i, ∀ k ≤ N, dist ((f : M → M)^[k] a) (q k) < ε) ∧
      (∀ i, Ws (L i) ∩ Wu (L i) ⊆ Ω) := by
  dsimp only
  intro hR hC hlam hlam1 hcompl hEs hEu hs hu hcyclic
  obtain ⟨b, L, hL, hdisjoint, hcover, hrest⟩ :=
    smale_original_anosov_transitive_components_source f Es Eu metric C lam
      hR hC hlam hlam1 hcompl hEs hEu hs hu hcyclic
  rcases hrest with ⟨htransitive, hfinite, hbasins, _⟩
  refine ⟨b, L, hL, hdisjoint, hcover, htransitive, hfinite, ?_⟩
  intro i x hx
  exact hcover ▸ hbasins i hx

end HolomorphicAnosov
