import HolomorphicAnosov.Dynamics.SmaleSpectralCore
import HolomorphicAnosov.Dynamics.SmaleTwoSidedBasinPartition
import HolomorphicAnosov.Dynamics.SmaleBasinIntersection

/-! Spectral components and stable and unstable basins of a real Anosov diffeomorphism (Shub, Thm.
8.13; Props. 9.7–9.8). -/

namespace HolomorphicAnosov

open Set Filter
open scoped ContDiff _root_.HolomorphicAnosov.Topology _root_.Topology Bundle

universe u


/-- An Anosov diffeomorphism has finitely many compact invariant locally maximal components with
dense full orbits and dense periodic points, whose stable and unstable basins each partition the
manifold and intersect in the corresponding component. A proper nonwandering set requires at
least two components (Shub, Thm. 8.13; Lemma 2.2; Prop. 9.8). -/
theorem smale_original_anosov_spectral_basins
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
    let Ω : Set M := {x | ∀ U : Set M, IsOpen U → x ∈ U →
      ∃ k : ℕ, 0 < k ∧ (((f : M → M)^[k]) '' U ∩ U).Nonempty}
    let Ws : Set M → Set M := fun L =>
      {x | Tendsto (fun k : ℕ => Metric.infDist (((f : M → M)^[k]) x) L)
        atTop (𝓝 0)}
    let Wu : Set M → Set M := fun L =>
      {x | Tendsto (fun k : ℕ => Metric.infDist (((f.symm : M → M)^[k]) x) L)
        atTop (𝓝 0)}
    closure (Function.periodicPts (f : M → M)) = Ω ∧
    ∃ (b : ℕ) (L : Fin b → Set M), 1 ≤ b ∧
      (∀ i, (L i).Nonempty ∧ IsCompact (L i) ∧ f '' L i = L i) ∧
      Pairwise (fun i j => Disjoint (L i) (L j)) ∧
      Ω = ⋃ i, L i ∧
      (∀ i, ∃ x ∈ L i,
        closure (Set.range (fun k : ℤ => (f.toEquiv ^ k) x)) = L i) ∧
      (∀ i, closure (Function.periodicPts (f : M → M) ∩ L i) = L i) ∧
      (∀ i, ∃ U : Set M, IsOpen U ∧ L i ⊆ U ∧
        L i = ⋂ k : ℤ, (fun x => (f.toEquiv ^ k) x) '' U) ∧
      (∀ i x, x ∈ L i →
        IsCompl (Es.toDistribution x) (Eu.toDistribution x) ∧
        (Es.toDistribution x).map (mfderiv I I f x).toLinearMap =
          Es.toDistribution (f x) ∧
        (Eu.toDistribution x).map (mfderiv I I f x).toLinearMap =
          Eu.toDistribution (f x) ∧
        ∀ k (v : TangentSpace I x),
          (v ∈ Es.toDistribution x →
            ‖mfderiv I I ((f : M → M)^[k]) x v‖ ≤ C * lam ^ k * ‖v‖) ∧
          (v ∈ Eu.toDistribution x →
            ‖mfderiv I I ((f.symm : M → M)^[k]) x v‖ ≤ C * lam ^ k * ‖v‖)) ∧
      Pairwise (fun i j => Disjoint (Ws (L i)) (Ws (L j))) ∧
      (⋃ i, Ws (L i)) = univ ∧
      Pairwise (fun i j => Disjoint (Wu (L i)) (Wu (L j))) ∧
      (⋃ i, Wu (L i)) = univ ∧
      (∀ i, Ws (L i) ∩ Wu (L i) = L i) ∧
      (Ω ≠ univ → 2 ≤ b) := by
  intro I hR hC hlam hlam1 hcompl hEs hEu hs hu Ω Ws Wu
  obtain ⟨hperiodic, b, L, hb, hL, hdisj, hΩ, horbit, hperiodicL, hisolated, hreturn⟩ :=
    smale_original_anosov_spectral_core f Es Eu metric C lam
      hR hC hlam hlam1 hcompl hEs hEu hs hu
  obtain ⟨hsdisj, hscover, hudisj, hucover⟩ :=
    smale_two_sided_basin_partition_of_spectral_components f.toHomeomorph L
      (fun i ↦ (hL i).2.1.isClosed) (fun i ↦ (hL i).1)
      hdisj (fun i ↦ (hL i).2.2) hΩ
  have hinter : ∀ i, Ws (L i) ∩ Wu (L i) = L i :=
    smale_basin_intersection_of_nonwandering f.toHomeomorph L
      (fun i ↦ (hL i).2.1.isClosed) (fun i ↦ (hL i).1)
      hdisj (fun i ↦ (hL i).2.2) hΩ hreturn
  refine ⟨hperiodic, b, L, hb, hL, hdisj, hΩ, horbit, hperiodicL, hisolated,
    ?_, hsdisj, hscover, hudisj, hucover, hinter, ?_⟩
  · intro i x hx
    exact ⟨hcompl x, hEs x, hEu x, fun k v ↦ ⟨hs x k v, hu x k v⟩⟩
  · intro hproper
    by_contra htwo
    have hb1 : b = 1 := by omega
    subst b
    have hindex (i : Fin 1) : L i = L 0 := congrArg L (Subsingleton.elim i 0)
    have hsall : Ws (L 0) = univ := by
      simpa only [Ws, Diffeomorph.coe_toHomeomorph, hindex, iUnion_const] using hscover
    have huall : Wu (L 0) = univ := by
      simpa only [Wu, Diffeomorph.coe_toHomeomorph_symm, hindex, iUnion_const] using hucover
    have hLall : L 0 = univ := by
      rw [← hinter 0, hsall, huall, inter_self]
    apply hproper
    simpa only [hindex, iUnion_const, hLall] using hΩ

end HolomorphicAnosov
