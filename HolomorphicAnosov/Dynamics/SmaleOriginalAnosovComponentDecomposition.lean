import HolomorphicAnosov.Dynamics.SmaleChains
import HolomorphicAnosov.Dynamics.SmaleFiniteInternalShadowing
import HolomorphicAnosov.Dynamics.SmaleCyclicShadowing
import HolomorphicAnosov.Dynamics.SmalePeriodicShadowingClosure
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.CompatibleMetricModulus
import HolomorphicAnosov.Dynamics.ContinuousTangentSubbundleOnUniv
import HolomorphicAnosov.Dynamics.HirschPughHyperbolicSetFactOne

namespace HolomorphicAnosov
open Set Filter
open scoped ContDiff _root_.Topology Bundle
universe u

/-- For an Anosov diffeomorphism with cyclic shadowing, the nonwandering set is a finite disjoint
union of nonempty compact invariant transitive components with internal finite shadowing (Shub,
Thm. 8.13; Prop. 8.20). -/
theorem smale_original_anosov_component_decomposition
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
    let _Ws : Set M → Set M := fun L =>
      {x | Tendsto (fun k : ℕ => Metric.infDist (((f : M → M)^[k]) x) L)
        atTop (𝓝 0)}
    let _Wu : Set M → Set M := fun L =>
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
          ∃ a ∈ L i, ∀ k ≤ N, dist ((f : M → M)^[k] a) (q k) < ε) := by
  classical
  dsimp only
  let : Bundle.RiemannianBundle (fun x : M ↦
      TangentSpace (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) x) :=
    ⟨metric.toRiemannianMetric⟩
  intro hRiem hC hlam hlam1 hcompl hstableInv hunstableInv hstable hunstable hcyclic
  obtain ⟨stableOn, hstableOn⟩ := continuousRealTangentSubbundle_on_univ Es
  obtain ⟨unstableOn, hunstableOn⟩ := continuousRealTangentSubbundle_on_univ Eu
  let H : HyperbolicSetFactOneDatum f Set.univ :=
    { nonempty := Set.univ_nonempty
      compact := isCompact_univ
      forward_mem := fun _ _ ↦ Set.mem_univ _
      backward_mem := fun _ _ ↦ Set.mem_univ _
      originalMetric := metric
      stable := stableOn
      unstable := unstableOn
      complementary := fun x ↦ by
        rw [hstableOn, hunstableOn]
        exact hcompl x
      stable_invariant := fun x ↦ by
        rw [hstableOn, hstableOn]
        exact hstableInv x
      unstable_invariant := fun x ↦ by
        rw [hunstableOn, hunstableOn]
        exact hunstableInv x
      C := max C 1
      one_le_C := le_max_right _ _
      rate := lam
      rate_pos := hlam
      rate_lt_one := hlam1
      stable_estimate := fun k x v hv ↦ by
        have h := hstable x k v (by simpa only [hstableOn] using hv)
        change ‖mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
          (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((f : M → M)^[k]) x v‖ ≤ max C 1 * lam ^ k * ‖v‖
        exact h.trans (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (le_max_left C 1) (pow_nonneg hlam.le k))
          (norm_nonneg v))
      unstable_estimate := fun k x v hv ↦ by
        have h := hunstable x k v (by simpa only [hunstableOn] using hv)
        change ‖mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
          (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((f.symm : M → M)^[k]) x v‖ ≤ max C 1 * lam ^ k * ‖v‖
        exact h.trans (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (le_max_left C 1) (pow_nonneg hlam.le k))
          (norm_nonneg v))
      isolatingNeighborhood := Set.univ
      isolating_open := isOpen_univ
      subset_isolating := Set.Subset.rfl
      locally_maximal := fun _ ↦ by simp }
  let old : MetricSpace M := inferInstance
  obtain ⟨h, a, d, κ, γ, ε₀, ha, hs, hu, htop, hlength, hκ, hκ1,
      hγ, hε₀, hstablePlaque, hunstablePlaque, bracket, hbracketCont, hbracket⟩ :=
    hirschPughHyperbolicSetFactOne f Set.univ H
  let : MetricSpace M := old
  let F := f.toHomeomorph
  have hpow (g : M ≃ₜ M) (k : ℕ) (x : M) : (g ^ k) x = (g : M → M)^[k] x := by
    induction k with
    | zero => rfl
    | succ k ih => simp [pow_succ', Homeomorph.mul_apply, Function.iterate_succ_apply', ih]
  have hneg (k : ℕ) (x : M) : (F ^ (-(k : ℤ))) x = (f.symm : M → M)^[k] x := by
    rw [zpow_neg, zpow_natCast, ← inv_pow]
    exact hpow F.symm k x
  have hexpD : ∀ x y : M,
      (∀ j : ℤ, d.dist ((F ^ j) x) ((F ^ j) y) ≤ γ) → x = y := by
    intro x y hxy
    let pair : hyperbolicClosedPairDomain Set.univ d ε₀ :=
      ⟨(x, x), Set.mem_univ x, Set.mem_univ x, by simpa only [d.dist_self] using hε₀.le⟩
    have hxx : x ∈ hyperbolicClosedStablePlaque f Set.univ d γ x ∩
        hyperbolicClosedUnstablePlaque f Set.univ d γ x := by
      constructor <;> refine ⟨Set.mem_univ _, fun k ↦ ?_⟩ <;> simpa only [d.dist_self] using hγ.le
    have hyx : y ∈ hyperbolicClosedStablePlaque f Set.univ d γ x ∩
        hyperbolicClosedUnstablePlaque f Set.univ d γ x := by
      constructor
      · refine ⟨Set.mem_univ _, fun k ↦ ?_⟩
        simpa only [zpow_natCast, hpow, F, Diffeomorph.coe_toHomeomorph, d.dist_comm] using hxy (k : ℤ)
      · refine ⟨Set.mem_univ _, fun k ↦ ?_⟩
        simpa only [hneg, d.dist_comm] using hxy (-(k : ℤ))
    have heq := hbracket pair
    have hxB : x = (bracket pair : M) := Set.mem_singleton_iff.mp (heq ▸ hxx)
    have hyB : y = (bracket pair : M) := Set.mem_singleton_iff.mp (heq ▸ hyx)
    exact hxB.trans hyB.symm
  have hdcompact : @CompactSpace M d.toUniformSpace.toTopologicalSpace :=
    htop.symm ▸ (inferInstance : CompactSpace M)
  obtain ⟨η, hη, hmod⟩ :=
    @Dynamics.ManningOriginalBasicSetSignedTraceG7.MetricAdapter.compatible_metric_modulus
      M d hdcompact old htop.symm γ hγ
  have hexp : ∀ x y : M,
      (∀ j : ℤ, dist ((F ^ j) x) ((F ^ j) y) ≤ η / 2) → x = y := by
    intro x y hxy
    exact hexpD x y (fun j ↦ (hmod _ _ ((hxy j).trans_lt (half_lt_self hη))).le)
  obtain ⟨b, L, hL, hdisj, hcover, htrans, hsep⟩ :=
    smale_finite_components_of_expansive_cyclic F (η / 2) (half_pos hη) hexp hcyclic
  have hP := smale_closure_periodic_eq_nonwandering_of_periodic_shadowing
    (f : M → M) (smale_periodic_shadowing_of_cyclic_semiconjugacy f hcyclic)
  refine ⟨b, L, hL, hdisj, hP.symm.trans hcover, htrans, ?_⟩
  intro i
  exact smale_finite_internal_shadowing_of_cyclic F (L i) (hL i).2.2
    (htrans i) (hsep i) hcyclic


end HolomorphicAnosov

