import HolomorphicAnosov.Topology.Franks.SpectralPeriodicDensity
import HolomorphicAnosov.Topology.Franks.LefschetzCoverCount
import HolomorphicAnosov.Dynamics.SmaleSpectralBasins
import HolomorphicAnosov.Dynamics.ManeLinearToralErgodicityTransitivityG1
import HolomorphicAnosov.Dynamics.Bowen.BowenBasicSetMarkovCoding
import HolomorphicAnosov.Topology.PeriodicFibreFromBowenCoding
import HolomorphicAnosov.Topology.Franks.TransitivePartitionIrreducible

noncomputable section
namespace HolomorphicAnosov
universe u
open scoped Manifold _root_.Topology ContDiff Bundle
/-- Compose the original spectral decomposition and Bowen periodic-fibre
construction with the exact periodic bijection. This is Manning Step 19. -/
theorem franks_original_periodic_density
    {n : ℕ} {M : Type u} [MetricSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ∞ M]
    [CompactSpace M] [ConnectedSpace M] [T2Space M] [SecondCountableTopology M]
    [Bundle.RiemannianBundle
      (fun x : M ↦ TangentSpace (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) x)]
    [IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (fun x : M ↦ TangentSpace (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) x)]
    [IsRiemannianManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) M]
    [IsContMDiffRiemannianBundle (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ∞
      (EuclideanSpace ℝ (Fin n))
      (fun x : M ↦ TangentSpace (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) x)]
    (f : Diffeomorph (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) M M ∞)
    (S : InvariantRealTangentSplitting f)
    (hBounds : BundleAnosovBounds f S)
    (q : M ≃ₜ UnitAddTorus (Fin n))
    (A : Matrix.GeneralLinearGroup (Fin n) ℤ)
    (hA : ∀ μ : ℂ, Module.End.HasEigenvalue
      (Matrix.mulVecLin (fun i j : Fin n ↦ (A i j : ℂ))) μ → ‖μ‖ ≠ 1)
    (targetPeriodicDense : Dense (Function.periodicPts (integralToralMap A)))
    (k : C(M, UnitAddTorus (Fin n)))
    (hksem : Function.Semiconj k (f : M → M) (integralToralMap A))
    (periodicInj : Set.InjOn k (Function.periodicPts (f : M → M)))
    (periodicOnto : Set.SurjOn k (Function.periodicPts (f : M → M))
      (Function.periodicPts (integralToralMap A))) :
    Dense (Function.periodicPts (f : M → M)) := by
  classical
  let : Nonempty M := ⟨q.symm 0⟩
  obtain ⟨C, lam, hC, hlam, hlam1, hs, hu⟩ := hBounds
  have hR : IsRiemannianManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) M := inferInstance
  let metric := FranksLefschetzCoverCount.suppliedSmoothMetric (n := n) (M := M)
  obtain ⟨hperiodic,b,L,hb,hL,hdisj,hΩ,horbit,hperiodicL,hisolated,hrestriction,
    hsdisj,hscover,hudisj,hucover,hinter,hproper⟩ :=
    smale_original_anosov_spectral_basins f S.stable S.unstable metric C lam
      hR hC hlam hlam1 S.isCompl S.stable_map S.unstable_map
      (fun x j v hv ↦ hs j x v hv) (fun x j v hv ↦ hu j x v hv)
  have hinv (i) (x : M) : x ∈ L i ↔ f.toHomeomorph x ∈ L i := by
    constructor
    · intro hx
      rw [← (hL i).2.2]
      exact Set.mem_image_of_mem f hx
    · intro hx
      rw [← (hL i).2.2] at hx
      obtain ⟨y,hy,he⟩ := hx
      exact f.injective he ▸ hy
  have hroot : ∀ μ : ℂ, Module.End.HasEigenvalue
      (Matrix.mulVecLin (fun i j : Fin n ↦ (A i j : ℂ))) μ → ¬ IsOfFinOrder μ := by
    intro μ hμ hfin
    obtain ⟨r,hr,he⟩ := hfin.exists_pow_eq_one
    apply hA μ hμ
    have hn : ‖μ‖ ^ r = 1 := by simpa using congrArg norm he
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg μ) (Nat.ne_of_gt hr)).mp hn
  obtain ⟨y,hy⟩ := (Dynamics.mane_linear_toral_ergodicity_transitivity_g1 n A hroot).2
  apply FranksOriginalLift.spectral_periodic_density (f : M → M) (integralToralMap A)
    k hksem periodicOnto periodicInj targetPeriodicDense y hy L
    (fun i ↦ ⟨(hL i).1, (hL i).2.1, fun x hx ↦ (hinv i x).mp hx⟩)
    hdisj (hperiodic.trans hΩ) (by simpa only [hperiodic] using hproper)
  intro i honto z hz
  let G := f.toHomeomorph.subtype (hinv i)
  let : CompactSpace (L i) := isCompact_iff_compactSpace.mp (hL i).2.1
  have hval (m : ℕ) (x : L i) : ((G^m) x).val = ((f : M → M)^[m]) x.val := by
    simpa only [Dynamics.ManningOriginalBasicSetSignedTraceG7.CarrierAdapter.homeomorph_pow_coe,
      Diffeomorph.coe_toHomeomorph] using
      Dynamics.ManningOriginalBasicSetSignedTraceG7.CarrierAdapter.restricted_iterate_val
        f.toHomeomorph (L i) (hinv i) x m
  obtain ⟨x,hx,horb⟩ := horbit i
  have himage : Subtype.val '' Set.range (fun j : ℤ ↦ (G^j) (⟨x,hx⟩ : L i)) =
      Set.range (fun j : ℤ ↦ (f.toEquiv^j) x) := by
    rw [← Set.range_comp]
    congr 1
    funext j
    exact (Dynamics.ManningOriginalBasicSetSignedTraceG7.CarrierAdapter.restricted_zpow_val
      f.toHomeomorph (L i) (hinv i) j ⟨x,hx⟩).trans
      (congrArg (fun g : Equiv.Perm M ↦ g x)
        (Dynamics.ManningOriginalBasicSetSignedTraceG7.CarrierAdapter.homeomorph_zpow_equiv
          f.toHomeomorph j))
  have hdense : Dense (Set.range (fun j : ℤ ↦ (G^j) (⟨x,hx⟩ : L i))) := by
    apply Subtype.dense_iff.mpr
    rw [himage,horb]
  have hperimage : Subtype.val '' Function.periodicPts (G : L i → L i) =
      Function.periodicPts (f : M → M) ∩ L i := by
    ext y
    constructor
    · rintro ⟨v,hv,rfl⟩
      obtain ⟨m,hm,hvm⟩ := Function.mem_periodicPts.mp hv
      refine ⟨Function.mem_periodicPts.mpr ⟨m,hm,?_⟩,v.property⟩
      change ((f : M → M)^[m]) v.val = v.val
      rw [← hval]
      exact congrArg Subtype.val (show (G^m) v=v by
        simpa only [Dynamics.ManningOriginalBasicSetSignedTraceG7.CarrierAdapter.homeomorph_pow_coe]
          using hvm.eq)
    · rintro ⟨hy,hyL⟩
      obtain ⟨m,hm,hym⟩ := Function.mem_periodicPts.mp hy
      refine ⟨⟨y,hyL⟩,Function.mem_periodicPts.mpr ⟨m,hm,?_⟩,rfl⟩
      change ((G : L i → L i)^[m]) ⟨y,hyL⟩ = ⟨y,hyL⟩
      rw [← Dynamics.ManningOriginalBasicSetSignedTraceG7.CarrierAdapter.homeomorph_pow_coe]
      apply Subtype.ext
      exact (hval m ⟨y,hyL⟩).trans hym
  have hpdense : Dense (Function.periodicPts (G : L i → L i)) := by
    apply Subtype.dense_iff.mpr
    rw [hperimage,hperiodicL i]
  have htrans := forward_transitive_of_dense_integer_orbit_and_periodic G ⟨x,hx⟩ hdense hpdense
  have hlocal : ∃ U : Set M, IsOpen U ∧ L i ⊆ U ∧
      L i = ⋂ j : ℤ, ((f.toHomeomorph^j : M ≃ₜ M) : M → M) '' U := by
    have he (j : ℤ) : (fun x : M ↦ (f.toEquiv^j) x) =
        ((f.toHomeomorph^j : M ≃ₜ M) : M → M) := by
      funext x
      exact (congrArg (fun g : Equiv.Perm M ↦ g x)
        (Dynamics.ManningOriginalBasicSetSignedTraceG7.CarrierAdapter.homeomorph_zpow_equiv
          f.toHomeomorph j)).symm
    simpa only [he] using hisolated i
  have hscale (r : ℕ) (x : M) (v : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x) :
      C*lam^r*‖v‖ ≤ max 1 C*lam^r*‖v‖ :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right 1 C)
      (pow_nonneg hlam.le _)) (norm_nonneg _)
  have hcoding : ∀ ε : ℝ, 0 < ε → ∃ (N : ℕ) (B : Fin N → Fin N → Prop)
      (R : Fin N → Set (L i)) (coding : BowenBasicSetCoding.CodeSpace B → L i),
      (∀ a, {x : L i | ∀ j : ℤ, (G ^ j) x ∈ R (a.val j)} = {coding a}) ∧
      Continuous coding ∧ Function.Surjective coding ∧
      (∀ a, coding (BowenBasicSetCoding.codeShift B a) = G (coding a)) ∧
      (∀ a b : BowenBasicSetCoding.CodeSpace B, a.val 0 = b.val 0 →
        ∃ c : BowenBasicSetCoding.CodeSpace B,
          (∀ j : ℤ, j ≤ 0 → c.val j = a.val j) ∧
          (∀ j : ℤ, 0 ≤ j → c.val j = b.val j) ∧
          (∀ j : ℤ, 0 ≤ j → dist ((G ^ j) (coding c)) ((G ^ j) (coding b)) < ε) ∧
          (∀ j : ℤ, j ≤ 0 → dist ((G ^ j) (coding c)) ((G ^ j) (coding a)) < ε)) := by
    intro ε hε
    obtain ⟨N,D,hN,hD,δ,hδ,γ,hγ,R,hR,hdisj,hcover,hmarkov,coding,hit,hcont,hsurj,
      hcov,hfibre,hlabels,hperiod,hsplice⟩ :=
      BowenBasicSetCoding.hyperbolic_basic_set_markov_coding f
        (fun x y _ ↦ (inferInstance : IsRiemannianManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) M).out x y)
        (L i) (hL i).1 (hL i).2.1 (hinv i) S.stable.toDistribution S.unstable.toDistribution
        (continuous_tangent_subbundle_restrict S.stable (L i))
        (continuous_tangent_subbundle_restrict S.unstable (L i))
        (fun x _ ↦ S.isCompl x) (fun x _ ↦ S.stable_map x) (fun x _ ↦ S.unstable_map x)
        (max 1 C) lam (le_max_left _ _) hlam hlam1
        (fun r x _ v hv ↦ (hs r x v hv).trans (hscale r x v))
        (fun r x _ v hv ↦ (hu r x v hv).trans (hscale r x v)) hlocal htrans ε hε
    exact ⟨N, _, R, coding, hit, hcont, hsurj, hcov, hsplice⟩
  obtain ⟨m, hm, hzm⟩ := hz
  obtain ⟨v,hv,r,hr,hvr⟩ := periodic_fibre_from_bowen_coding G A hA
    (fun v : L i ↦ k v.val) (k.continuous.comp continuous_subtype_val)
    (fun v ↦ hksem v.val) (by
      intro w
      obtain ⟨v,hv,hvw⟩ := show w ∈ k '' L i by rw [honto]; trivial
      exact ⟨⟨v,hv⟩,hvw⟩) hcoding z m (by omega) hzm
  refine ⟨v.val,v.property,⟨r,by omega,?_⟩,hv⟩
  change (f : M → M)^[r] v.val = v.val
  rw [← hval]
  exact congrArg Subtype.val (show (G^r) v=v by
    simpa only [Dynamics.ManningOriginalBasicSetSignedTraceG7.CarrierAdapter.homeomorph_pow_coe]
      using hvr)


end HolomorphicAnosov
