import HolomorphicAnosov.Dynamics.Anosov.GlobalLaminationGraphHelpers

noncomputable section
open Set Filter
open scoped ContDiff Manifold _root_.Topology Bundle
namespace HolomorphicAnosov

/-- A smooth map on a compact manifold has uniformly bounded derivative in
any tangent gauge uniformly equivalent to a smooth metric. The metric
operator norm is upper semicontinuous and hence bounded above on the compact
base. The two comparison constants transfer that bound to the supplied gauge.
Applied to the inverse diffeomorphism, this supplies the missing uniform
inverse-linear margin in the cutoff construction. -/
theorem uniform_tangent_gauge_derivative_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {M : Type*} [TopologicalSpace M] [CompactSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ,E) ∞ M]
    (g : Bundle.ContMDiffRiemannianMetric 𝓘(ℝ,E) ∞ E
      (fun x : M ↦ TangentSpace 𝓘(ℝ,E) x))
    (f : M → M) (hf : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,E) ∞ f)
    (ν : ∀ x : M, TangentSpace 𝓘(ℝ,E) x → ℝ)
    (m K : ℝ) (hm : 0 < m) (hK : 0 < K)
    (hlower : ∀ x v, m * ExponentialLift.metricNorm g x v ≤ ν x v)
    (hupper : ∀ x v, ν x v ≤ K * ExponentialLift.metricNorm g x v) :
    ∃ B : ℝ, 0 < B ∧ ∀ x v,
      ν (f x) (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) f x v) ≤ B * ν x v := by
  let : Bundle.RiemannianBundle (fun x : M ↦ TangentSpace 𝓘(ℝ,E) x) :=
    ⟨g.toRiemannianMetric⟩
  have hnorm (x : M) (v : TangentSpace 𝓘(ℝ,E) x) :
      ExponentialLift.metricNorm g x v = ‖v‖ := by
    change Real.sqrt (g.inner x v v) = ‖v‖
    exact (norm_eq_sqrt_real_inner v).symm
  have hsemi : UpperSemicontinuous (fun x : M ↦ ‖mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) f x‖) := by
    intro x
    change UpperSemicontinuousAt (fun y : M ↦ ‖mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) f y‖) x
    rw [upperSemicontinuousAt_iff]
    intro c hc
    exact FixedBlockEstimates.Native.ambient_opNorm_eventually_lt g f hf x hc
  obtain ⟨B,hB⟩ := (hsemi.upperSemicontinuousOn Set.univ).bddAbove_of_isCompact isCompact_univ
  let B' := max B 1
  have hB' : 0 < B' := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hbound (x : M) : ‖mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) f x‖ ≤ B' :=
    (hB ⟨x,mem_univ x,rfl⟩).trans (le_max_left _ _)
  refine ⟨K * B' / m, by positivity, ?_⟩
  intro x v
  have hv := hlower x v
  rw [hnorm] at hv
  have hnormv : ‖v‖ ≤ ν x v / m := (le_div_iff₀ hm).mpr (by simpa [mul_comm] using hv)
  calc
    ν (f x) (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) f x v) ≤
        K * ‖mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) f x v‖ := by simpa only [hnorm] using hupper (f x) _
    _ ≤ K * (B' * ‖v‖) := mul_le_mul_of_nonneg_left
      (((mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) f x).le_opNorm v).trans
        (mul_le_mul_of_nonneg_right (hbound x) (norm_nonneg v))) hK.le
    _ ≤ K * (B' * (ν x v / m)) := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hnormv hB'.le) hK.le
    _ = (K * B' / m) * ν x v := by ring
end HolomorphicAnosov

noncomputable section
open scoped ContDiff NNReal Manifold
namespace HolomorphicAnosov

/-- A smooth sufficiently small global Lipschitz perturbation of a linear
equivalence is a smooth diffeomorphism. Mathlib's contraction inverse theorem
first gives the global homeomorphism; the Wells inverse theorem upgrades its
actual inverse to smoothness. Source: Wells (1976), pp.285–287, and the
global cutoff step in Smale (1963), pp.103–106. -/
theorem diffeomorph_of_small_lipschitz_perturbation
    {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (T : X ≃L[ℝ] Y) (f : X → Y) (hf : ContDiff ℝ ∞ f)
    (ε : ℝ≥0) (hR : LipschitzWith ε (fun x ↦ f x - T x))
    (hsmall : ‖T.symm.toContinuousLinearMap‖ * ε < 1) :
    ∃ D : Diffeomorph 𝓘(ℝ, X) 𝓘(ℝ, Y) X Y ∞, (D : X → Y) = f := by
  have happrox : ApproximatesLinearOn f T.toContinuousLinearMap Set.univ ε :=
    hR.lipschitzOnWith.approximatesLinearOn
  have hc : Subsingleton X ∨ ε < ‖T.symm.toContinuousLinearMap‖₊⁻¹ := by
    rcases subsingleton_or_nontrivial X with hX | hX
    · exact Or.inl hX
    · let : Nontrivial Y := T.symm.toEquiv.nontrivial
      right
      have hp := T.symm.norm_pos
      change (ε : ℝ) < ‖T.symm.toContinuousLinearMap‖⁻¹
      rw [← one_div]
      apply (lt_div_iff₀ hp).mpr
      simpa [mul_comm] using hsmall
  let H : X ≃ₜ Y := happrox.toHomeomorph f hc
  have hH : (H : X → Y) = f := rfl
  have hinv := parameter_graph_smooth_inverse T H ⊤ (by simp)
    (by simpa only [hH] using hf) ‖T.symm.toContinuousLinearMap‖₊ ε le_rfl hsmall
    (by simpa only [hH] using hR)
  exact ⟨{ toEquiv := H.toEquiv
           contMDiff_toFun := by apply ContDiff.contMDiff; exact hf
           contMDiff_invFun := hinv.contMDiff }, rfl⟩

end HolomorphicAnosov




noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped ContDiff Manifold Topology _root_.Topology Bundle
namespace HolomorphicAnosov.HPS
universe u
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [FiniteDimensional ℝ E]
variable (X : Type u) [EMetricSpace X] [ChartedSpace E X]
variable [IsManifold 𝓘(ℝ,E) ∞ X]
variable [Bundle.RiemannianBundle (fun p : X ↦ TangentSpace 𝓘(ℝ,E) p)]

/-- A continuous fibre norm used for the HPS local graph construction. -/
structure StrongPlaqueGauge where
  value : ∀ p : X, TangentSpace 𝓘(ℝ,E) p → ℝ
  nonneg : ∀ p v, 0 ≤ value p v
  definite : ∀ p v, value p v = 0 ↔ v = 0
  triangle : ∀ p v w, value p (v + w) ≤ value p v + value p w
  smul : ∀ p (c : ℝ) v, value p (c • v) = ‖c‖ * value p v
  continuous : Continuous (fun z : TangentBundle 𝓘(ℝ,E) X ↦ value z.proj z.snd)

namespace StrongPlaqueGauge
variable {X}
/-- The adapted norm on a linear subspace; its algebraic operations are unchanged. -/
abbrev group (A : StrongPlaqueGauge (E := E) X)
    (D : RealTangentDistribution 𝓘(ℝ,E) X) (p : X) :=
  finiteDimensionalRenorm (fun v : D p ↦ A.value p v.val)
    (fun v ↦ A.nonneg p v.val)
    (fun v ↦ by simpa only [Submodule.coe_eq_zero] using A.definite p v.val)
    (fun v w ↦ A.triangle p v.val w.val) (fun c v ↦ A.smul p c v.val)

/-- Scalar multiplication for the adapted fibre norm. -/
abbrev space (A : StrongPlaqueGauge (E := E) X)
    (D : RealTangentDistribution 𝓘(ℝ,E) X) (p : X) :
    @NormedSpace ℝ (D p) _ (A.group D p).toSeminormedAddCommGroup :=
  @NormedSpace.mk ℝ (D p) _ (A.group D p).toSeminormedAddCommGroup inferInstance
    (fun c v ↦ (A.smul p c v.val).le)
/-- The finite-rank atlas induced by the adapted gauge on a continuous subbundle. -/
abbrev atlas (A : StrongPlaqueGauge (E := E) X)
    (D : ContinuousRealTangentSubbundle 𝓘(ℝ,E) X) :=
  adaptedSubbundleFiniteRankNormedAtlas D (fun p v ↦ A.value p v.val)
    (fun p v ↦ A.nonneg p v.val)
    (fun p v ↦ by simpa only [Submodule.coe_eq_zero] using A.definite p v.val)
    (fun p v w ↦ A.triangle p v.val w.val) (fun p c v ↦ A.smul p c v.val)
    (by
      let := subbundleSigmaTopology D
      exact A.continuous.comp (show Continuous
        (fun z : Sigma fun p ↦ D.toDistribution p ↦
          (⟨z.1,z.2.val⟩ : TangentBundle 𝓘(ℝ,E) X)) from continuous_induced_dom))

end StrongPlaqueGauge
variable (f : Diffeomorph 𝓘(ℝ,E) 𝓘(ℝ,E) X X ∞)
variable (S : InvariantRealTangentSplitting f)

/-- Concrete local stable plaques from the HPS graph construction, without any supplied
leaf partition. The adapted gauge, the actual cutoff diffeomorphisms and graph maps
are retained, together with smoothness, original-map trapping and orbit capture. -/
structure LocalStrongPlaqueConstruction (A : StrongPlaqueGauge (E := E) X) where
  radius : ℝ
  radius_pos : 0 < radius
  rate : ℝ
  rate_pos : 0 < rate
  rate_lt_one : rate < 1
  graph : ∀ p : X, S.stable.toDistribution p → S.unstable.toDistribution p
  graph_zero : ∀ p, graph p 0 = 0
  graph_lipschitz : ∀ p,
    @LipschitzWith _ _ (A.group S.stable.toDistribution p).toMetricSpace.toEMetricSpace.toPseudoEMetricSpace
      (A.group S.unstable.toDistribution p).toMetricSpace.toEMetricSpace.toPseudoEMetricSpace
      1 (graph p)
  graph_smooth : ∀ p,
    letI := A.group S.stable.toDistribution p
    letI := A.space S.stable.toDistribution p
    letI := A.group S.unstable.toDistribution p
    letI := A.space S.unstable.toDistribution p
    ContDiff ℝ ∞ (graph p)
  graph_regular : ∀ r : ℕ, 1 ≤ r →
    letI _groupsS (p : X) := A.group S.stable.toDistribution p
    letI _spacesS (p : X) := A.space S.stable.toDistribution p
    letI _groupsU (p : X) := A.group S.unstable.toDistribution p
    letI _spacesU (p : X) := A.space S.unstable.toDistribution p
    letI := subbundleSigmaTopology S.stable
    letI := subbundleSigmaTopology S.unstable
    JointFiberContDiff (A.atlas S.stable) (A.atlas S.unstable) id r graph
  graph_gauge : ∀ p y, A.value p ((graph p y).val + y.val) = A.value p y.val
  merge_continuous :
    letI := subbundleSigmaTopology S.unstable
    letI := subbundleSigmaTopology S.stable
    letI := productSigmaTopology (V := fun p ↦ S.unstable.toDistribution p)
      (W := fun p ↦ S.stable.toDistribution p)
    Continuous (fun z : Sigma (fun p ↦ S.unstable.toDistribution p × S.stable.toDistribution p) ↦
      (⟨z.1,z.2.1.val + z.2.2.val⟩ : TangentBundle 𝓘(ℝ,E) X))
  metric : Bundle.ContMDiffRiemannianMetric 𝓘(ℝ,E) ∞ E
    (fun p : X ↦ TangentSpace 𝓘(ℝ,E) p)
  cutoff : ∀ p,
    letI := A.group S.stable.toDistribution p
    letI := A.space S.stable.toDistribution p
    letI := A.group S.unstable.toDistribution p
    letI := A.space S.unstable.toDistribution p
    letI := A.group S.stable.toDistribution (f p)
    letI := A.space S.stable.toDistribution (f p)
    letI := A.group S.unstable.toDistribution (f p)
    letI := A.space S.unstable.toDistribution (f p)
    Diffeomorph 𝓘(ℝ,S.unstable.toDistribution p × S.stable.toDistribution p)
      𝓘(ℝ,S.unstable.toDistribution (f p) × S.stable.toDistribution (f p))
      (S.unstable.toDistribution p × S.stable.toDistribution p)
      (S.unstable.toDistribution (f p) × S.stable.toDistribution (f p)) ∞
  cutoff_graph : ∀ p,
    (cutoff p).toFun ⁻¹' Set.range (fun y ↦ (graph (f p) y, y)) =
      Set.range (fun y ↦ (graph p y, y))
  cutoff_contract : ∀ p (y : S.stable.toDistribution p),
    A.value (f p) ((cutoff p).toFun (graph p y, y)).2.val ≤ rate * A.value p y.val
  plaque : ∀ p : X, S.stable.toDistribution p → X
  plaque_formula : ∀ p y,
    plaque p y = ExponentialLift.riemannianExp metric p ((graph p y).val + y.val)
  exponential_domain : ∀ p y, A.value p y.val < radius →
    (⟨p, (graph p y).val + y.val⟩ : TangentBundle 𝓘(ℝ,E) X) ∈
      riemannianExponentialDomain metric
  exponential_chart : ∀ _p : X, PartialDiffeomorph 𝓘(ℝ,E) 𝓘(ℝ,E) E X ∞
  exponential_chart_apply : ∀ p v,
    exponential_chart p v = ExponentialLift.riemannianExp metric p
      ((tangentSpaceCastModel 𝓘(ℝ,E) p).symm v)
  exponential_chart_source : ∀ p y, A.value p y.val < radius →
    tangentSpaceCastModel 𝓘(ℝ,E) p ((graph p y).val + y.val) ∈ (exponential_chart p).source
  plaque_zero : ∀ p, plaque p 0 = p
  plaque_injective : ∀ p, Set.InjOn (plaque p) {y | A.value p y.val < radius}
  disc_open : ∀ p,
    letI := A.group S.stable.toDistribution p
    IsOpen {y : S.stable.toDistribution p | A.value p y.val < radius}
  plaque_continuous :
    letI := subbundleSigmaTopology S.stable
    ContinuousOn (fun z : Sigma (fun p ↦ S.stable.toDistribution p) ↦ plaque z.1 z.2)
      {z | A.value z.1 z.2.val < radius}
  plaque_smooth : ∀ p,
    letI := A.group S.stable.toDistribution p
    letI := A.space S.stable.toDistribution p
    ContMDiffOn 𝓘(ℝ,S.stable.toDistribution p) 𝓘(ℝ,E) ∞
      (plaque p) {y | A.value p y.val < radius}
  plaque_immersion : ∀ p y, A.value p y.val < radius →
    letI := A.group S.stable.toDistribution p
    letI := A.space S.stable.toDistribution p
    Manifold.IsImmersionAt 𝓘(ℝ,S.stable.toDistribution p) 𝓘(ℝ,E) 1 (plaque p) y
  plaque_derivative_zero : ∀ p v,
    letI := A.group S.stable.toDistribution p
    letI := A.space S.stable.toDistribution p
    mfderiv 𝓘(ℝ,S.stable.toDistribution p) 𝓘(ℝ,E) (plaque p) 0 v = v.val
  coordinate : ∀ p : X, X → S.stable.toDistribution p
  coordinate_domain : TopologicalSpace.Opens (X × X)
  coordinate_domain_diagonal : ∀ p, (p,p) ∈ coordinate_domain
  exponential_chart_target : ∀ p, (exponential_chart p).target = {q | (p,q) ∈ coordinate_domain}
  coordinate_smooth : ∀ p,
    letI := A.group S.stable.toDistribution p
    letI := A.space S.stable.toDistribution p
    ContMDiffOn 𝓘(ℝ,E) 𝓘(ℝ,S.stable.toDistribution p) ∞
      (coordinate p) {q | (p,q) ∈ coordinate_domain}
  coordinate_inverse : ∀ p y, A.value p y.val < radius → coordinate p (plaque p y) = y
  coordinate_domain_plaque : ∀ p y, A.value p y.val < radius → (p,plaque p y) ∈ coordinate_domain
  plaque_forward : ∀ p y, A.value p y.val < radius →
    f (plaque p y) = plaque (f p) ((cutoff p).toFun (graph p y,y)).2
  uniform_asymptotic : ∀ ε : ENNReal, 0 < ε →
    ∃ N : ℕ, ∀ n ≥ N, ∀ p y, A.value p y.val < radius →
      edist ((f : X → X)^[n] p) ((f : X → X)^[n] (plaque p y)) < ε
  capture_distance : ENNReal
  capture_distance_pos : 0 < capture_distance
  local_capture : ∀ p q,
    (∀ n : ℕ, edist ((f : X → X)^[n] p) ((f : X → X)^[n] q) < capture_distance) →
    ∃ y, A.value p y.val < radius ∧ plaque p y = q
  asymptotic_iff : ∀ p q,
    Tendsto (fun n : ℕ ↦ edist ((f : X → X)^[n] p) ((f : X → X)^[n] q)) atTop (𝓝 0) ↔
    ∃ N : ℕ, ∃ y : S.stable.toDistribution ((f : X → X)^[N] p),
      A.value _ y.val < radius ∧ plaque _ y = (f : X → X)^[N] q

set_option maxHeartbeats 800000 in
/-- HPS (5.1)--(5.5), pp.53--63: construct stable plaques from the adapted splitting
and the exponential cutoff, independently of any pre-existing leaf partition.

Proof. Equip the splitting with its finite-energy norm, choose one cutoff error
below both the graph and every finite-order jet margins, and obtain the unique
parameter graphs. Exponentiation in a common logarithm domain gives injective
smooth immersed plaques and a left coordinate inverse. Their graph return has
rate less than one and agrees with the original map; uniform exponential
continuity gives asymptotic contraction. Conversely, sufficiently close forward
orbits are logarithmically conjugate to cutoff orbits and the bounded-orbit graph
characterization captures them. The inverse derivative margin also makes the
cutoff a whole-fibre diffeomorphism, preserving the Euclidean-leaf consumer. -/
theorem local_strong_plaque_construction
    [CompactSpace X] [SecondCountableTopology X]
    [IsContMDiffRiemannianBundle 𝓘(ℝ,E) ∞ E
      (fun x : X ↦ TangentSpace 𝓘(ℝ,E) x)]
    [IsRiemannianManifold 𝓘(ℝ,E) X]
    (h : BundleAnosovBounds f S) :
    ∃ A : StrongPlaqueGauge (E := E) X, Nonempty (LocalStrongPlaqueConstruction X f S A) := by
  obtain ⟨θ, K, νs, νu, ν, hθ, hθ1, hK, hνscontinuous, hνucontinuous,
    hνsupper, hνuupper, hνsplit, hνzero, hνadd, hνsmul, hνlower,
    hνstable_contract, hνunstable_contract, hνcontinuous⟩ :=
    continuous_anosov_finite_energy_split_norm X f S h
  have hνnonneg (x : X) (v : TangentSpace 𝓘(ℝ, E) x) : 0 ≤ ν x v := by
    linarith [norm_nonneg v, hνlower x v]
  have hνdef (x : X) (v : TangentSpace 𝓘(ℝ, E) x) : ν x v = 0 ↔ v = 0 := by
    constructor
    · intro hv
      apply norm_eq_zero.mp
      simpa [hv] using hνlower x v
    · rintro rfl
      exact hνzero x
  let nν := continuousRestrictedTangentNorm_univ ν hνnonneg hνdef hνadd hνsmul hνcontinuous
  obtain ⟨gMetric, hm, hM, hmpos, hMpos, hνlowerMetric, hνupperMetric⟩ :=
    exists_metric_uniform_comparison X nν
  have hfA : MapsTo f (Set.univ : Set X) Set.univ := fun _ _ ↦ mem_univ _
  have hh : IsHomeomorph (fun p : (Set.univ : Set X) ↦
      (⟨f p, hfA p.property⟩ : (Set.univ : Set X))) := by
    exact ((Homeomorph.Set.univ X).trans
      (f.toHomeomorph.trans (Homeomorph.Set.univ X).symm)).isHomeomorph
  have hcutoff := fun (ε : ℝ) (hε : 0 < ε) ↦
    ExponentialCutoff.exponential_cutoff_extension gMetric Set.univ isCompact_univ f
      (⊤ : ℕ∞) (by simp) f.contMDiff hfA hh nν ε hε
  let νU (p : X) (v : S.unstable.toDistribution p) := ν p v.val
  let νS (p : X) (v : S.stable.toDistribution p) := ν p v.val
  have hzeroU (p : X) (v : S.unstable.toDistribution p) : νU p v = 0 ↔ v = 0 := by
    simpa only [νU, νS, Submodule.coe_eq_zero] using hνdef p v.val
  have hzeroS (p : X) (v : S.stable.toDistribution p) : νS p v = 0 ↔ v = 0 := by
    simpa only [νU, νS, Submodule.coe_eq_zero] using hνdef p v.val
  have hnormU : letI := subbundleSigmaTopology S.unstable
      Continuous (fun z : Sigma fun p ↦ S.unstable.toDistribution p ↦ νU z.1 z.2) := by
    let := subbundleSigmaTopology S.unstable
    exact hνcontinuous.comp (show Continuous
      (fun z : Sigma fun p ↦ S.unstable.toDistribution p ↦
        (⟨z.1, z.2.val⟩ : TangentBundle 𝓘(ℝ, E) X)) from continuous_induced_dom)
  have hnormS : letI := subbundleSigmaTopology S.stable
      Continuous (fun z : Sigma fun p ↦ S.stable.toDistribution p ↦ νS z.1 z.2) := by
    let := subbundleSigmaTopology S.stable
    exact hνcontinuous.comp (show Continuous
      (fun z : Sigma fun p ↦ S.stable.toDistribution p ↦
        (⟨z.1, z.2.val⟩ : TangentBundle 𝓘(ℝ, E) X)) from continuous_induced_dom)
  let atlasU := adaptedSubbundleFiniteRankNormedAtlas S.unstable νU
    (fun p v ↦ hνnonneg p v.val) hzeroU
    (fun p v w ↦ hνadd p v.val w.val) (fun p c v ↦ hνsmul p c v.val) hnormU
  let atlasS := adaptedSubbundleFiniteRankNormedAtlas S.stable νS
    (fun p v ↦ hνnonneg p v.val) hzeroS
    (fun p v w ↦ hνadd p v.val w.val) (fun p c v ↦ hνsmul p c v.val) hnormS
  let derivativeEquiv (p : X) := f.mfderivToContinuousLinearEquiv (by simp) p
  let rawTU (p : X) := (derivativeEquiv p).toLinearEquiv.ofSubmodules
    (S.unstable.toDistribution p) (S.unstable.toDistribution (f p)) (S.unstable_map p)
  let rawTS (p : X) := (derivativeEquiv p).toLinearEquiv.ofSubmodules
    (S.stable.toDistribution p) (S.stable.toDistribution (f p)) (S.stable_map p)
  let groupsU (p : X) := finiteDimensionalRenorm (νU p)
    (fun v ↦ hνnonneg p v.val) (hzeroU p)
    (fun v w ↦ hνadd p v.val w.val) (fun c v ↦ hνsmul p c v.val)
  let spacesU (p : X) : @NormedSpace ℝ (S.unstable.toDistribution p) _
      (groupsU p).toSeminormedAddCommGroup :=
    @NormedSpace.mk ℝ (S.unstable.toDistribution p) _ (groupsU p).toSeminormedAddCommGroup
      inferInstance (fun c v ↦ (hνsmul p c v.val).le)
  let groupsS (p : X) := finiteDimensionalRenorm (νS p)
    (fun v ↦ hνnonneg p v.val) (hzeroS p)
    (fun v w ↦ hνadd p v.val w.val) (fun c v ↦ hνsmul p c v.val)
  let spacesS (p : X) : @NormedSpace ℝ (S.stable.toDistribution p) _
      (groupsS p).toSeminormedAddCommGroup :=
    @NormedSpace.mk ℝ (S.stable.toDistribution p) _ (groupsS p).toSeminormedAddCommGroup
      inferInstance (fun c v ↦ (hνsmul p c v.val).le)
  let := subbundleSigmaTopology S.unstable
  let := subbundleSigmaTopology S.stable
  let := productSigmaTopology (V := fun p ↦ S.unstable.toDistribution p)
    (W := fun p ↦ S.stable.toDistribution p)
  let atlas := @splitFiniteRankNormedAtlas X _
    (fun p ↦ S.unstable.toDistribution p) (fun p ↦ S.stable.toDistribution p)
    groupsU spacesU groupsS spacesS _ _ atlasU atlasS
  let TU (p : X) : S.unstable.toDistribution p ≃L[ℝ] S.unstable.toDistribution (f p) :=
    (rawTU p).toContinuousLinearEquiv
  let TS (p : X) : S.stable.toDistribution p →L[ℝ] S.stable.toDistribution (f p) :=
    (rawTS p).toContinuousLinearEquiv.toContinuousLinearMap
  have hTUinv (p : X) (v : S.unstable.toDistribution (f p)) :
      ((TU p).symm v).val = mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) f.symm (f p) v.val := by
    obtain ⟨w, rfl⟩ := (TU p).surjective v
    rw [ContinuousLinearEquiv.symm_apply_apply]
    exact (derivative_inverse_forward f p w.val).symm
  have hTSbound (p : X) :
      letI := groupsS p
      letI : SeminormedAddCommGroup (S.stable.toDistribution p) :=
        (groupsS p).toSeminormedAddCommGroup
      letI := spacesS p
      letI := groupsS (f p)
      letI : SeminormedAddCommGroup (S.stable.toDistribution (f p)) :=
        (groupsS (f p)).toSeminormedAddCommGroup
      letI := spacesS (f p)
      ‖TS p‖ ≤ θ := by
    let := groupsS p
    let : SeminormedAddCommGroup (S.stable.toDistribution p) :=
      (groupsS p).toSeminormedAddCommGroup
    let := spacesS p
    let := groupsS (f p)
    let : SeminormedAddCommGroup (S.stable.toDistribution (f p)) :=
      (groupsS (f p)).toSeminormedAddCommGroup
    let := spacesS (f p)
    apply (TS p).opNorm_le_bound hθ.le
    intro v
    change ν (f p) ((TS p v).val) ≤ θ * ν p v.val
    exact hνstable_contract p v
  have hTUbound (p : X) :
      letI := groupsU p
      letI : SeminormedAddCommGroup (S.unstable.toDistribution p) :=
        (groupsU p).toSeminormedAddCommGroup
      letI := spacesU p
      letI := groupsU (f p)
      letI : SeminormedAddCommGroup (S.unstable.toDistribution (f p)) :=
        (groupsU (f p)).toSeminormedAddCommGroup
      letI := spacesU (f p)
      ‖(TU p).symm.toContinuousLinearMap‖ ≤ θ := by
    let := groupsU p
    let : SeminormedAddCommGroup (S.unstable.toDistribution p) :=
      (groupsU p).toSeminormedAddCommGroup
    let := spacesU p
    let := groupsU (f p)
    let : SeminormedAddCommGroup (S.unstable.toDistribution (f p)) :=
      (groupsU (f p)).toSeminormedAddCommGroup
    let := spacesU (f p)
    apply (TU p).symm.toContinuousLinearMap.opNorm_le_bound hθ.le
    intro v
    change ν p ((TU p).symm v).val ≤ θ * ν (f p) v.val
    rw [hTUinv]
    have hv := hνunstable_contract (f p) v
    have hbaseν := congrArg (fun q : X ↦ (fun v : E ↦ ν q v)) (f.symm_apply_apply p)
    exact (congrFun hbaseν (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) f.symm (f p) v.val)) ▸ hv
  have hT : Continuous (fun z : Sigma (fun p ↦
      S.unstable.toDistribution p × S.stable.toDistribution p) ↦
      (⟨f z.1, (TU z.1 z.2.1, TS z.1 z.2.2)⟩ :
        Sigma (fun p ↦ S.unstable.toDistribution p × S.stable.toDistribution p))) := by
    have hpair : Continuous (fun z : Sigma (fun p ↦
        S.unstable.toDistribution p × S.stable.toDistribution p) ↦
        ((⟨z.1, z.2.1⟩ : Sigma fun p ↦ S.unstable.toDistribution p),
          (⟨z.1, z.2.2⟩ : Sigma fun p ↦ S.stable.toDistribution p))) :=
      continuous_induced_dom
    have hiU : Continuous (fun z : Sigma fun p ↦ S.unstable.toDistribution p ↦
        (⟨z.1, z.2.val⟩ : TangentBundle 𝓘(ℝ, E) X)) := continuous_induced_dom
    have hiS : Continuous (fun z : Sigma fun p ↦ S.stable.toDistribution p ↦
        (⟨z.1, z.2.val⟩ : TangentBundle 𝓘(ℝ, E) X)) := continuous_induced_dom
    have hd := f.contMDiff.continuous_tangentMap (by simp)
    apply continuous_induced_rng.mpr
    apply Continuous.prodMk
    · apply continuous_induced_rng.mpr
      exact hd.comp (hiU.comp hpair.fst)
    · apply continuous_induced_rng.mpr
      exact hd.comp (hiS.comp hpair.snd)
  let opU (p : X) : ℝ :=
    letI : SeminormedAddCommGroup (S.unstable.toDistribution p) :=
      (groupsU p).toSeminormedAddCommGroup
    letI : SeminormedAddCommGroup (S.unstable.toDistribution (f p)) :=
      (groupsU (f p)).toSeminormedAddCommGroup
    ‖(TU p).symm.toContinuousLinearMap‖
  let opS (p : X) : ℝ :=
    letI : SeminormedAddCommGroup (S.stable.toDistribution p) :=
      (groupsS p).toSeminormedAddCommGroup
    letI : SeminormedAddCommGroup (S.stable.toDistribution (f p)) :=
      (groupsS (f p)).toSeminormedAddCommGroup
    ‖TS p‖
  have hsupU : sSup (Set.range opU) < (1 : ℝ)⁻¹ := by
    rw [inv_one]
    apply lt_of_le_of_lt (Real.sSup_le ?_ hθ.le) hθ1
    rintro _ ⟨p, rfl⟩
    exact hTUbound p
  have hsupS : sSup (Set.range opS) < (1 : ℝ) := by
    apply lt_of_le_of_lt (Real.sSup_le ?_ hθ.le) hθ1
    rintro _ ⟨p, rfl⟩
    exact hTSbound p
  have hgraph := @parameter_graph_construction X _
    (fun p ↦ S.unstable.toDistribution p) (fun p ↦ S.stable.toDistribution p)
    groupsU spacesU groupsS spacesS _ _ _ _ 1 (by simp)
    atlas f.toHomeomorph TU TS hT 1 zero_lt_one hsupU hsupS
  let merge (p : X) :
      (S.unstable.toDistribution p × S.stable.toDistribution p) ≃L[ℝ]
        TangentSpace 𝓘(ℝ, E) p :=
    (Submodule.prodEquivOfIsCompl (S.unstable.toDistribution p)
      (S.stable.toDistribution p) (S.isCompl p).symm).toContinuousLinearEquiv
  have hmerge : Continuous (fun z : Sigma (fun p ↦
      S.unstable.toDistribution p × S.stable.toDistribution p) ↦
      (⟨z.1, merge z.1 z.2⟩ : TangentBundle 𝓘(ℝ, E) X)) := by
    have hpair : Continuous (fun z : Sigma (fun p ↦
        S.unstable.toDistribution p × S.stable.toDistribution p) ↦
        ((⟨z.1, z.2.1⟩ : Sigma fun p ↦ S.unstable.toDistribution p),
          (⟨z.1, z.2.2⟩ : Sigma fun p ↦ S.stable.toDistribution p))) := continuous_induced_dom
    have hiU : Continuous (fun z : Sigma fun p ↦ S.unstable.toDistribution p ↦
        (⟨z.1, z.2.val⟩ : TangentBundle 𝓘(ℝ, E) X)) := continuous_induced_dom
    have hiS : Continuous (fun z : Sigma fun p ↦ S.stable.toDistribution p ↦
        (⟨z.1, z.2.val⟩ : TangentBundle 𝓘(ℝ, E) X)) := continuous_induced_dom
    apply continuous_iff_continuousAt.mpr
    intro z
    have hu := (FiberBundle.continuousAt_totalSpace E _).mp ((hiU.comp hpair.fst).continuousAt (x := z))
    have hs := (FiberBundle.continuousAt_totalSpace E _).mp ((hiS.comp hpair.snd).continuousAt (x := z))
    apply (FiberBundle.continuousAt_totalSpace E _).mpr
    refine ⟨hu.1, ?_⟩
    apply (hu.2.add hs.2).congr_of_eventuallyEq
    have hb := (FiberBundle.continuous_proj E (TangentSpace 𝓘(ℝ, E))).comp
      (hiU.comp hpair.fst)
    filter_upwards [hb.continuousAt.preimage_mem_nhds
      ((trivializationAt E (TangentSpace 𝓘(ℝ, E)) z.1).open_baseSet.mem_nhds
        (mem_baseSet_trivializationAt E (TangentSpace 𝓘(ℝ, E)) z.1))] with w hw
    change ((trivializationAt E (TangentSpace 𝓘(ℝ, E)) z.1)
      ⟨w.1, w.2.1.val + w.2.2.val⟩).2 = _
    have hlin := congrArg (fun l : TangentSpace 𝓘(ℝ, E) w.1 → E ↦
      l (w.2.1.val + w.2.2.val) = l w.2.1.val + l w.2.2.val)
      (Bundle.Trivialization.coe_linearMapAt_of_mem (R := ℝ)
        (trivializationAt E (TangentSpace 𝓘(ℝ, E)) z.1) hw)
    exact hlin.mp (map_add _ _ _)
  have hsplitContinuous : Continuous (fun z : TangentBundle 𝓘(ℝ, E) X ↦
      (⟨z.proj, (merge z.proj).symm z.snd⟩ : Sigma (fun p ↦
        S.unstable.toDistribution p × S.stable.toDistribution p))) := by
    apply continuous_induced_rng.mpr
    apply Continuous.prodMk
    · apply continuous_induced_rng.mpr
      exact NativeSplittingPreparation.continuous_native_projection
        (I := 𝓘(ℝ, E)) S.unstable S.stable (fun p ↦ (S.isCompl p).symm)
    · apply continuous_induced_rng.mpr
      convert NativeSplittingPreparation.continuous_native_projection
        (I := 𝓘(ℝ, E)) S.stable S.unstable S.isCompl using 1
      funext z
      change (⟨z.proj, (((Submodule.prodEquivOfIsCompl
        (S.unstable.toDistribution z.proj) (S.stable.toDistribution z.proj)
          (S.isCompl z.proj).symm).symm z.snd).2 : TangentSpace 𝓘(ℝ, E) z.proj)⟩ :
          TangentBundle 𝓘(ℝ, E) X) = _
      rw [Submodule.prodEquivOfIsCompl_symm_apply]
      rfl
  have hνmerge (p : X) (v : S.unstable.toDistribution p × S.stable.toDistribution p) :
      ν p (merge p v) = max (ν p v.1.val) (ν p v.2.val) := by
    have hsplitpair :
        (Submodule.prodEquivOfIsCompl (S.stable.toDistribution p)
          (S.unstable.toDistribution p) (S.isCompl p)).symm (merge p v) = (v.2, v.1) := by
      apply (Submodule.prodEquivOfIsCompl _ _ (S.isCompl p)).symm_apply_eq.mpr
      change v.1.val + v.2.val = v.2.val + v.1.val
      exact add_comm _ _
    have hz := hνsplit p 0
    have hu := hνsplit p v.1.val
    have hs := hνsplit p v.2.val
    have hb := hνsplit p (merge p v)
    simp only [map_zero, Prod.fst_zero, Prod.snd_zero, Submodule.coe_zero, hνzero] at hz
    simp only [Submodule.prodEquivOfIsCompl_symm_apply_right,
      Submodule.coe_zero] at hu
    simp only [Submodule.prodEquivOfIsCompl_symm_apply_left,
      Submodule.coe_zero] at hs
    rw [hsplitpair] at hb
    dsimp only at hu hs hb
    rw [hu, hs, hb]
    have hnonneg := hνnonneg p (merge p v)
    rw [hb] at hnonneg
    rw [max_comm (νs p 0) (νu p v.1.val), max_max_max_comm,
      max_comm (νu p v.1.val) (νs p v.2.val), ← hz, max_eq_left hnonneg]
  obtain ⟨δgraph, hδgraph, hgraph⟩ := hgraph
  obtain ⟨inverseBound,hInverseBound,hInverseGauge⟩ :=
    uniform_tangent_gauge_derivative_bound gMetric f.symm f.symm.contMDiff ν
      hm hM hmpos hMpos
      (fun p v ↦ hνlowerMetric ⟨p,mem_univ p⟩ v)
      (fun p v ↦ hνupperMetric ⟨p,mem_univ p⟩ v)
  obtain ⟨εJet, hεJet, hjetThreshold⟩ := parameter_graph_contraction_threshold
    θ θ 1 hθ.le hθ.le zero_lt_one (by simpa using hθ1) hθ1
  let ε := min (min (min (δgraph / 2) (εJet / 2)) ((1 - θ) / 4))
    (1 / (2 * inverseBound))
  have hεpos : 0 < ε :=
    lt_min (lt_min (lt_min (half_pos hδgraph) (half_pos hεJet)) (by linarith)) (by positivity)
  have hεgraph : ε < δgraph :=
    ((min_le_left _ _).trans ((min_le_left _ _).trans (min_le_left _ _))).trans_lt
      (half_lt_self hδgraph)
  have hεjet : ε < εJet :=
    ((min_le_left _ _).trans ((min_le_left _ _).trans (min_le_right _ _))).trans_lt
      (half_lt_self hεJet)
  have hεrate : θ + ε < 1 := by
    have he : ε ≤ (1 - θ) / 4 := (min_le_left _ _).trans (min_le_right _ _)
    linarith
  obtain ⟨ρexp, Rexp, δexp, b, logExp, hρexp, hRexp, hRρexp,
    hδexp, hδRexp, hb, hExpInjective, hExtension, hAgreement⟩ :=
    hcutoff ε hεpos
  let extension := ExponentialCutoff.extension Set.univ f gMetric
    (fun p ↦ ExponentialLift.centeredLift gMetric f logExp p) Rexp δexp
  let G (p : X) (v : S.unstable.toDistribution p × S.stable.toDistribution p) :
      S.unstable.toDistribution (f p) × S.stable.toDistribution (f p) :=
    (merge (f p)).symm (extension ⟨p, mem_univ p⟩ (merge p v))
  have hGzero (p : X) : G p 0 = 0 := by
    dsimp only [G, extension]
    rw [map_zero, hExtension.2.2.1 ⟨p, mem_univ p⟩, map_zero]
  have hGcontinuous : Continuous (fun z : Sigma (fun p ↦
      S.unstable.toDistribution p × S.stable.toDistribution p) ↦
      (⟨f z.1, G z.1 z.2⟩ : Sigma (fun p ↦
        S.unstable.toDistribution p × S.stable.toDistribution p))) := by
    have he := hExtension.1.comp
      (hmerge.subtype_mk (fun z ↦ mem_univ z.1))
    exact hsplitContinuous.comp he
  have hmergeDerivative (p : X)
      (v : S.unstable.toDistribution p × S.stable.toDistribution p) :
      merge (f p) (TU p v.1, TS p v.2) =
        mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) f p (merge p v) := by
    change mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) f p v.1.val +
      mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) f p v.2.val =
        mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) f p (v.1.val + v.2.val)
    exact (map_add _ _ _).symm
  have hGerror (p : X)
      (v w : S.unstable.toDistribution p × S.stable.toDistribution p) :
      ν (f p) (merge (f p)
        ((G p v - (TU p v.1, TS p v.2)) -
          (G p w - (TU p w.1, TS p w.2)))) ≤
        ε * ν p (merge p (v - w)) := by
    have he := hExtension.2.2.2.2.1 ⟨p, mem_univ p⟩ (merge p v) (merge p w)
    change ν (f p)
      ((extension ⟨p, mem_univ p⟩ (merge p v) -
        mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) f p (merge p v)) -
       (extension ⟨p, mem_univ p⟩ (merge p w) -
        mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) f p (merge p w))) ≤
          ε * ν p (merge p v - merge p w) at he
    simpa only [map_sub, hmergeDerivative, G,
      ContinuousLinearEquiv.apply_symm_apply] using he
  let η : NNReal := ⟨ε, hεpos.le⟩
  have hηsmall : (η : ℝ) < δgraph := hεgraph
  let splitGroups (p : X) : NormedAddCommGroup
      (S.unstable.toDistribution p × S.stable.toDistribution p) := by
    letI := groupsU p
    letI := groupsS p
    exact inferInstance
  let splitSpaces (p : X) : @NormedSpace ℝ
      (S.unstable.toDistribution p × S.stable.toDistribution p) _
      (splitGroups p).toSeminormedAddCommGroup := by
    letI := groupsU p
    letI := groupsS p
    letI : SeminormedAddCommGroup (S.unstable.toDistribution p) :=
      (groupsU p).toSeminormedAddCommGroup
    letI : SeminormedAddCommGroup (S.stable.toDistribution p) :=
      (groupsS p).toSeminormedAddCommGroup
    letI := spacesU p
    letI := spacesS p
    exact inferInstance
  have hGlipschitz (p : X) := @lipschitz_of_gauge_bound
    (S.unstable.toDistribution p × S.stable.toDistribution p)
    (S.unstable.toDistribution (f p) × S.stable.toDistribution (f p))
    (splitGroups p) (splitGroups (f p))
    (fun v ↦ ν p (merge p v)) (fun v ↦ ν (f p) (merge (f p) v))
    (by intro v; exact hνmerge p v)
    (by intro v; exact hνmerge (f p) v)
    (fun v ↦ G p v - (TU p v.1, TS p v.2)) η (hGerror p)
  have hExtensionDeriv (p : X) : HasFDerivAt
      (extension ⟨p, mem_univ p⟩)
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) f p) 0 := by
    exact hExtension.2.2.2.1 ⟨p, mem_univ p⟩
  have hGderiv (p : X) := @derivative_conjugate
    (S.unstable.toDistribution p × S.stable.toDistribution p)
    (S.unstable.toDistribution (f p) × S.stable.toDistribution (f p)) E
    (splitGroups p) (splitSpaces p) (splitGroups (f p)) (splitSpaces (f p)) _ _
    (merge p) (merge (f p)) (extension ⟨p, mem_univ p⟩)
    (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) f p)
    ((TU p).toContinuousLinearMap.prodMap (TS p)) (hmergeDerivative p) (hExtensionDeriv p)
  have hGreg (r : ℕ) := @nativeJointFiberContDiff E _ _ _ X _ _ _ _
    (fun p ↦ S.unstable.toDistribution p × S.stable.toDistribution p)
    splitGroups splitSpaces _ atlas.total f f.continuous merge hmerge hsplitContinuous
    (fun p ↦ extension ⟨p, mem_univ p⟩) hExtension.2.1 r
  obtain ⟨unstableGraph, stableGraph, hGraphCentered, hUnstableInvariant,
    hStableInvariant, hUnstableC1, hStableC1, hGraphTangent,
    hUnstableCharacterization, hStableCharacterization⟩ :=
      hgraph G (hGreg 1) hGzero (fun p ↦ (hGderiv p).fderiv)
        ⟨η, hηsmall, hGlipschitz⟩
  have hStableNorm := fun p ↦ @stable_graph_image_norm
    (S.unstable.toDistribution p) (S.stable.toDistribution p)
    (S.unstable.toDistribution (f p)) (S.stable.toDistribution (f p))
    (groupsU p) (spacesU p) (groupsS p) (spacesS p)
    (groupsU (f p)) (spacesU (f p)) (groupsS (f p)) (spacesS (f p))
    (TU p).toContinuousLinearMap (TS p) (G p) (stableGraph p) (stableGraph (f p))
    (hGraphCentered p).2.2.2 (hGraphCentered p).2.1
    (hGraphCentered (f p)).2.2.2 (hGraphCentered (f p)).2.1
    (fun y ↦ by
      have hy : G p (stableGraph p y, y) ∈
          Set.range (fun v ↦ (stableGraph (f p) v, v)) := by
        change (stableGraph p y, y) ∈ G p ⁻¹'
          Set.range (fun v ↦ (stableGraph (f.toHomeomorph p) v, v))
        rw [hStableInvariant p]
        exact ⟨y, rfl⟩
      obtain ⟨v, hv⟩ := hy
      rw [← hv])
    (hGzero p) η (hGlipschitz p) θ (hTSbound p)
  have hθeps : θ * (η : ℝ) < 1 := by
    change θ * ε < 1
    have he : ε < 1 := by linarith [hεrate, hθ]
    nlinarith [hθ1]
  have hStableGauge (p : X) (y : S.stable.toDistribution p) :
      ν p (merge p (stableGraph p y, y)) = ν p y.val := by
    rw [hνmerge]
    exact @graph_norm (S.unstable.toDistribution p) (S.stable.toDistribution p)
      (groupsU p) (groupsS p) (stableGraph p)
      (hGraphCentered p).2.2.2 (hGraphCentered p).2.1 y
  obtain ⟨localLog, ρLog, logDomain, hρLog, hLogDiagonal, hLogInverse, hLogImage, hLogDomain, hLogSmooth, hLocalLog⟩ :=
    uniform_exponential_logarithm_small gMetric ν hνcontinuous hνzero
  let exponentialChart (p : X) := exponential_fibre_chart gMetric p ρLog logDomain
    (localLog p) (hLogInverse p) (hLogImage p) (hLogDomain p) (hLogSmooth p)
  let plaqueRadius := min b (hm * min ρexp ρLog) / 2
  have hPlaqueRadius : 0 < plaqueRadius :=
    half_pos (lt_min hb (mul_pos hmpos (lt_min hρexp hρLog)))
  have hPlaqueAgreement : plaqueRadius ≤ b :=
    (half_le_self (le_of_lt (lt_min hb (mul_pos hmpos (lt_min hρexp hρLog))))).trans (min_le_left _ _)
  have hPlaqueInjective : plaqueRadius < hm * ρexp :=
    (half_lt_self (lt_min hb (mul_pos hmpos (lt_min hρexp hρLog)))).trans_le
      ((min_le_right _ _).trans (mul_le_mul_of_nonneg_left (min_le_left _ _) hmpos.le))
  have hPlaqueLogRadius : plaqueRadius < hm * ρLog :=
    (half_lt_self (lt_min hb (mul_pos hmpos (lt_min hρexp hρLog)))).trans_le
      ((min_le_right _ _).trans (mul_le_mul_of_nonneg_left (min_le_right _ _) hmpos.le))
  have hSmallMetric (p : X) (v : TangentSpace 𝓘(ℝ, E) p)
      (hv : ν p v < plaqueRadius) : ExponentialLift.metricNorm gMetric p v < ρexp := by
    have hmν := hνlowerMetric ⟨p, mem_univ p⟩ v
    change hm * ExponentialLift.metricNorm gMetric p v ≤ ν p v at hmν
    exact (mul_lt_mul_iff_right₀ hmpos).mp (hmν.trans_lt (hv.trans hPlaqueInjective))
  have hSmallLogMetric (p : X) (v : TangentSpace 𝓘(ℝ, E) p)
      (hv : ν p v < plaqueRadius) : ExponentialLift.metricNorm gMetric p v < ρLog := by
    have hmν := hνlowerMetric ⟨p, mem_univ p⟩ v
    change hm * ExponentialLift.metricNorm gMetric p v ≤ ν p v at hmν
    exact (mul_lt_mul_iff_right₀ hmpos).mp (hmν.trans_lt (hv.trans hPlaqueLogRadius))
  let stablePlaque (p : X) (y : S.stable.toDistribution p) :=
    ExponentialLift.riemannianExp gMetric p (merge p (stableGraph p y, y))
  have hStablePlaqueZero (p : X) : stablePlaque p 0 = p := by
    simp only [stablePlaque, (hGraphCentered p).2.1, ← Prod.zero_eq_mk, map_zero]
    exact (riemannianExponential_zero gMetric p).2
  have hStablePlaqueInjective (p : X) :
      Set.InjOn (stablePlaque p) {y | ν p y.val < plaqueRadius} := by
    intro y hy z hz heq
    have hylog := (hExpInjective p (mem_univ p) (merge p (stableGraph p y, y))
      (hSmallMetric p _ ((hStableGauge p y).symm ▸ hy))).2
    have hzlog := (hExpInjective p (mem_univ p) (merge p (stableGraph p z, z))
      (hSmallMetric p _ ((hStableGauge p z).symm ▸ hz))).2
    have he := congrArg (logExp p) heq
    change logExp p (ExponentialLift.riemannianExp gMetric p _) =
      logExp p (ExponentialLift.riemannianExp gMetric p _) at he
    rw [hylog, hzlog] at he
    exact congrArg Prod.snd ((merge p).injective he)
  have hStableTrap (p : X) (y : S.stable.toDistribution p)
      (hy : ν p y.val < plaqueRadius) :
      ∃ y' : S.stable.toDistribution (f p),
        ν (f p) y'.val ≤ (θ + ε) * ν p y.val ∧
        ν (f p) y'.val < plaqueRadius ∧
        f (stablePlaque p y) = stablePlaque (f p) y' := by
    have hygraph : G p (stableGraph p y, y) ∈
        Set.range (fun v ↦ (stableGraph (f.toHomeomorph p) v, v)) := by
      change (stableGraph p y, y) ∈ G p ⁻¹'
        Set.range (fun v ↦ (stableGraph (f.toHomeomorph p) v, v))
      rw [hStableInvariant p]
      exact ⟨y, rfl⟩
    obtain ⟨y', hy'⟩ := hygraph
    have hnorm := hStableNorm p y
    have hgauge : ν (f p) y'.val ≤ (θ + ε) * ν p y.val := by
      rw [← hy'] at hnorm
      have hsrc := @graph_norm (S.unstable.toDistribution p) (S.stable.toDistribution p)
        (groupsU p) (groupsS p) (stableGraph p)
        (hGraphCentered p).2.2.2 (hGraphCentered p).2.1 y
      have htgt := @graph_norm (S.unstable.toDistribution (f p)) (S.stable.toDistribution (f p))
        (groupsU (f p)) (groupsS (f p)) (stableGraph (f p))
        (hGraphCentered (f p)).2.2.2 (hGraphCentered (f p)).2.1 y'
      change max (ν (f p) (stableGraph (f p) y').val) (ν (f p) y'.val) ≤
        (θ + ε) * max (ν p (stableGraph p y).val) (ν p y.val) at hnorm
      change max (ν p (stableGraph p y).val) (ν p y.val) = ν p y.val at hsrc
      change max (ν (f p) (stableGraph (f p) y').val) (ν (f p) y'.val) =
        ν (f p) y'.val at htgt
      rw [hsrc, htgt] at hnorm
      exact hnorm
    refine ⟨y', hgauge, ?_, ?_⟩
    · exact (hgauge.trans (mul_le_of_le_one_left (hνnonneg p y.val) hεrate.le)).trans_lt hy
    · have hAgree := (hAgreement ⟨p, mem_univ p⟩ (merge p (stableGraph p y, y))
        (by change ν p (merge p (stableGraph p y, y)) ≤ b
            rw [hStableGauge]
            exact hy.le.trans hPlaqueAgreement)).2.2.2.2
      have hmergeEq := congrArg (merge (f p)) hy'
      change merge (f p) (stableGraph (f p) y', y') =
        merge (f p) ((merge (f p)).symm (extension ⟨p, mem_univ p⟩
          (merge p (stableGraph p y, y)))) at hmergeEq
      rw [ContinuousLinearEquiv.apply_symm_apply] at hmergeEq
      change f (ExponentialLift.riemannianExp gMetric p (merge p (stableGraph p y, y))) =
        ExponentialLift.riemannianExp gMetric (f p) (merge (f p) (stableGraph (f p) y', y'))
      rw [hmergeEq]
      exact hAgree.symm
  let StableDisc := Sigma fun p : X ↦
    {y : S.stable.toDistribution p // ν p y.val < plaqueRadius}
  let stableStep (z : StableDisc) : StableDisc :=
    ⟨f z.1, ⟨(hStableTrap z.1 z.2.val z.2.property).choose,
      (hStableTrap z.1 z.2.val z.2.property).choose_spec.2.1⟩⟩
  have hStableUniform (ε' : ENNReal) (hε' : 0 < ε') :
      ∃ N : ℕ, ∀ n ≥ N, ∀ p : X, ∀ y : S.stable.toDistribution p,
        ν p y.val < plaqueRadius → edist ((f : X → X)^[n] p)
          ((f : X → X)^[n] (stablePlaque p y)) < ε' := by
    have hu := exponential_trapped_orbit_uniform gMetric
      (fun z : StableDisc ↦ z.1)
      (fun z ↦ merge z.1 (stableGraph z.1 z.2.val, z.2.val))
      (fun z ↦ ν z.1 z.2.val.val) stableStep f
      (fun _ ↦ rfl)
      (fun z ↦ (hStableTrap z.1 z.2.val z.2.property).choose_spec.2.2.symm)
      hm⁻¹ (θ + ε) (inv_pos.mpr hmpos) (add_nonneg hθ.le hεpos.le) hεrate
      (fun z ↦ show ExponentialLift.metricNorm gMetric z.1
        (merge z.1 (stableGraph z.1 z.2.val, z.2.val)) ≤ hm⁻¹ * ν z.1 z.2.val.val from by
        rw [inv_mul_eq_div]
        apply (le_div_iff₀ hmpos).mpr
        have hh := hνlowerMetric ⟨z.1, mem_univ z.1⟩
          (merge z.1 (stableGraph z.1 z.2.val, z.2.val))
        change hm * ExponentialLift.metricNorm gMetric z.1
          (merge z.1 (stableGraph z.1 z.2.val, z.2.val)) ≤
            ν z.1 (merge z.1 (stableGraph z.1 z.2.val, z.2.val)) at hh
        simpa only [hStableGauge, mul_comm] using hh) (fun z ↦ (hStableTrap z.1 z.2.val z.2.property).choose_spec.1)
      plaqueRadius ε' hε'
    obtain ⟨N, hN⟩ := hu
    exact ⟨N, fun n hn p y hy ↦ hN n hn (⟨p, ⟨y, hy⟩⟩ : StableDisc) hy.le⟩
  have hStableAsymptotic (p : X) (y : S.stable.toDistribution p)
      (hy : ν p y.val < plaqueRadius) :
      Tendsto (fun n ↦ edist ((f : X → X)^[n] p)
        ((f : X → X)^[n] (stablePlaque p y))) atTop (𝓝 0) := by
    apply ENNReal.tendsto_nhds_zero.mpr
    intro ε' hε'
    obtain ⟨N, hN⟩ := hStableUniform ε' hε'
    exact eventually_atTop.mpr ⟨N, fun n hn ↦ (hN n hn p y hy).le⟩
  have hStableGraphContinuous := @jointFiberContDiff_total_continuous X X _ _
    (fun p ↦ S.stable.toDistribution p) (fun p ↦ S.unstable.toDistribution p)
    groupsS spacesS groupsU spacesU _ _ atlas.second atlas.first id continuous_id
    1 stableGraph hStableC1
  have hUnstableGraphContinuous := @jointFiberContDiff_total_continuous X X _ _
    (fun p ↦ S.unstable.toDistribution p) (fun p ↦ S.stable.toDistribution p)
    groupsU spacesU groupsS spacesS _ _ atlas.first atlas.second id continuous_id
    1 unstableGraph hUnstableC1
  obtain ⟨hjetSmall, hjetDen1, hjetDen2, _, _, hjetContract, hjetSlope,
    hjetInverse, _, _, _, hjetStrongImage, hjetStrongPreimage, _⟩ :=
      hjetThreshold ε hεpos.le hεjet
  let θN : NNReal := ⟨θ, hθ.le⟩
  have hGraphsRegular (r : ℕ) (hr : 1 ≤ r) :
      JointFiberContDiff atlas.first atlas.second id r unstableGraph ∧
      JointFiberContDiff atlas.second atlas.first id r stableGraph := by
    have hh := parameter_graph_fixed_graph_regularity r hr 1 atlas f.toHomeomorph
      TU TS G (hGreg r) hGzero (fun p ↦ (hGderiv p).fderiv)
      θN θN η hTUbound hTSbound hjetSmall hjetContract hjetSlope.le hjetInverse
      (fun h ↦ (hjetStrongImage h).trans_le (min_le_left _ _))
      (fun h ↦ (hjetStrongPreimage h).trans_le (min_le_left _ _))
      hGlipschitz unstableGraph stableGraph
      (fun p ↦ ⟨(hGraphCentered p).1, (hGraphCentered p).2.2.1⟩)
      (fun p ↦ ⟨(hGraphCentered p).2.1, (hGraphCentered p).2.2.2⟩)
      hUnstableGraphContinuous hStableGraphContinuous hUnstableInvariant hStableInvariant
    exact ⟨hh.2.2.1 le_rfl, hh.2.2.2 le_rfl⟩
  have hStableGraphSmooth (p : X) : ContDiff ℝ ∞ (stableGraph p) := by
    apply contDiff_infty.mpr
    intro n
    exact ((hGraphsRegular (n + 1) (by omega)).2.1 p).of_le (by exact_mod_cast Nat.le_succ n)
  have hStablePairContinuous : Continuous (fun z : Sigma (fun p ↦ S.stable.toDistribution p) ↦
      (⟨z.1, (stableGraph z.1 z.2, z.2)⟩ : Sigma (fun p ↦
        S.unstable.toDistribution p × S.stable.toDistribution p))) :=
    continuous_induced_rng.mpr (hStableGraphContinuous.prodMk continuous_id)
  have hStablePlaqueContinuous : ContinuousOn
      (fun z : Sigma (fun p ↦ S.stable.toDistribution p) ↦ stablePlaque z.1 z.2)
      {z | ν z.1 z.2.val < plaqueRadius} := by
    exact (riemannian_exponential_local_addition gMetric).2.2.1.continuousOn.comp
      (hmerge.comp hStablePairContinuous).continuousOn (fun z hz ↦
        (hExpInjective z.1 (mem_univ z.1) _
          (hSmallMetric z.1 _ ((hStableGauge z.1 z.2).symm ▸ hz))).1)
  have hStablePlaqueC1 (p : X) :
      letI := groupsS p
      letI := spacesS p
      ContMDiffOn 𝓘(ℝ, S.stable.toDistribution p) 𝓘(ℝ, E) 1
        (stablePlaque p) {y | ν p y.val < plaqueRadius} := by
    let := groupsS p
    let := spacesS p
    let := groupsU p
    let := spacesU p
    have hψ : ContDiff ℝ 1 (fun y : S.stable.toDistribution p ↦
        merge p (stableGraph p y, y)) :=
      (merge p).contDiff.comp ((hStableC1.1 p).prodMk contDiff_id)
    exact exponential_fibreMap_contMDiffOn gMetric p _ 1 (by simp) hψ _
      (fun y hy ↦ (hExpInjective p (mem_univ p) _
        (hSmallMetric p _ ((hStableGauge p y).symm ▸ hy))).1)
  have hStablePlaqueSmooth (p : X) :
      letI := groupsS p
      letI := spacesS p
      ContMDiffOn 𝓘(ℝ, S.stable.toDistribution p) 𝓘(ℝ, E) ∞
        (stablePlaque p) {y | ν p y.val < plaqueRadius} := by
    let := groupsS p
    let := spacesS p
    let := groupsU p
    let := spacesU p
    have hψ : ContDiff ℝ ∞ (fun y : S.stable.toDistribution p ↦
        merge p (stableGraph p y, y)) :=
      (merge p).contDiff.comp ((hStableGraphSmooth p).prodMk contDiff_id)
    exact exponential_fibreMap_contMDiffOn gMetric p _ ∞ (by simp) hψ _
      (fun y hy ↦ (hExpInjective p (mem_univ p) _
        (hSmallMetric p _ ((hStableGauge p y).symm ▸ hy))).1)
  let stableCoordinate (p q : X) : S.stable.toDistribution p :=
    ((merge p).symm (localLog p q)).2
  let exponentialChartC1 (p : X) : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E X 1 :=
    { (exponentialChart p).toPartialEquiv with
      open_source := (exponentialChart p).open_source
      open_target := (exponentialChart p).open_target
      contMDiffOn_toFun := (exponentialChart p).contMDiffOn_toFun.of_le (by simp)
      contMDiffOn_invFun := (exponentialChart p).contMDiffOn_invFun.of_le (by simp) }
  let stableModel (p : X) :
      (S.stable.toDistribution p × S.unstable.toDistribution p) ≃L[ℝ] E :=
    ((ContinuousLinearEquiv.prodComm ℝ _ _).trans (merge p)).trans
      (tangentSpaceCastModel 𝓘(ℝ, E) p)
  have hStablePlaqueImmersion (p : X) (y : S.stable.toDistribution p)
      (hy : ν p y.val < plaqueRadius) :
      letI := groupsS p
      letI := spacesS p
      Manifold.IsImmersionAt 𝓘(ℝ, S.stable.toDistribution p) 𝓘(ℝ, E) 1 (stablePlaque p) y := by
    let := groupsS p
    let := spacesS p
    let := groupsU p
    let := spacesU p
    have hsource : stableModel p (y, stableGraph p y) ∈ (exponentialChartC1 p).source := by
      change ExponentialLift.metricNorm gMetric p
        ((tangentSpaceCastModel 𝓘(ℝ, E) p).symm
          ((tangentSpaceCastModel 𝓘(ℝ, E) p) (merge p (stableGraph p y, y)))) < ρLog
      rw [ContinuousLinearEquiv.symm_apply_apply]
      exact hSmallLogMetric p _ ((hStableGauge p y).symm ▸ hy)
    have hh := graph_param_immersion 1 (exponentialChartC1 p) (stableModel p)
      (stableGraph p) (hStableC1.1 p) y hsource
    convert hh using 1
    ext v
    change ExponentialLift.riemannianExp gMetric p (merge p (stableGraph p v, v)) =
      ExponentialLift.riemannianExp gMetric p
        ((tangentSpaceCastModel 𝓘(ℝ, E) p).symm
          ((tangentSpaceCastModel 𝓘(ℝ, E) p) (merge p (stableGraph p v, v))))
    rw [ContinuousLinearEquiv.symm_apply_apply]
  have hStableCoordinateSmooth (p : X) :
      letI := groupsS p
      letI := spacesS p
      ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, S.stable.toDistribution p) ∞
        (stableCoordinate p) {q | (p, q) ∈ logDomain} := by
    let := groupsS p
    let := spacesS p
    let C : E →L[ℝ] S.stable.toDistribution p :=
      (ContinuousLinearMap.snd ℝ _ _).comp ((merge p).symm.toContinuousLinearMap.comp
        (tangentSpaceCastModel 𝓘(ℝ, E) p).symm.toContinuousLinearMap)
    have hc := C.contDiff.contMDiff.comp_contMDiffOn (hLogSmooth p)
    convert hc using 1
    ext q
    simp only [C, stableCoordinate, ContinuousLinearMap.coe_comp,
      ContinuousLinearEquiv.coe_coe, Function.comp_def,
      ContinuousLinearEquiv.symm_apply_apply]
    rfl
  let unstableCoordinate (p q : X) : S.unstable.toDistribution p :=
    ((merge p).symm (localLog p q)).1
  have hUnstableCoordinateSmooth (p : X) :
      letI := groupsU p
      letI := spacesU p
      ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, S.unstable.toDistribution p) ∞
        (unstableCoordinate p) {q | (p, q) ∈ logDomain} := by
    let := groupsU p
    let := spacesU p
    let C : E →L[ℝ] S.unstable.toDistribution p :=
      (ContinuousLinearMap.fst ℝ _ _).comp ((merge p).symm.toContinuousLinearMap.comp
        (tangentSpaceCastModel 𝓘(ℝ, E) p).symm.toContinuousLinearMap)
    have hc := C.contDiff.contMDiff.comp_contMDiffOn (hLogSmooth p)
    convert hc using 1
    ext q
    simp only [C, unstableCoordinate, ContinuousLinearMap.coe_comp,
      ContinuousLinearEquiv.coe_coe, Function.comp_def,
      ContinuousLinearEquiv.symm_apply_apply]
    rfl
  have hStableCoordinateInverse (p : X) (y : S.stable.toDistribution p)
      (hy : ν p y.val < plaqueRadius) : stableCoordinate p (stablePlaque p y) = y := by
    change ((merge p).symm (localLog p (ExponentialLift.riemannianExp gMetric p
      (merge p (stableGraph p y, y))))).2 = y
    rw [(hLogInverse p _ (hSmallLogMetric p _ ((hStableGauge p y).symm ▸ hy))).2,
      ContinuousLinearEquiv.symm_apply_apply]
  have hStableDiscOpen (p : X) :
      IsOpen {y : S.stable.toDistribution p | ν p y.val < plaqueRadius} :=
    isOpen_lt (hnormS.comp (atlas.second.fibre_inducing p).continuous) continuous_const
  have hStablePlaqueDerivativeZero (p : X) (v : S.stable.toDistribution p) :
      letI := groupsS p
      letI := spacesS p
      mfderiv 𝓘(ℝ, S.stable.toDistribution p) 𝓘(ℝ, E) (stablePlaque p) 0 v = v.val := by
    let := groupsS p
    let := spacesS p
    let := groupsU p
    let := spacesU p
    have ht : HasFDerivAt (stableGraph p)
        (0 : S.stable.toDistribution p →L[ℝ] S.unstable.toDistribution p) 0 := by
      have hh := ((hStableC1.1 p).differentiable (by simp) 0).hasFDerivAt
      rwa [(hGraphTangent p).2] at hh
    have hp := ht.prodMk (hasFDerivAt_id (0 : S.stable.toDistribution p))
    let C := (tangentSpaceCastModel 𝓘(ℝ, E) p).toContinuousLinearMap.comp
      (merge p).toContinuousLinearMap
    have hc := C.hasFDerivAt.comp 0 hp
    have hh := exponential_fibreMap_mfderiv_zero gMetric p
      (fun y : S.stable.toDistribution p ↦ merge p (stableGraph p y, y))
      (by rw [(hGraphCentered p).2.1]; exact (merge p).map_zero) _ hc v
    apply hh.trans
    change (0 : TangentSpace 𝓘(ℝ, E) p) + v.val = v.val
    exact zero_add _
  have hStablePlaqueRestrictionContinuous (p : X) : Continuous
      (fun y : {y : S.stable.toDistribution p // ν p y.val < plaqueRadius} ↦
        stablePlaque p y.val) := by
    exact hStablePlaqueContinuous.comp_continuous
      ((atlas.second.fibre_inducing p).continuous.comp continuous_subtype_val) (fun y ↦ y.property)
  obtain ⟨_, _, stableCaptureRadius, hStableCaptureRadius, hStableCapture⟩ :=
    hStableCharacterization le_rfl
  obtain ⟨_, _, unstableCaptureRadius, hUnstableCaptureRadius, hUnstableCapture⟩ :=
    hUnstableCharacterization le_rfl
  let captureRadius := min plaqueRadius (min stableCaptureRadius unstableCaptureRadius) / 2
  have hCaptureRadius : 0 < captureRadius :=
    half_pos (lt_min hPlaqueRadius (lt_min hStableCaptureRadius hUnstableCaptureRadius))
  have hCapturePlaque : captureRadius < plaqueRadius :=
    (half_lt_self (lt_min hPlaqueRadius (lt_min hStableCaptureRadius hUnstableCaptureRadius))).trans_le (min_le_left _ _)
  have hCaptureGraph : captureRadius < stableCaptureRadius :=
    (half_lt_self (lt_min hPlaqueRadius (lt_min hStableCaptureRadius hUnstableCaptureRadius))).trans_le
      ((min_le_right _ _).trans (min_le_left _ _))
  obtain ⟨captureDistance, hCaptureDistance, hlogSmall⟩ := hLocalLog captureRadius hCaptureRadius
  let relativeCoordinates (z : X × X) : Sigma (fun p ↦
      S.unstable.toDistribution p × S.stable.toDistribution p) :=
    ⟨z.1, (merge z.1).symm (localLog z.1 z.2)⟩
  let splitDynamics (z : Sigma (fun p ↦
      S.unstable.toDistribution p × S.stable.toDistribution p)) : Sigma (fun p ↦
      S.unstable.toDistribution p × S.stable.toDistribution p) := ⟨f z.1, G z.1 z.2⟩
  have hRelativeStep (p q : X) (hpq : edist p q < captureDistance)
      (hfpq : edist (f p) (f q) < captureDistance) :
      splitDynamics (relativeCoordinates (p, q)) = relativeCoordinates (f p, f q) := by
    have hsmall := (hlogSmall p q hpq).1.trans hCapturePlaque
    have hnextsmall := (hlogSmall (f p) (f q) hfpq).1.trans hCapturePlaque
    have hAgree := (hAgreement ⟨p, mem_univ p⟩ (localLog p q)
      (show ν p (localLog p q) ≤ b from hsmall.le.trans hPlaqueAgreement)).2.2.2.1
    have hnextInv := (hExpInjective (f p) (mem_univ (f p))
      (localLog (f p) (f q)) (hSmallMetric (f p) _ hnextsmall)).2
    change extension ⟨p, mem_univ p⟩ (localLog p q) =
      logExp (f p) (f (ExponentialLift.riemannianExp gMetric p (localLog p q))) at hAgree
    rw [(hlogSmall p q hpq).2] at hAgree
    rw [(hlogSmall (f p) (f q) hfpq).2] at hnextInv
    dsimp only [splitDynamics, relativeCoordinates]
    apply congrArg (fun v : S.unstable.toDistribution (f p) × S.stable.toDistribution (f p) ↦
      (⟨f p, v⟩ : Sigma (fun p ↦ S.unstable.toDistribution p × S.stable.toDistribution p)))
    change (merge (f p)).symm (extension ⟨p, mem_univ p⟩
      (merge p ((merge p).symm (localLog p q)))) =
        (merge (f p)).symm (localLog (f p) (f q))
    rw [ContinuousLinearEquiv.apply_symm_apply, hAgree, hnextInv]
  have hStableLocalCapture (p q : X)
      (hpq : ∀ n : ℕ, edist ((f : X → X)^[n] p) ((f : X → X)^[n] q) < captureDistance) :
      ∃ y : S.stable.toDistribution p, ν p y.val < plaqueRadius ∧ stablePlaque p y = q := by
    let pairs (n : ℕ) := (((f : X → X)^[n] p), ((f : X → X)^[n] q))
    have hstep (n : ℕ) : splitDynamics (relativeCoordinates (pairs n)) =
        relativeCoordinates (pairs (n + 1)) := by
      have hn := hRelativeStep (pairs n).1 (pairs n).2 (hpq n)
        (by simpa only [pairs, Function.iterate_succ_apply'] using hpq (n + 1))
      simpa only [pairs, Function.iterate_succ_apply'] using hn
    have hiter (n : ℕ) : splitDynamics^[n] (relativeCoordinates (p, q)) =
        relativeCoordinates (pairs n) := by
      induction n with
      | zero => rfl
      | succ n ih => rw [Function.iterate_succ_apply', ih, hstep]
    have hnorm (n : ℕ) :
        ν (pairs n).1 (merge (pairs n).1 (relativeCoordinates (pairs n)).2) < captureRadius := by
      simpa only [relativeCoordinates, ContinuousLinearEquiv.apply_symm_apply] using
        (hlogSmall (pairs n).1 (pairs n).2 (hpq n)).1
    have hmem : (relativeCoordinates (p, q)).2 ∈ Set.range (fun y ↦ (stableGraph p y, y)) := by
      apply (hStableCapture p (relativeCoordinates (p, q)).2 ?_).mpr
      · refine ⟨?_, stableCaptureRadius, hStableCaptureRadius, ?_⟩
        · intro n
          change ‖(splitDynamics^[n] (relativeCoordinates (p, q))).2‖ < stableCaptureRadius
          rw [hiter]
          change max (ν (pairs n).1 (relativeCoordinates (pairs n)).2.1.val)
            (ν (pairs n).1 (relativeCoordinates (pairs n)).2.2.val) < stableCaptureRadius
          rw [← hνmerge]
          exact (hnorm n).trans hCaptureGraph
        · intro n
          change ‖(splitDynamics^[n] (relativeCoordinates (p, q))).2‖ ≤ stableCaptureRadius * 1 ^ n
          rw [hiter, one_pow, mul_one]
          change max (ν (pairs n).1 (relativeCoordinates (pairs n)).2.1.val)
            (ν (pairs n).1 (relativeCoordinates (pairs n)).2.2.val) ≤ stableCaptureRadius
          rw [← hνmerge]
          exact ((hnorm n).trans hCaptureGraph).le
      · change max (ν p (relativeCoordinates (p, q)).2.1.val)
          (ν p (relativeCoordinates (p, q)).2.2.val) < stableCaptureRadius
        rw [← hνmerge]
        exact (hnorm 0).trans hCaptureGraph
    obtain ⟨y, hy⟩ := hmem
    have hmergeEq := congrArg (merge p) hy
    change merge p (stableGraph p y, y) =
      merge p ((merge p).symm (localLog p q)) at hmergeEq
    rw [ContinuousLinearEquiv.apply_symm_apply] at hmergeEq
    refine ⟨y, ?_, ?_⟩
    · rw [← hStableGauge, hmergeEq]
      exact (hlogSmall p q (hpq 0)).1.trans hCapturePlaque
    · change ExponentialLift.riemannianExp gMetric p (merge p (stableGraph p y, y)) = q
      rw [hmergeEq]
      exact (hlogSmall p q (hpq 0)).2
  have hStableEventualCapture (p q : X)
      (hpq : Tendsto (fun n : ℕ ↦ edist ((f : X → X)^[n] p)
        ((f : X → X)^[n] q)) atTop (𝓝 0)) :
      ∃ N : ℕ, ∃ y : S.stable.toDistribution ((f : X → X)^[N] p),
        ν _ y.val < plaqueRadius ∧ stablePlaque _ y = (f : X → X)^[N] q := by
    obtain ⟨N, hN⟩ := asymptotic_eventually_close (f : X → X) p q
      captureDistance hCaptureDistance hpq
    exact ⟨N, hStableLocalCapture _ _ hN⟩
  have hStableAsymptoticIff (p q : X) :
      Tendsto (fun n : ℕ ↦ edist ((f : X → X)^[n] p)
        ((f : X → X)^[n] q)) atTop (𝓝 0) ↔
      ∃ N : ℕ, ∃ y : S.stable.toDistribution ((f : X → X)^[N] p),
        ν _ y.val < plaqueRadius ∧ stablePlaque _ y = (f : X → X)^[N] q := by
    constructor
    · exact hStableEventualCapture p q
    · rintro ⟨N, y, hy, heq⟩
      apply (orbitAsymptotic_shift (f : X → X) p q N).mp
      have ht := hStableAsymptotic ((f : X → X)^[N] p) y hy
      rw [heq] at ht
      exact ht
  let semiU (p : X) : SeminormedAddCommGroup (S.unstable.toDistribution p) :=
    (groupsU p).toSeminormedAddCommGroup
  let semiS (p : X) : SeminormedAddCommGroup (S.stable.toDistribution p) :=
    (groupsS p).toSeminormedAddCommGroup
  let fullLinear (p : X) :
      (S.unstable.toDistribution p × S.stable.toDistribution p) ≃L[ℝ]
        (S.unstable.toDistribution (f p) × S.stable.toDistribution (f p)) :=
    (TU p).prodCongr (rawTS p).toContinuousLinearEquiv
  have hFullMap (p : X) (v : S.unstable.toDistribution p × S.stable.toDistribution p) :
      merge (f p) (fullLinear p v) =
        mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) f p (merge p v) := hmergeDerivative p v
  have hFullInv (p : X) (v : S.unstable.toDistribution (f p) × S.stable.toDistribution (f p)) :
      merge p ((fullLinear p).symm v) =
        mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) f.symm (f p) (merge (f p) v) := by
    have hh := derivative_inverse_forward f p (merge p ((fullLinear p).symm v))
    rw [← hFullMap,ContinuousLinearEquiv.apply_symm_apply] at hh
    exact hh.symm
  have hFullInverseBound (p : X) : ‖(fullLinear p).symm.toContinuousLinearMap‖ ≤ inverseBound := by
    apply (fullLinear p).symm.toContinuousLinearMap.opNorm_le_bound hInverseBound.le
    intro v
    change max (ν p ((fullLinear p).symm v).1.val) (ν p ((fullLinear p).symm v).2.val) ≤
      inverseBound * max (ν (f p) v.1.val) (ν (f p) v.2.val)
    rw [← hνmerge,← hνmerge,hFullInv]
    let gauge : X → E → ℝ := fun x v ↦ ν x v
    change gauge p (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) f.symm (f p) (merge (f p) v)) ≤
      inverseBound * gauge (f p) (merge (f p) v)
    have hh : gauge (f.symm (f p))
        (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) f.symm (f p) (merge (f p) v)) ≤
        inverseBound * gauge (f p) (merge (f p) v) := hInverseGauge (f p) (merge (f p) v)
    simpa only [f.symm_apply_apply] using hh
  have hInverseMargin : inverseBound * ε < 1 := by
    have hb : ε ≤ 1 / (2 * inverseBound) := min_le_right _ _
    have hh := (le_div_iff₀ (by positivity : 0 < 2 * inverseBound)).mp hb
    nlinarith
  have hCutoffDiffeomorph (p : X) :
      ∃ D : Diffeomorph
        𝓘(ℝ,S.unstable.toDistribution p × S.stable.toDistribution p)
        𝓘(ℝ,S.unstable.toDistribution (f p) × S.stable.toDistribution (f p))
        (S.unstable.toDistribution p × S.stable.toDistribution p)
        (S.unstable.toDistribution (f p) × S.stable.toDistribution (f p)) ∞,
        (D : _ → _) = G p := by
    apply @diffeomorph_of_small_lipschitz_perturbation
      (S.unstable.toDistribution p × S.stable.toDistribution p)
      (S.unstable.toDistribution (f p) × S.stable.toDistribution (f p))
      (splitGroups p) (splitSpaces p) (parameter_graph_fibre_complete atlas.total p)
      (splitGroups (f p)) (splitSpaces (f p)) (fullLinear p) (G p)
    · apply contDiff_infty.mpr
      intro n
      exact (hGreg n).1 p
    · exact hGlipschitz p
    · exact (mul_le_mul_of_nonneg_right (hFullInverseBound p) hεpos.le).trans_lt hInverseMargin
  choose cutoff hCutoffEq using hCutoffDiffeomorph
  have hCutoffGraph (p : X) (y : S.stable.toDistribution p) :
      cutoff p (stableGraph p y,y) =
        (stableGraph (f p) (cutoff p (stableGraph p y,y)).2,
          (cutoff p (stableGraph p y,y)).2) := by
    rw [hCutoffEq]
    have hy : G p (stableGraph p y,y) ∈ Set.range (fun v ↦ (stableGraph (f p) v,v)) := by
      change (stableGraph p y,y) ∈ G p ⁻¹' Set.range (fun v ↦ (stableGraph (f p) v,v))
      exact (hStableInvariant p).symm ▸ Set.mem_range_self y
    obtain ⟨z,hz⟩ := hy
    rw [← hz]
  have hCutoffContract (p : X) (y : S.stable.toDistribution p) :
      ‖(cutoff p (stableGraph p y,y)).2‖ ≤ (θ + ε) * ‖y‖ := by
    have hb := hStableNorm p y
    have hsrc := @graph_norm (S.unstable.toDistribution p) (S.stable.toDistribution p)
      (groupsU p) (groupsS p) (stableGraph p)
      (hGraphCentered p).2.2.2 (hGraphCentered p).2.1 y
    rw [hsrc] at hb
    rw [hCutoffEq]
    exact (le_max_right _ _).trans hb
  have hPlaqueForward (p : X) (y : S.stable.toDistribution p)
      (hy : ν p y.val < plaqueRadius) :
      f (stablePlaque p y) = stablePlaque (f p) (cutoff p (stableGraph p y,y)).2 := by
    have hAgree := (hAgreement ⟨p,mem_univ p⟩ (merge p (stableGraph p y,y))
      (by change ν p (merge p (stableGraph p y,y)) ≤ b
          rw [hStableGauge]
          exact hy.le.trans hPlaqueAgreement)).2.2.2.2
    have he := congrArg (merge (f p)) (hCutoffGraph p y)
    rw [hCutoffEq] at he
    change merge (f p) ((merge (f p)).symm (extension ⟨p,mem_univ p⟩
      (merge p (stableGraph p y,y)))) = _ at he
    rw [ContinuousLinearEquiv.apply_symm_apply] at he
    change f (ExponentialLift.riemannianExp gMetric p (merge p (stableGraph p y,y))) = _
    rw [← hAgree]
    rw [hCutoffEq]
    exact congrArg (ExponentialLift.riemannianExp gMetric (f p)) he
  let A : StrongPlaqueGauge (E := E) X :=
    ⟨ν, hνnonneg, hνdef, hνadd, hνsmul, hνcontinuous⟩
  refine ⟨A, ⟨{
    radius := plaqueRadius
    radius_pos := hPlaqueRadius
    rate := θ + ε
    rate_pos := add_pos hθ hεpos
    rate_lt_one := hεrate
    graph := stableGraph
    graph_zero := fun p ↦ (hGraphCentered p).2.1
    graph_lipschitz := fun p ↦ (hGraphCentered p).2.2.2
    graph_smooth := hStableGraphSmooth
    graph_regular := fun r hr ↦ (hGraphsRegular r hr).2
    graph_gauge := hStableGauge
    merge_continuous := hmerge
    metric := gMetric
    cutoff := cutoff
    cutoff_graph := ?_
    cutoff_contract := ?_
    plaque := stablePlaque
    plaque_formula := fun p y ↦ rfl
    exponential_domain := fun p y hy ↦
      (hExpInjective p (mem_univ p) _ (hSmallMetric p _ ((hStableGauge p y).symm ▸ hy))).1
    exponential_chart := exponentialChart
    exponential_chart_apply := fun p v ↦ rfl
    exponential_chart_source := ?_
    plaque_zero := hStablePlaqueZero
    plaque_injective := hStablePlaqueInjective
    disc_open := hStableDiscOpen
    plaque_continuous := hStablePlaqueContinuous
    plaque_smooth := hStablePlaqueSmooth
    plaque_immersion := hStablePlaqueImmersion
    plaque_derivative_zero := hStablePlaqueDerivativeZero
    coordinate := stableCoordinate
    coordinate_domain := logDomain
    coordinate_domain_diagonal := fun p ↦ (hLogDiagonal p).1
    exponential_chart_target := fun p ↦ rfl
    coordinate_smooth := hStableCoordinateSmooth
    coordinate_inverse := hStableCoordinateInverse
    coordinate_domain_plaque := ?_
    plaque_forward := hPlaqueForward
    uniform_asymptotic := hStableUniform
    capture_distance := captureDistance
    capture_distance_pos := hCaptureDistance
    local_capture := hStableLocalCapture
    asymptotic_iff := hStableAsymptoticIff
  }⟩⟩
  · intro p
    change (cutoff p : _ → _) ⁻¹' _ = _
    rw [hCutoffEq]
    exact hStableInvariant p
  · exact hCutoffContract
  · intro p y hy
    change ExponentialLift.metricNorm gMetric p
      ((tangentSpaceCastModel 𝓘(ℝ,E) p).symm
        ((tangentSpaceCastModel 𝓘(ℝ,E) p) (merge p (stableGraph p y,y)))) < ρLog
    rw [ContinuousLinearEquiv.symm_apply_apply]
    exact hSmallLogMetric p _ ((hStableGauge p y).symm ▸ hy)
  · intro p y hy
    exact (hLogInverse p _ (hSmallLogMetric p _ ((hStableGauge p y).symm ▸ hy))).1

end HolomorphicAnosov.HPS

