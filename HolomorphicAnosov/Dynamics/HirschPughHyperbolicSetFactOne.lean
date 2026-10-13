import HolomorphicAnosov.Geometry.NativeTransverseGraphIntersectionG9
import HolomorphicAnosov.Geometry.RadialGaussLengthG9
import HolomorphicAnosov.Dynamics.BoundedSectionGraphFibrewiseG9
import HolomorphicAnosov.Dynamics.ClosedOrbitPlaqueAssemblyG9
import HolomorphicAnosov.Analysis.BoundedSectionReindex
import HolomorphicAnosov.Dynamics.HirschPughFactOneData
import HolomorphicAnosov.Dynamics.HirschPughRestrictedSplitting
import HolomorphicAnosov.Dynamics.HirschPughSectionTransport
import HolomorphicAnosov.Dynamics.HirschPughUnstableSectionEquiv
import HolomorphicAnosov.Dynamics.HirschPughNonlinearLift
import HolomorphicAnosov.Geometry.BoundedTangentSuperposition
import HolomorphicAnosov.Dynamics.HirschPughSmoothAdaptedMetric
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.ExistsComponentwiseLengthMetric
import HolomorphicAnosov.Geometry.Riemannian.PiecewiseSmoothRiemannianEDist
import HolomorphicAnosov.Geometry.Riemannian.RiemannianEDistEqPiecewiseSmooth
import HolomorphicAnosov.Geometry.Riemannian.GallierQuaintanceGaussLemma
import HolomorphicAnosov.Geometry.UniformExponentialLift
import HolomorphicAnosov.Paper.HPS.LocalStrongGraphs

/-!
# Original-map hyperbolic-set Fact 1

This module formalizes `dynamics.hirsch_pugh_hyperbolic_set_fact1_g9`.
The continuous invariant splitting is defined only over the original compact set.
The hyperbolicity estimates use the derivative of the original map's actual iterates
and an actual smooth Riemannian tensor. Plaques are the literal closed orbit sets.

Sources: Hirsch–Pugh (1969), Theorem 3.1, p.148; Shub, *Global Stability of Dynamical
Systems* (1987), Proposition 4.2, pp.21–22, Definition 6.1 and Theorem 6.2, pp.71–72,
Lemma 6.5 and its application, pp.75–78; Bowen, *Markov Partitions for Axiom A
Diffeomorphisms*, Fact 1, pp.726–727. The full composite proof below records the
additional tensor-extension, smoothing, length-distance and equal-radius arguments.
Neither transitivity nor an ambient extension of the invariant splitting is assumed.
-/


namespace HolomorphicAnosov

open Set
open scoped ContDiff Manifold _root_.Topology Bundle

noncomputable section

set_option maxHeartbeats 1200000

universe u v

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {M : Type v} [TopologicalSpace M] [ChartedSpace E M]
variable [IsManifold 𝓘(ℝ, E) ∞ M]

private theorem graph_orbit_retained_g9
    {U S : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
    [NormedAddCommGroup S] [NormedSpace ℝ S]
    (boxMap : U × S → U × S) (Ψ : S → U)
    (hΨmem : ∀ s ∈ Metric.ball (0 : S) (1 / 4), (Ψ s, s) ∈ Metric.ball 0 (1 / 4))
    (hΨinv : ∀ s ∈ Metric.ball (0 : S) (1 / 4),
      boxMap (Ψ s, s) ∈ Metric.ball 0 (1 / 4) ∧
        (boxMap (Ψ s, s)).1 = Ψ (boxMap (Ψ s, s)).2)
    (s : S) (hs : ‖s‖ < 1 / 4) (n : ℕ) :
    ‖boxMap^[n] (Ψ s, s)‖ < 1 / 4 ∧
      (boxMap^[n] (Ψ s, s)).1 = Ψ (boxMap^[n] (Ψ s, s)).2 := by
  induction n with
  | zero => exact ⟨by simpa using hΨmem s (by simpa using hs), rfl⟩
  | succ n ih =>
    have hsm : (boxMap^[n] (Ψ s, s)).2 ∈ Metric.ball (0 : S) (1 / 4) := by
      simpa using (norm_snd_le _).trans_lt ih.1
    have hh := hΨinv _ hsm
    have heq : (Ψ (boxMap^[n] (Ψ s, s)).2, (boxMap^[n] (Ψ s, s)).2) =
        boxMap^[n] (Ψ s, s) := by rw [← ih.2]
    rw [heq] at hh
    simpa only [Function.iterate_succ_apply', Metric.mem_ball, dist_zero_right] using hh

private theorem invariant_graph_derivative_zero_g9
    {U S : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
    [NormedAddCommGroup S] [NormedSpace ℝ S]
    (TUnstable : U ≃L[ℝ] U) (TStable : S →L[ℝ] S)
    (hUnstableInverseContraction : ‖TUnstable.symm.toContinuousLinearMap‖ < 1)
    (hStableContraction : ‖TStable‖ < 1)
    (boxMap : U × S → U × S) (hBoxZero : boxMap 0 = 0)
    (hBoxDeriv : HasFDerivAt boxMap (TUnstable.toContinuousLinearMap.prodMap TStable) 0)
    (Ψ : S → U) (hΨzero : Ψ 0 = 0)
    (hΨderiv : HasFDerivAt Ψ (fderiv ℝ Ψ 0) 0)
    (hΨinv : ∀ s ∈ Metric.ball (0 : S) (1 / 4),
      boxMap (Ψ s, s) ∈ Metric.ball 0 (1 / 4) ∧
        (boxMap (Ψ s, s)).1 = Ψ (boxMap (Ψ s, s)).2) : fderiv ℝ Ψ 0 = 0 := by
  let D := fderiv ℝ Ψ 0
  have hpair := hΨderiv.prodMk (hasFDerivAt_id (0 : S))
  have hg : HasFDerivAt boxMap (TUnstable.toContinuousLinearMap.prodMap TStable)
      (Ψ 0, 0) := by simpa only [hΨzero, Prod.zero_eq_mk] using hBoxDeriv
  have hcomp := hg.comp (f := fun s : S ↦ (Ψ s, s)) 0 hpair
  have hd' : HasFDerivAt Ψ (fderiv ℝ Ψ 0) (boxMap (Ψ 0, 0)).2 := by
    simpa only [hΨzero, show ((0 : U), (0 : S)) = 0 from rfl,
      hBoxZero, Prod.snd_zero] using hΨderiv
  have hright := hd'.comp 0 hcomp.snd
  have heq : (fun s : S ↦ (boxMap (Ψ s, s)).1) =ᶠ[𝓝 0]
      (fun s : S ↦ Ψ (boxMap (Ψ s, s)).2) := by
    filter_upwards [Metric.ball_mem_nhds (0 : S)
      (by norm_num : (0 : ℝ) < 1 / 4)] with s hs
    exact (hΨinv s hs).2
  have hlinear : TUnstable.toContinuousLinearMap.comp D = D.comp TStable := by
    have hh := hcomp.fst.unique (hright.congr_of_eventuallyEq heq)
    convert hh using 1 <;> apply ContinuousLinearMap.ext <;> intro s <;> rfl
  have hfixed : D = TUnstable.symm.toContinuousLinearMap.comp (D.comp TStable) := by
    apply ContinuousLinearMap.ext
    intro s
    have hh := congrArg TUnstable.symm (DFunLike.congr_fun hlinear s)
    simpa using hh
  have hbound : ‖D‖ ≤ ‖TUnstable.symm.toContinuousLinearMap‖ * ‖D‖ * ‖TStable‖ := by
    calc
      ‖D‖ = ‖TUnstable.symm.toContinuousLinearMap.comp (D.comp TStable)‖ := congrArg norm hfixed
      _ ≤ ‖TUnstable.symm.toContinuousLinearMap‖ * ‖D.comp TStable‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ ‖TUnstable.symm.toContinuousLinearMap‖ * (‖D‖ * ‖TStable‖) :=
        mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg TUnstable.symm.toContinuousLinearMap)
      _ = _ := by ring
  have hgap : ‖TUnstable.symm.toContinuousLinearMap‖ * ‖TStable‖ < 1 := by
    have hnonnegT := norm_nonneg TUnstable.symm.toContinuousLinearMap
    calc
      _ ≤ 1 * ‖TStable‖ := mul_le_mul_of_nonneg_right hUnstableInverseContraction.le (norm_nonneg TStable)
      _ < 1 := by simpa only [one_mul] using hStableContraction
  change D = 0
  apply (norm_eq_zero (a := D)).mp
  have hnonneg := norm_nonneg D
  nlinarith only [hbound, hgap, hnonneg]

/-- Iterate actual graph invariance on its retained source domain. The chosen
receiving parameters remain in the same ball, so the metric estimate iterates. -/
private theorem native_graph_orbit_metric_g9
    {X P : Type*} [PseudoMetricSpace X] {V : P → Type*}
    [∀ p, SeminormedAddCommGroup (V p)]
    (f : X → X) (σ : P → P) (center : P → X)
    (hcenter : ∀ p, center (σ p) = f (center p))
    (b : (p : P) → V p → X) (κ r : ℝ) (hκ : 0 ≤ κ)
    (hstep : ∀ p, ∀ s : V p, ‖s‖ < r → ∃ t : V (σ p), ‖t‖ < r ∧
      dist (b (σ p) t) (center (σ p)) ≤ κ * dist (b p s) (center p) ∧
      f (b p s) = b (σ p) t)
    (p : P) (s : V p) (hs : ‖s‖ < r) (n : ℕ) :
    dist (f^[n] (b p s)) (f^[n] (center p)) ≤ κ ^ n * dist (b p s) (center p) := by
  classical
  let Ω := (p : P) × {s : V p // ‖s‖ < r}
  let next : Ω → Ω := fun z ↦ ⟨σ z.1, ⟨(hstep z.1 z.2.val z.2.property).choose,
    (hstep z.1 z.2.val z.2.property).choose_spec.1⟩⟩
  have hnext (z : Ω) :
      dist (b (next z).1 (next z).2.val) (center (next z).1) ≤
        κ * dist (b z.1 z.2.val) (center z.1) ∧
      f (b z.1 z.2.val) = b (next z).1 (next z).2.val :=
    (hstep z.1 z.2.val z.2.property).choose_spec.2
  let z : ℕ → Ω := fun m ↦ next^[m] ⟨p, ⟨s, hs⟩⟩
  have hz (m : ℕ) : z (m + 1) = next (z m) := Function.iterate_succ_apply' _ _ _
  have hbase (m : ℕ) : center (z m).1 = f^[m] (center p) := by
    induction m with
    | zero => rfl
    | succ m ih =>
      rw [hz, Function.iterate_succ_apply']
      exact (hcenter (z m).1).trans (congrArg f ih)
  have hpoint (m : ℕ) : b (z m).1 (z m).2.val = f^[m] (b p s) := by
    induction m with
    | zero => rfl
    | succ m ih =>
      rw [hz, Function.iterate_succ_apply']
      exact (hnext (z m)).2.symm.trans (congrArg f ih)
  have hdist (m : ℕ) : dist (b (z m).1 (z m).2.val) (center (z m).1) ≤
      κ ^ m * dist (b p s) (center p) := by
    induction m with
    | zero => simp only [z, Function.iterate_zero, id_eq, pow_zero, one_mul, le_refl]
    | succ m ih =>
      rw [hz, pow_succ']
      exact (hnext (z m)).1.trans ((mul_le_mul_of_nonneg_left ih hκ).trans_eq (mul_assoc _ _ _).symm)
  simpa only [hbase, hpoint] using hdist n

/-- The inverse derivative carries each invariant subspace back to its original
fibre, by the chain rule and equality of the forward image subspace. -/
private theorem reverse_subbundle_invariant_g9
    (f : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞) (Λ : Set M)
    (hf : MapsTo f Λ Λ) (hb : MapsTo f.symm Λ Λ)
    (S : ContinuousTangentSubbundleOn (E := E) Λ)
    (hinv : ∀ x : Λ, (S.fibre x).map (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) f x.val).toLinearMap =
      S.fibre ⟨f x.val, hf x.property⟩) :
    ∀ x : Λ, (S.fibre x).map (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) f.symm x.val).toLinearMap =
      S.fibre ⟨f.symm x.val, hb x.property⟩ := by
  have hback (q : Λ) :
      (S.fibre ⟨f q.val, hf q.property⟩).map
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) f.symm (f q.val)).toLinearMap = S.fibre q := by
    rw [← hinv q, ← _root_.Submodule.map_comp]
    have hchain := mfderiv_comp q.val
      (f.symm.contMDiff.mdifferentiableAt (by simp))
      (f.contMDiff.mdifferentiableAt (by simp))
    have hid : (f.symm : M → M) ∘ f = id := by funext x; exact f.symm_apply_apply x
    rw [hid, mfderiv_id] at hchain
    have heq : (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) f.symm (f q.val)).toLinearMap.comp
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) f q.val).toLinearMap = LinearMap.id := by
      exact congrArg ContinuousLinearMap.toLinearMap hchain.symm
    ext v
    rw [_root_.Submodule.mem_map]
    constructor
    · rintro ⟨w, hw, hwv⟩
      have hew := DFunLike.congr_fun heq w
      exact (hew.symm.trans hwv) ▸ hw
    · intro hv
      exact ⟨v, hv, DFunLike.congr_fun heq v⟩
  intro x
  have hh := hback ⟨f.symm x.val, hb x.property⟩
  have he : (⟨f (f.symm x.val), hf (hb x.property)⟩ : Λ) = x :=
    Subtype.ext (f.apply_symm_apply x.val)
  change (S.fibre ⟨f (f.symm x.val), hf (hb x.property)⟩).map
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) f.symm (f (f.symm x.val))).toLinearMap = _ at hh
  rw [he, f.apply_symm_apply] at hh
  exact hh

private theorem reverse_locally_maximal_g9
    (f : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞) (Λ : Set M)
    (H : HyperbolicSetFactOneDatum f Λ) (x : M) :
    x ∈ Λ ↔ ∀ n : ℤ, hyperbolicIntegerOrbit f.symm n x ∈ H.isolatingNeighborhood := by
  rw [H.locally_maximal]
  have heq (n : ℤ) : hyperbolicIntegerOrbit f.symm n x = hyperbolicIntegerOrbit f (-n) x := by
    unfold hyperbolicIntegerOrbit
    change ((f.toHomeomorph)⁻¹ ^ n) x = (f.toHomeomorph ^ (-n)) x
    rw [inv_zpow, zpow_neg]
  simp only [heq]
  exact Equiv.neg ℤ |>.surjective.forall

private def reverse_hyperbolic_datum_g9
    (f : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞) (Λ : Set M)
    (H : HyperbolicSetFactOneDatum f Λ) : HyperbolicSetFactOneDatum f.symm Λ where
  nonempty := H.nonempty
  compact := H.compact
  forward_mem := H.backward_mem
  backward_mem := H.forward_mem
  originalMetric := H.originalMetric
  stable := H.unstable
  unstable := H.stable
  complementary := fun x ↦ (H.complementary x).symm
  stable_invariant := reverse_subbundle_invariant_g9 f Λ H.forward_mem H.backward_mem H.unstable H.unstable_invariant
  unstable_invariant := reverse_subbundle_invariant_g9 f Λ H.forward_mem H.backward_mem H.stable H.stable_invariant
  C := H.C
  one_le_C := H.one_le_C
  rate := H.rate
  rate_pos := H.rate_pos
  rate_lt_one := H.rate_lt_one
  stable_estimate := H.unstable_estimate
  unstable_estimate := H.stable_estimate
  isolatingNeighborhood := H.isolatingNeighborhood
  isolating_open := H.isolating_open
  subset_isolating := H.subset_isolating
  locally_maximal := reverse_locally_maximal_g9 f Λ H

/-- The native stable graph construction, retaining its small original domains,
actual exponential invariance, and capture of ambient close forward orbits.
This is the stable half of Shub Lemma 6.5 and Theorem 6.2, pp.75–78. -/
private theorem native_stable_graph_data_g9
    [FiniteDimensional ℝ E] [T2Space M] [CompactSpace M]
    (f : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞) (Λ : Set M)
    (H : HyperbolicSetFactOneDatum f Λ)
    (hAdapt : Bundle.ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E
      (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x))
    (aAdapt : ℝ) (haAdapt : aAdapt < 1)
    (hsAdapt : ∀ (x : Λ) (v : TangentSpace 𝓘(ℝ, E) x.val), v ∈ H.stable.fibre x →
      hyperbolicRiemannianNorm hAdapt (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) f x.val v) ≤
        aAdapt * hyperbolicRiemannianNorm hAdapt v)
    (huAdapt : ∀ (x : Λ) (v : TangentSpace 𝓘(ℝ, E) x.val), v ∈ H.unstable.fibre x →
      hyperbolicRiemannianNorm hAdapt (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) f.symm x.val v) ≤
        aAdapt * hyperbolicRiemannianNorm hAdapt v)
    (dAdapt : MetricSpace M)
    (hdTop : dAdapt.toUniformSpace.toTopologicalSpace = (inferInstance : TopologicalSpace M))
    (hdComp : letI : Bundle.RiemannianBundle (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x) :=
      ⟨hAdapt.toRiemannianMetric⟩
      ∀ x y : M, y ∈ connectedComponent x →
        @edist M dAdapt.toPseudoMetricSpace.toPseudoEMetricSpace.toEDist x y =
          Manifold.riemannianEDist 𝓘(ℝ, E) x y) :
    letI : Bundle.RiemannianBundle (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x) :=
      ⟨hAdapt.toRiemannianMetric⟩
    ∃ μ : (p : Λ) → H.stable.fibre p → H.unstable.fibre p,
      (∀ p, μ p 0 = 0) ∧
      (∀ η : NNReal, 0 < η → ∃ r : ℝ, 0 < r ∧ r ≤ 1 / 4 ∧
        ∀ p : Λ, LipschitzOnWith η (μ p) (Metric.ball 0 r)) ∧
      (∃ κ r : ℝ, 0 < κ ∧ κ < 1 ∧ 0 < r ∧ r ≤ 1 / 4 ∧
        ∀ p : Λ, ∀ s : H.stable.fibre p, ‖s‖ < r →
          dAdapt.dist p.val (riemannianExponential hAdapt ⟨p.val, s.val + (μ p s).val⟩) =
            ‖s.val + (μ p s).val‖ ∧
          ∀ n : ℕ, dAdapt.dist ((f : M → M)^[n]
              (riemannianExponential hAdapt ⟨p.val, s.val + (μ p s).val⟩))
              ((f : M → M)^[n] p.val) ≤ κ ^ n *
            dAdapt.dist (riemannianExponential hAdapt ⟨p.val, s.val + (μ p s).val⟩) p.val) ∧
      (∀ r₀ : ℝ, 0 < r₀ → ∃ κ ε : ℝ, 0 < κ ∧ κ < 1 ∧ 0 < ε ∧
        ∀ x, ∀ hx : x ∈ Λ, ∀ y : M,
          (∀ n : ℕ, dAdapt.dist ((f : M → M)^[n] y) ((f : M → M)^[n] x) < ε) →
          ∃ s : H.stable.fibre ⟨x, hx⟩, ‖s‖ < r₀ ∧
            riemannianExponential hAdapt ⟨x, s.val + (μ ⟨x, hx⟩ s).val⟩ = y ∧
            dAdapt.dist (f y) (f x) ≤ κ * dAdapt.dist y x) := by
  classical
  let : Bundle.RiemannianBundle (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x) :=
    ⟨hAdapt.toRiemannianMetric⟩
  let : (x : M) → NormedAddCommGroup (TangentSpace 𝓘(ℝ, E) x) := fun x ↦ inferInstance
  let : (x : M) → InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, E) x) := fun x ↦ inferInstance
  -- Shub pp.72–74: the given Λ-local splitting induces the actual Banach
  -- product coordinates on all bounded sections, with no ambient extension.
  let B : Type _ := lp (fun x : Λ ↦ TangentSpace 𝓘(ℝ, E) (x : M)) ⊤
  let : NormedAddCommGroup B := inferInstance
  let : NormedSpace ℝ B := inferInstance
  let StableSections : Submodule ℝ B := HirschRestrictedCoordinates.boundedSectionSubmodule H.stable.fibre
  let UnstableSections : Submodule ℝ B := HirschRestrictedCoordinates.boundedSectionSubmodule H.unstable.fibre
  let : NormedAddCommGroup StableSections := inferInstance
  let : NormedSpace ℝ StableSections := inferInstance
  let : NormedAddCommGroup UnstableSections := inferInstance
  let : NormedSpace ℝ UnstableSections := inferInstance
  have hsectionSplit : Submodule.IsTopCompl StableSections UnstableSections :=
    HirschRestrictedCoordinates.bounded_sections_split H.compact
      H.stable H.unstable H.complementary hAdapt
  have hStableClosed : IsClosed (StableSections : Set B) := hsectionSplit.isClosed
  have hUnstableClosed : IsClosed (UnstableSections : Set B) := hsectionSplit.isClosed'
  have : CompleteSpace StableSections := hStableClosed.completeSpace_coe
  have : CompleteSpace UnstableSections := hUnstableClosed.completeSpace_coe
  let sectionCoordinates :=
    UnstableSections.prodEquivOfIsTopCompl StableSections hsectionSplit.symm
  -- The actual original derivative blocks satisfy the graph theorem's strict
  -- contraction bounds. max(aAdapt, 0) also covers zero-rank factors.
  let aBlock := max aAdapt 0
  have haBlock : 0 ≤ aBlock := le_max_right _ _
  have haBlockOne : aBlock < 1 := max_lt haAdapt zero_lt_one
  obtain ⟨TStable, hTStable, hnTStable⟩ :=
    HirschRestrictedCoordinates.exists_stable_derivative_section_transport f Λ H hAdapt
      aBlock haBlock (fun x v hv ↦ (hsAdapt x v hv).trans
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.sqrt_nonneg _)))
  obtain ⟨TUnstable, hTUnstable, hnTUnstableInverse⟩ :=
    HirschRestrictedCoordinates.exists_unstable_section_equiv f Λ H hAdapt
      aBlock haBlock (fun x v hv ↦ (huAdapt x v hv).trans
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.sqrt_nonneg _)))
  have hStableContraction : ‖TStable‖ < 1 := hnTStable.trans_lt haBlockOne
  have hUnstableInverseContraction : ‖TUnstable.symm.toContinuousLinearMap‖ < 1 :=
    hnTUnstableInverse.trans_lt haBlockOne
  -- The graph theorem now applies to the original linear blocks at every
  -- positive native radius; only the nonlinear lift certificate remains here.
  obtain ⟨εGraph, hεGraph, hGraphData⟩ :=
    hps_corollary_5_4_local_strong_graphs TUnstable TStable 1 (1 / 4)
      zero_lt_one (by norm_num) (1 : ℕ∞) le_rfl
      (by simpa only [inv_one] using hUnstableInverseContraction) hStableContraction
  have hεNonlinear : 0 < min εGraph ((1 - aBlock) / 4) :=
    lt_min hεGraph (by positivity)
  have hNonlinearLift := exists_hirsch_nonlinear_lift f Λ H hAdapt hεNonlinear
  obtain ⟨ν, hν, ρ, R, δ, b, L, hρ, hR, hRρ, hδ, hδR, hb, hL, hGlobal, hExp⟩ :=
    hNonlinearLift
  let G := ExponentialCutoff.extension Λ (f : M → M) hAdapt
    (fun p ↦ ExponentialLift.centeredLift hAdapt (f : M → M) L p) R δ
  obtain ⟨sectionLift, hsectionZero, hsectionC1, hsectionEval⟩ :=
    ExponentialLift.exists_bounded_tangent_superposition hAdapt Λ H.compact
      (f : M → M) f.continuous H.forward_mem G ⊤ (by simp)
      hGlobal.2.1 hGlobal.2.2.1 1 zero_lt_one
  let baseEquiv : Λ ≃ Λ :=
    { toFun := fun p ↦ ⟨f p, H.forward_mem p.property⟩
      invFun := fun p ↦ ⟨f.symm p, H.backward_mem p.property⟩
      left_inv := by intro p; apply Subtype.ext; exact f.left_inv p
      right_inv := by intro p; apply Subtype.ext; exact f.right_inv p }
  obtain ⟨reindex, hreindex⟩ := Analysis.exists_bounded_section_reindex
    (fun p : Λ ↦ TangentSpace 𝓘(ℝ, E) (p : M)) baseEquiv
  let sectionEndomorph : B → B := reindex ∘ sectionLift
  have hEndomorphC1 : ContDiffOn ℝ 1 sectionEndomorph (Metric.ball 0 1) :=
    hsectionC1.continuousLinearMap_comp reindex.toContinuousLinearEquiv.toContinuousLinearMap
  have hEndomorphZero : sectionEndomorph 0 = 0 := by
    simp only [sectionEndomorph, Function.comp_apply, hsectionZero, map_zero]
  have hEndomorphEval (w : B) (hw : w ∈ Metric.ball 0 1) (p : Λ) :
      sectionEndomorph w (baseEquiv p) = G p (w p) := by
    exact (hreindex (sectionLift w) p).trans (hsectionEval w hw p)
  have hCoordinatesNorm (z : UnstableSections × StableSections) :
      ‖sectionCoordinates z‖ ≤ 2 * ‖z‖ := by
    change ‖(z.1.val : B) + z.2.val‖ ≤ _
    calc
      ‖(z.1.val : B) + z.2.val‖ ≤ ‖z.1‖ + ‖z.2‖ := norm_add_le _ _
      _ ≤ ‖z‖ + ‖z‖ := add_le_add (norm_fst_le z) (norm_snd_le z)
      _ = 2 * ‖z‖ := by ring
  have hCoordinatesBall : MapsTo sectionCoordinates
      (Metric.ball (0 : UnstableSections × StableSections) (1 / 4))
      (Metric.ball (0 : B) 1) := by
    intro z hz
    have hz' : ‖z‖ < 1 / 4 := by simpa using hz
    have hb := hCoordinatesNorm z
    simpa using (show ‖sectionCoordinates z‖ < 1 by linarith only [hb, hz'])
  obtain ⟨boxMap, hboxMap⟩ : ∃ g : UnstableSections × StableSections → UnstableSections × StableSections,
      g = sectionCoordinates.symm ∘ sectionEndomorph ∘ sectionCoordinates := ⟨_, rfl⟩
  have hBoxC1 : ContDiffOn ℝ 1 boxMap (Metric.ball 0 (1 / 4)) := by
    rw [hboxMap]
    exact (hEndomorphC1.comp sectionCoordinates.contDiff.contDiffOn hCoordinatesBall).continuousLinearMap_comp
      sectionCoordinates.symm.toContinuousLinearMap
  have hBoxZero : boxMap 0 = 0 := by
    simp only [hboxMap, Function.comp_apply, map_zero, hEndomorphZero]
  have hNuCoordinates (z : UnstableSections × StableSections) (p : Λ) :
      ν.value p (sectionCoordinates z p) = max ‖z.2.val p‖ ‖z.1.val p‖ := by
    rw [hν]
    change max ‖(H.stable.fibre p).projection (H.unstable.fibre p) (H.complementary p)
      (z.1.val p + z.2.val p)‖
      ‖(H.unstable.fibre p).projection (H.stable.fibre p) (H.complementary p).symm
      (z.1.val p + z.2.val p)‖ = _
    rw [map_add, map_add,
      Submodule.projection_apply_of_mem_right (H.complementary p) (z.1.property p),
      Submodule.projection_apply_of_mem_left (H.complementary p) (z.2.property p),
      Submodule.projection_apply_of_mem_left (H.complementary p).symm (z.1.property p),
      Submodule.projection_apply_of_mem_right (H.complementary p).symm (z.2.property p),
      zero_add, add_zero]
  have hNuCoordinatesLe (z : UnstableSections × StableSections) (p : Λ) :
      ν.value p (sectionCoordinates z p) ≤ ‖z‖ := by
    rw [hNuCoordinates]
    exact max_le ((lp.norm_apply_le_norm ENNReal.top_ne_zero z.2.val p).trans (norm_snd_le z))
      ((lp.norm_apply_le_norm ENNReal.top_ne_zero z.1.val p).trans (norm_fst_le z))
  have hNuBound (w : B) (C : ℝ) (hC : 0 ≤ C) (hw : ∀ p, ν.value p (w p) ≤ C) :
      ‖sectionCoordinates.symm w‖ ≤ C := by
    rw [Prod.norm_def]
    have hp (p : Λ) : max ‖(sectionCoordinates.symm w).2.val p‖
        ‖(sectionCoordinates.symm w).1.val p‖ ≤ C := by
      rw [← hNuCoordinates, sectionCoordinates.apply_symm_apply]
      exact hw p
    apply max_le
    · exact lp.norm_le_of_forall_le hC (fun p ↦ (le_max_right _ _).trans (hp p))
    · exact lp.norm_le_of_forall_le hC (fun p ↦ (le_max_left _ _).trans (hp p))
  have hLinearEval (z : UnstableSections × StableSections) (p : Λ) :
      sectionCoordinates (TUnstable z.1, TStable z.2) (baseEquiv p) =
        mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) f (p : M) (sectionCoordinates z p) := by
    change (TUnstable z.1).val (baseEquiv p) + (TStable z.2).val (baseEquiv p) = _
    rw [hTUnstable, hTStable]
    have he : (⟨f.symm (baseEquiv p), H.backward_mem (baseEquiv p).property⟩ : Λ) = p :=
      Subtype.ext (f.symm_apply_apply p)
    rw [he]
    change mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) f (f.symm (f p)) (z.1.val p) +
      mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) f (f.symm (f p)) (z.2.val p) =
      mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) f (p : M) (z.1.val p + z.2.val p)
    rw [f.symm_apply_apply, map_add]
  have hGderiv (p : Λ) : HasFDerivAt (G p)
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) f (p : M)) 0 := by
    let J := tangentSpaceCastModel 𝓘(ℝ, E) (p : M)
    let K := tangentSpaceCastModel 𝓘(ℝ, E) (f p)
    have hh : HasFDerivAt (K ∘ (G p ∘ J.symm))
        (K.toContinuousLinearMap.comp
          ((mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) f (p : M)).comp J.symm.toContinuousLinearMap)) 0 :=
      hGlobal.2.2.2.1 p
    have hn := K.comp_hasFDerivAt_iff.mp hh
    simpa only [map_zero] using J.symm.comp_right_hasFDerivAt_iff.mp hn
  have hEndomorphDeriv : HasFDerivAt sectionEndomorph
      (fderiv ℝ sectionEndomorph 0) 0 :=
    ((hEndomorphC1.contDiffAt (Metric.ball_mem_nhds 0 zero_lt_one)).differentiableAt
      (by simp)).hasFDerivAt
  have hEndomorphDerivEval (w : B) (p : Λ) :
      fderiv ℝ sectionEndomorph 0 w (baseEquiv p) =
        mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) f (p : M) (w p) := by
    let ev (q : Λ) := lp.evalCLM (𝕜 := ℝ)
      (fun x : Λ ↦ TangentSpace 𝓘(ℝ, E) (x : M)) ⊤ q
    have hh := (ev (baseEquiv p)).hasFDerivAt.comp 0 hEndomorphDeriv
    have hh' := (hGderiv p).comp 0 (ev p).hasFDerivAt
    have heq : (fun w : B ↦ ev (baseEquiv p) (sectionEndomorph w)) =ᶠ[𝓝 0]
        (fun w : B ↦ G p (ev p w)) := by
      filter_upwards [Metric.ball_mem_nhds (0 : B) zero_lt_one] with w hw
      exact hEndomorphEval w hw p
    have he := hh.unique (hh'.congr_of_eventuallyEq heq)
    exact DFunLike.congr_fun he w
  have hBoxDeriv : HasFDerivAt boxMap
      (TUnstable.toContinuousLinearMap.prodMap TStable) 0 := by
    rw [hboxMap]
    have he : HasFDerivAt sectionEndomorph (fderiv ℝ sectionEndomorph 0)
        (sectionCoordinates 0) := by simpa only [map_zero] using hEndomorphDeriv
    have hh := sectionCoordinates.symm.hasFDerivAt.comp 0
      (he.comp 0 sectionCoordinates.hasFDerivAt)
    apply hh.congr_fderiv
    apply ContinuousLinearMap.ext
    intro z
    apply sectionCoordinates.injective
    apply lp.ext
    funext p
    obtain ⟨q, rfl⟩ := baseEquiv.surjective p
    change sectionCoordinates (sectionCoordinates.symm
      (fderiv ℝ sectionEndomorph 0 (sectionCoordinates z))) (baseEquiv q) =
        sectionCoordinates (TUnstable z.1, TStable z.2) (baseEquiv q)
    rw [sectionCoordinates.apply_symm_apply, hEndomorphDerivEval, hLinearEval]
  have hBoxRemainder : ∀ z ∈ Metric.ball (0 : UnstableSections × StableSections) (1 / 4),
      ∀ z' ∈ Metric.ball (0 : UnstableSections × StableSections) (1 / 4),
      ‖(boxMap z - (TUnstable z.1, TStable z.2)) -
        (boxMap z' - (TUnstable z'.1, TStable z'.2))‖ ≤ εGraph * ‖z - z'‖ := by
    intro z hz z' hz'
    let W : B := (sectionEndomorph (sectionCoordinates z) -
      sectionCoordinates (TUnstable z.1, TStable z.2)) -
      (sectionEndomorph (sectionCoordinates z') -
        sectionCoordinates (TUnstable z'.1, TStable z'.2))
    have hW := hNuBound W (εGraph * ‖z - z'‖)
      (mul_nonneg hεGraph.le (norm_nonneg _))
    have hWp : ∀ p, ν.value p (W p) ≤ εGraph * ‖z - z'‖ := by
      intro p
      obtain ⟨q, rfl⟩ := baseEquiv.surjective p
      change ν.value (baseEquiv q)
        ((sectionEndomorph (sectionCoordinates z) (baseEquiv q) -
          sectionCoordinates (TUnstable z.1, TStable z.2) (baseEquiv q)) -
        (sectionEndomorph (sectionCoordinates z') (baseEquiv q) -
          sectionCoordinates (TUnstable z'.1, TStable z'.2) (baseEquiv q))) ≤ _
      rw [hEndomorphEval (sectionCoordinates z) (hCoordinatesBall hz) q,
        hEndomorphEval (sectionCoordinates z') (hCoordinatesBall hz') q,
        hLinearEval z q, hLinearEval z' q]
      have hm := hGlobal.2.2.2.2.1 q (sectionCoordinates z q) (sectionCoordinates z' q)
      have hsc := congrArg Subtype.val (sectionCoordinates.map_sub z z')
      have hin0 := hNuCoordinatesLe (z - z') q
      rw [hsc] at hin0
      have hin : ν.value q (sectionCoordinates z q - sectionCoordinates z' q) ≤ ‖z - z'‖ := by
        exact hin0
      exact hm.trans ((mul_le_mul_of_nonneg_left hin hεNonlinear.le).trans
        (mul_le_mul_of_nonneg_right (min_le_left _ _) (norm_nonneg _)))
    have hh := hW hWp
    simpa only [W, map_sub, sectionCoordinates.symm_apply_apply,
      hboxMap, Function.comp_apply] using hh
  have hSectionGraphs := hGraphData.2.2.2.2.2.2 boxMap hBoxC1 hBoxZero hBoxRemainder
  have hUnstableGraph := hSectionGraphs.1 hUnstableInverseContraction
  have hStableGraph := hSectionGraphs.2 hStableContraction
  obtain ⟨Ψ, hΨsmooth, hΨzero, hΨmem, hΨinv, hΨcapture, hΨunique⟩ := hStableGraph
  have hCoordinatesUnstable (w : B) (p : Λ) :
      (sectionCoordinates.symm w).1.val p =
        (H.unstable.fibre p).projection (H.stable.fibre p) (H.complementary p).symm (w p) := by
    have hh := congrArg (fun v : B ↦
      (H.unstable.fibre p).projection (H.stable.fibre p) (H.complementary p).symm (v p))
      (sectionCoordinates.apply_symm_apply w)
    change (H.unstable.fibre p).projection (H.stable.fibre p) (H.complementary p).symm
      ((sectionCoordinates.symm w).1.val p + (sectionCoordinates.symm w).2.val p) = _ at hh
    simpa only [map_add,
      Submodule.projection_apply_of_mem_left (H.complementary p).symm
        ((sectionCoordinates.symm w).1.property p),
      Submodule.projection_apply_of_mem_right (H.complementary p).symm
        ((sectionCoordinates.symm w).2.property p), add_zero] using hh
  have hCoordinatesStable (w : B) (p : Λ) :
      (sectionCoordinates.symm w).2.val p =
        (H.stable.fibre p).projection (H.unstable.fibre p) (H.complementary p) (w p) := by
    have hh := congrArg (fun v : B ↦
      (H.stable.fibre p).projection (H.unstable.fibre p) (H.complementary p) (v p))
      (sectionCoordinates.apply_symm_apply w)
    change (H.stable.fibre p).projection (H.unstable.fibre p) (H.complementary p)
      ((sectionCoordinates.symm w).1.val p + (sectionCoordinates.symm w).2.val p) = _ at hh
    simpa only [map_add,
      Submodule.projection_apply_of_mem_right (H.complementary p)
        ((sectionCoordinates.symm w).1.property p),
      Submodule.projection_apply_of_mem_left (H.complementary p)
        ((sectionCoordinates.symm w).2.property p), zero_add] using hh
  have hBoxLocal (w : UnstableSections × StableSections) (hw : ‖w‖ < 1 / 4)
      (z : UnstableSections × StableSections) (hz : ‖z‖ < 1 / 4) (p : Λ)
      (h₁ : w.1.val p = z.1.val p) (h₂ : w.2.val p = z.2.val p) :
      (boxMap w).1.val (baseEquiv p) = (boxMap z).1.val (baseEquiv p) ∧
      (boxMap w).2.val (baseEquiv p) = (boxMap z).2.val (baseEquiv p) := by
    have hinput : sectionCoordinates w p = sectionCoordinates z p := by
      change w.1.val p + w.2.val p = z.1.val p + z.2.val p
      rw [h₁, h₂]
    simp only [hboxMap, Function.comp_apply]
    rw [hCoordinatesUnstable, hCoordinatesUnstable, hCoordinatesStable, hCoordinatesStable,
      hEndomorphEval _ (hCoordinatesBall (by simpa using hw)),
      hEndomorphEval _ (hCoordinatesBall (by simpa using hz)), hinput]
    exact ⟨rfl, rfl⟩
  have hΨorbit (s : StableSections) (hs : ‖s‖ < 1 / 4) (n : ℕ) :
      ‖boxMap^[n] (Ψ s, s)‖ < 1 / 4 ∧
        (boxMap^[n] (Ψ s, s)).1 = Ψ (boxMap^[n] (Ψ s, s)).2 := by
    exact graph_orbit_retained_g9 boxMap Ψ hΨmem hΨinv s hs n
  have hΨcaptureOrbit (w : ℕ → UnstableSections × StableSections)
      (hm : ∀ n, ‖w n‖ < 1 / 4) (hr : ∀ n, boxMap (w n) = w (n + 1)) :
      (w 0).1 = Ψ (w 0).2 := by
    apply (hΨcapture (w 0) (by simpa using hm 0)).1.mpr
    refine ⟨w, rfl, fun n ↦ by simpa using hm n, hr, 1 / 4, ?_⟩
    intro n
    simpa using (hm n).le
  have hΨfibrewise (s t : StableSections) (hs : ‖s‖ < 1 / 4) (ht : ‖t‖ < 1 / 4)
      (p : Λ) (heq : s.val p = t.val p) : (Ψ s).val p = (Ψ t).val p :=
    bounded_section_graph_fibrewise H.unstable.fibre H.stable.fibre baseEquiv boxMap Ψ (1 / 4)
      (fun s hs n ↦ (hΨorbit s hs n).1) hΨcaptureOrbit hBoxLocal s t hs ht p heq
  have hΨderiv := ((hΨsmooth.contDiffAt
    (Metric.ball_mem_nhds (0 : StableSections) (by norm_num : (0 : ℝ) < 1 / 4))).differentiableAt
      (by simp)).hasFDerivAt
  have hΨtangent : fderiv ℝ Ψ 0 = 0 := by
    exact invariant_graph_derivative_zero_g9 TUnstable TStable
      hUnstableInverseContraction hStableContraction boxMap hBoxZero hBoxDeriv Ψ hΨzero hΨderiv hΨinv
  let singleS (p : Λ) : H.stable.fibre p →L[ℝ] StableSections :=
    (((lp.singleContinuousLinearMap ℝ
      (fun x : Λ ↦ TangentSpace 𝓘(ℝ, E) (x : M)) ⊤ p).comp
      (H.stable.fibre p).subtypeL).codRestrict StableSections (by
        intro s q
        by_cases hq : q = p
        · subst q; simp
        · simp [Pi.single_eq_of_ne hq]))
  let evalU (p : Λ) : UnstableSections →L[ℝ] H.unstable.fibre p :=
    (((lp.evalCLM (𝕜 := ℝ)
      (fun x : Λ ↦ TangentSpace 𝓘(ℝ, E) (x : M)) ⊤ p).comp
      UnstableSections.subtypeL).codRestrict (H.unstable.fibre p) (fun s ↦ s.property p))
  have hSingleNorm (p : Λ) (s : H.stable.fibre p) : ‖singleS p s‖ = ‖s‖ := by
    change ‖lp.single (E := fun x : Λ ↦ TangentSpace 𝓘(ℝ, E) (x : M)) ⊤ p s.val‖ = ‖s.val‖
    exact lp.norm_single (E := fun x : Λ ↦ TangentSpace 𝓘(ℝ, E) (x : M))
      (by simp : (0 : ENNReal) < ⊤) p s.val
  let μ (p : Λ) : H.stable.fibre p → H.unstable.fibre p := evalU p ∘ Ψ ∘ singleS p
  have hμzero (p : Λ) : μ p 0 = 0 := by simp [μ, hΨzero]
  have hμsmooth (p : Λ) : ContDiffOn ℝ 1 (μ p) (Metric.ball 0 (1 / 4)) := by
    apply (hΨsmooth.comp (singleS p).contDiff.contDiffOn ?_).continuousLinearMap_comp (evalU p)
    intro s hs
    simpa only [Metric.mem_ball, dist_zero_right, hSingleNorm] using hs
  have hμtangent (p : Λ) : HasFDerivAt (μ p) (0 : H.stable.fibre p →L[ℝ] H.unstable.fibre p) 0 := by
    have hd : HasFDerivAt Ψ (0 : StableSections →L[ℝ] UnstableSections) (singleS p 0) := by
      simpa only [map_zero, hΨtangent] using hΨderiv
    have hh := (evalU p).hasFDerivAt.comp 0 (hd.comp 0 (singleS p).hasFDerivAt)
    simpa only [ContinuousLinearMap.zero_comp, ContinuousLinearMap.comp_zero] using hh
  have hμrepresents (s : StableSections) (hs : ‖s‖ < 1 / 4) (p : Λ) :
      (Ψ s).val p = (μ p ⟨s.val p, s.property p⟩).val := by
    have hn : ‖singleS p ⟨s.val p, s.property p⟩‖ < 1 / 4 := by
      rw [hSingleNorm]
      exact (lp.norm_apply_le_norm ENNReal.top_ne_zero s.val p).trans_lt hs
    exact hΨfibrewise s (singleS p ⟨s.val p, s.property p⟩) hs hn p (by
      change s.val p = lp.single (E := fun x : Λ ↦ TangentSpace 𝓘(ℝ, E) (x : M)) ⊤ p (s.val p) p
      simp)
  have hΨsmallSlope (η : NNReal) (hη : 0 < η) : ∃ r : ℝ,
      0 < r ∧ r ≤ 1 / 4 ∧ LipschitzOnWith η Ψ (Metric.ball 0 r) := by
    have hd := (hΨsmooth.contDiffAt (Metric.ball_mem_nhds (0 : StableSections)
      (by norm_num : (0 : ℝ) < 1 / 4))).hasStrictFDerivAt (by simp)
    rw [hΨtangent] at hd
    obtain ⟨V, hV, hLip⟩ := hd.exists_lipschitzOnWith_of_nnnorm_lt η (by simpa using hη)
    obtain ⟨r, hr, hrV⟩ := Metric.mem_nhds_iff.mp hV
    refine ⟨min r (1 / 4), lt_min hr (by norm_num), min_le_right _ _, hLip.mono ?_⟩
    exact (Metric.ball_subset_ball (min_le_left _ _)).trans hrV
  have hμsmallSlope (η : NNReal) (hη : 0 < η) : ∃ r : ℝ,
      0 < r ∧ r ≤ 1 / 4 ∧ ∀ p : Λ,
        LipschitzOnWith η (μ p) (Metric.ball 0 r) := by
    obtain ⟨r, hr, hrq, hLip⟩ := hΨsmallSlope η hη
    refine ⟨r, hr, hrq, fun p ↦ lipschitzOnWith_iff_norm_sub_le.mpr ?_⟩
    intro s hs t ht
    have hsm : singleS p s ∈ Metric.ball 0 r := by
      simpa only [Metric.mem_ball, dist_zero_right, hSingleNorm] using hs
    have htm : singleS p t ∈ Metric.ball 0 r := by
      simpa only [Metric.mem_ball, dist_zero_right, hSingleNorm] using ht
    have hh := (lipschitzOnWith_iff_norm_sub_le.mp hLip) hsm htm
    rw [← map_sub, hSingleNorm] at hh
    have hev := lp.norm_apply_le_norm ENNReal.top_ne_zero
      ((Ψ (singleS p s)).val - (Ψ (singleS p t)).val) p
    exact hev.trans hh
  have hNativeGraphStep : ∃ r : ℝ, 0 < r ∧ r ≤ 1 / 4 ∧
      ∀ p : Λ, ∀ s : H.stable.fibre p, ‖s‖ < r →
        ∃ t : H.stable.fibre (baseEquiv p), ‖t‖ ≤ ‖s‖ ∧ ‖t‖ < r ∧
          G p (s.val + (μ p s).val) = t.val + (μ (baseEquiv p) t).val := by
    obtain ⟨r, hr, hrq, hLip⟩ := hΨsmallSlope 1 (by norm_num)
    refine ⟨r, hr, hrq, ?_⟩
    intro p s hs
    let S := singleS p s
    have hSm : S ∈ Metric.ball (0 : StableSections) r := by
      simpa only [S, Metric.mem_ball, dist_zero_right, hSingleNorm] using hs
    have hΨS : ‖Ψ S‖ ≤ ‖S‖ := by
      have hh := (lipschitzOnWith_iff_norm_sub_le.mp hLip) hSm
        (show (0 : StableSections) ∈ Metric.ball 0 r by simpa using hr)
      simpa only [hΨzero, sub_zero, NNReal.coe_one, one_mul] using hh
    let Z := (Ψ S, S)
    have hZn : ‖Z‖ = ‖s‖ := by
      rw [Prod.norm_def, max_eq_right hΨS, hSingleNorm]
    have hZm : Z ∈ Metric.ball (0 : UnstableSections × StableSections) (1 / 4) := by
      simpa only [Metric.mem_ball, dist_zero_right, hZn] using hs.trans_le hrq
    have hSmq : S ∈ Metric.ball (0 : StableSections) (1 / 4) :=
      Metric.ball_subset_ball hrq hSm
    let W := boxMap Z
    have hWi := hΨinv S hSmq
    have hWn : ‖W‖ < 1 / 4 := by simpa only [Metric.mem_ball, dist_zero_right] using hWi.1
    let t : H.stable.fibre (baseEquiv p) := ⟨W.2.val (baseEquiv p), W.2.property (baseEquiv p)⟩
    have hrem := hBoxRemainder Z hZm 0 (by simp : (0 : UnstableSections × StableSections) ∈ Metric.ball 0 (1 / 4))
    simp only [hBoxZero, Prod.fst_zero, Prod.snd_zero, map_zero,
      Prod.mk_zero_zero, sub_self, sub_zero, hZn] at hrem
    have hW2 : ‖W.2‖ ≤ (‖TStable‖ + εGraph) * ‖s‖ := by
      have hcoord := (norm_snd_le (W - (TUnstable Z.1, TStable Z.2))).trans hrem
      have hlin := TStable.le_opNorm S
      rw [hSingleNorm] at hlin
      have hh := norm_le_norm_add_norm_sub' W.2 (TStable S)
      change ‖W.2 - TStable S‖ ≤ εGraph * ‖s‖ at hcoord
      nlinarith only [hcoord, hlin, hh]
    have hcoef : ‖TStable‖ + εGraph < 1 := hGraphData.2.2.1
    have ht : ‖t‖ ≤ ‖s‖ :=
      ((lp.norm_apply_le_norm ENNReal.top_ne_zero W.2.val (baseEquiv p)).trans hW2).trans
        (mul_le_of_le_one_left (norm_nonneg s) hcoef.le)
    refine ⟨t, ht, ht.trans_lt hs, ?_⟩
    have hZval : sectionCoordinates Z p = s.val + (μ p s).val := by
      change (μ p s).val + (lp.single ⊤ p s.val : B) p = _
      rw [lp.single_apply_self, add_comm]
    have hWeval : sectionCoordinates W (baseEquiv p) = G p (s.val + (μ p s).val) := by
      dsimp only [W]
      rw [hboxMap]
      have hh := hEndomorphEval (sectionCoordinates Z) (hCoordinatesBall hZm) p
      change sectionCoordinates (sectionCoordinates.symm (sectionEndomorph (sectionCoordinates Z)))
        (baseEquiv p) = _
      rw [sectionCoordinates.apply_symm_apply, hh, hZval]
    rw [← hWeval]
    change W.1.val (baseEquiv p) + W.2.val (baseEquiv p) = _
    rw [show W.1 = Ψ W.2 from hWi.2,
      hμrepresents W.2 ((norm_snd_le W).trans_lt hWn) (baseEquiv p)]
    exact add_comm _ _
  have hCaptureSections (w : ℕ → B)
      (hm : ∀ n, ‖sectionCoordinates.symm (w n)‖ < 1 / 4)
      (hrec : ∀ n p, w (n + 1) (baseEquiv p) = G p (w n p)) (p : Λ) :
      (sectionCoordinates.symm (w 0)).1.val p =
        (μ p ⟨(sectionCoordinates.symm (w 0)).2.val p,
          (sectionCoordinates.symm (w 0)).2.property p⟩).val := by
    let z (n : ℕ) := sectionCoordinates.symm (w n)
    have hz : ∀ n, boxMap (z n) = z (n + 1) := by
      intro n
      rw [hboxMap]
      apply sectionCoordinates.injective
      change sectionCoordinates (sectionCoordinates.symm (sectionEndomorph
        (sectionCoordinates (sectionCoordinates.symm (w n))))) =
          sectionCoordinates (sectionCoordinates.symm (w (n + 1)))
      simp only [sectionCoordinates.apply_symm_apply]
      apply lp.ext
      funext q
      obtain ⟨p, rfl⟩ := baseEquiv.surjective q
      have hw : w n ∈ Metric.ball (0 : B) 1 := by
        have hh := hCoordinatesBall (show sectionCoordinates.symm (w n) ∈
          Metric.ball 0 (1 / 4) by simpa using hm n)
        simpa only [sectionCoordinates.apply_symm_apply] using hh
      exact (hEndomorphEval (w n) hw p).trans (hrec n p).symm
    have hh := hΨcaptureOrbit z hm hz
    have he := congrArg (fun s : UnstableSections ↦ s.val p) hh
    exact he.trans (hμrepresents (z 0).2 ((norm_snd_le _).trans_lt (hm 0)) p)
  have hCaptureNative (p : ℕ → Λ)
      (hp : ∀ n, p (n + 1) = baseEquiv (p n))
      (v : (n : ℕ) → TangentSpace 𝓘(ℝ, E) ((p n : Λ) : M))
      (hm : ∀ n, ‖sectionCoordinates.symm.toContinuousLinearMap‖ * ‖v n‖ < 1 / 4)
      (hrec : ∀ n, G (p n) (v n) =
        (lp.single ⊤ (p (n + 1)) (v (n + 1)) : B) (baseEquiv (p n))) :
      (H.unstable.fibre (p 0)).projection (H.stable.fibre (p 0))
          (H.complementary (p 0)).symm (v 0) =
        (μ (p 0) ((H.stable.fibre (p 0)).projectionOnto (H.unstable.fibre (p 0))
          (H.complementary (p 0)) (v 0))).val := by
    let w (n : ℕ) : B := lp.single ⊤ (p n) (v n)
    have hwm (n : ℕ) : ‖sectionCoordinates.symm (w n)‖ < 1 / 4 := by
      apply (sectionCoordinates.symm.toContinuousLinearMap.le_opNorm (w n)).trans_lt
      simpa only [w, lp.norm_single (by simp : (0 : ENNReal) < ⊤)] using hm n
    have hwrec (n : ℕ) (q : Λ) : w (n + 1) (baseEquiv q) = G q (w n q) := by
      by_cases hq : q = p n
      · subst q
        simpa only [w, lp.single_apply_self] using (hrec n).symm
      · have hq' : baseEquiv q ≠ p (n + 1) := by
          rw [hp n]
          exact fun hh ↦ hq (baseEquiv.injective hh)
        simp only [w, lp.single_apply_ne ⊤ _ _ hq', lp.single_apply_ne ⊤ _ _ hq]
        exact (hGlobal.2.2.1 q).symm
    have hh := hCaptureSections w hwm hwrec (p 0)
    have hs : (⟨(sectionCoordinates.symm (w 0)).2.val (p 0),
        (sectionCoordinates.symm (w 0)).2.property (p 0)⟩ : H.stable.fibre (p 0)) =
        (H.stable.fibre (p 0)).projectionOnto (H.unstable.fibre (p 0))
          (H.complementary (p 0)) (v 0) := by
      apply Subtype.ext
      simpa only [w, lp.single_apply_self, Submodule.coe_projectionOnto_apply] using
        hCoordinatesStable (w 0) (p 0)
    rw [hs] at hh
    simpa only [w, lp.single_apply_self, Submodule.coe_projectionOnto_apply] using
      (hCoordinatesUnstable (w 0) (p 0)).symm.trans hh
  have hNormNu (p : Λ) (v : TangentSpace 𝓘(ℝ, E) (p : M)) :
      ‖v‖ ≤ 2 * ν.value p v := by
    rw [hν]
    let s := (H.stable.fibre p).projection (H.unstable.fibre p) (H.complementary p) v
    let u := (H.unstable.fibre p).projection (H.stable.fibre p) (H.complementary p).symm v
    have hv : s + u = v := Submodule.projection_add_projection_eq_self (H.complementary p) v
    change ‖v‖ ≤ 2 * max ‖s‖ ‖u‖
    calc
      ‖v‖ = ‖s + u‖ := congrArg norm hv.symm
      _ ≤ ‖s‖ + ‖u‖ := norm_add_le _ _
      _ ≤ 2 * max ‖s‖ ‖u‖ := by linarith only [le_max_left ‖s‖ ‖u‖, le_max_right ‖s‖ ‖u‖]
  obtain ⟨K, hK, hDerivativeBound⟩ :=
    HirschRestrictedCoordinates.exists_uniform_mfderiv_bound H.compact f f.contMDiff hAdapt
  have hNativeTangentContraction : ∃ κ r : ℝ,
      0 < κ ∧ κ < 1 ∧ 0 < r ∧ r ≤ 1 / 4 ∧
      ∀ p : Λ, ∀ s : H.stable.fibre p, ‖s‖ < r →
        ‖G p (s.val + (μ p s).val)‖ ≤ κ * ‖s.val + (μ p s).val‖ := by
    let κ := (3 + aBlock) / 4
    let η := (1 - aBlock) / (16 * (K + 1))
    have hκ : 0 < κ := by dsimp [κ]; linarith only [haBlock]
    have hκ1 : κ < 1 := by dsimp [κ]; linarith only [haBlockOne]
    have hη : 0 < η := div_pos (by linarith only [haBlockOne]) (by positivity)
    have hη1 : η < 1 := by dsimp [η]; apply (div_lt_one (by positivity)).mpr; linarith only [haBlock, hK]
    have hηid : η * (16 * (K + 1)) = 1 - aBlock := by
      dsimp [η]; exact div_mul_cancel₀ _ (by positivity)
    have hcoeff : aBlock + K * η + (1 - aBlock) / 2 ≤ κ * (1 - η) := by
      dsimp [κ]
      nlinarith only [hηid, mul_nonneg (sub_nonneg.mpr haBlockOne.le) hη.le, mul_nonneg hK.le hη.le, hη.le]
    obtain ⟨r, hr, hrq, hμLip⟩ := hμsmallSlope ⟨η, hη.le⟩ hη
    refine ⟨κ, r, hκ, hκ1, hr, hrq, ?_⟩
    intro p s hs
    let u := (μ p s).val
    let v := s.val + u
    have hu : ‖u‖ ≤ η * ‖s‖ := by
      have hh := (lipschitzOnWith_iff_norm_sub_le.mp (hμLip p))
        (show s ∈ Metric.ball 0 r by simpa using hs)
        (show (0 : H.stable.fibre p) ∈ Metric.ball 0 r by simpa using hr)
      simp only [hμzero, sub_zero] at hh
      change ‖u‖ ≤ η * ‖s‖ at hh
      exact hh
    have hu' : ‖u‖ ≤ ‖s‖ := hu.trans (mul_le_of_le_one_left (norm_nonneg _) hη1.le)
    have hνv : ν.value p v = ‖s‖ := by
      rw [hν]
      change max
        ‖(H.stable.fibre p).projection (H.unstable.fibre p) (H.complementary p) (s.val + u)‖
        ‖(H.unstable.fibre p).projection (H.stable.fibre p) (H.complementary p).symm (s.val + u)‖ = ‖s‖
      rw [map_add, map_add,
        Submodule.projection_apply_of_mem_left (H.complementary p) s.property,
        Submodule.projection_apply_of_mem_right (H.complementary p) (μ p s).property,
        Submodule.projection_apply_of_mem_right (H.complementary p).symm s.property,
        Submodule.projection_apply_of_mem_left (H.complementary p).symm (μ p s).property,
        add_zero, zero_add]
      exact max_eq_left hu'
    have hrem : ‖G p v - mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) f (p : M) v‖ ≤
        ((1 - aBlock) / 2) * ‖s‖ := by
      have hh := hGlobal.2.2.2.2.1 p v 0
      simp only [hGlobal.2.2.1, map_zero, sub_zero, hνv] at hh
      have hb := (hNormNu (baseEquiv p) _).trans (mul_le_mul_of_nonneg_left hh (by norm_num))
      have he := mul_le_mul_of_nonneg_right (min_le_right εGraph ((1 - aBlock) / 4)) (norm_nonneg s)
      nlinarith only [hb, he]
    have hlinear : ‖mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) f (p : M) v‖ ≤
        (aBlock + K * η) * ‖s‖ := by
      have hs' : ‖mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) f (p : M) s.val‖ ≤ aBlock * ‖s‖ :=
        (hsAdapt p s.val s.property).trans
          (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg s))
      have hu'' : ‖mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) f (p : M) u‖ ≤ K * (η * ‖s‖) :=
        (hDerivativeBound p u).trans (mul_le_mul_of_nonneg_left hu hK.le)
      have hh := norm_add_le
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) f (p : M) s.val)
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) f (p : M) u)
      change ‖mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) f (p : M) (s.val + u)‖ ≤ _
      rw [map_add]
      nlinarith only [hs', hu'', hh]
    have hlower : (1 - η) * ‖s‖ ≤ ‖v‖ := by
      have hh := norm_sub_le v u
      have he : v - u = s.val := by simp [v]
      rw [he] at hh
      change ‖s‖ ≤ ‖v‖ + ‖u‖ at hh
      nlinarith only [hh, hu]
    have hupper := norm_le_norm_add_norm_sub' (G p v)
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) f (p : M) v)
    exact (hupper.trans (add_le_add hlinear hrem)).trans (by
      calc
        _ = (aBlock + K * η + (1 - aBlock) / 2) * ‖s‖ := by ring
        _ ≤ (κ * (1 - η)) * ‖s‖ := mul_le_mul_of_nonneg_right hcoeff (norm_nonneg s)
        _ = κ * ((1 - η) * ‖s‖) := by ring
        _ ≤ κ * ‖v‖ := mul_le_mul_of_nonneg_left hlower hκ.le)
  obtain ⟨ρnormal, hρnormal, hNormalDistance⟩ :=
    compact_uniform_exponential_distance_radius hAdapt Λ H.compact
  have hNativeGraphGeometricStep : ∃ κ r : ℝ,
      0 < κ ∧ κ < 1 ∧ 0 < r ∧ r ≤ 1 / 4 ∧
      ∀ p : Λ, ∀ s : H.stable.fibre p, ‖s‖ < r →
        ‖s.val + (μ p s).val‖ ≤ ρnormal ∧
        ∃ t : H.stable.fibre (baseEquiv p), ‖t‖ ≤ ‖s‖ ∧ ‖t‖ < r ∧
          ‖t.val + (μ (baseEquiv p) t).val‖ ≤ κ * ‖s.val + (μ p s).val‖ ∧
          f (riemannianExponential hAdapt ⟨(p : M), s.val + (μ p s).val⟩) =
            riemannianExponential hAdapt ⟨(baseEquiv p : M), t.val + (μ (baseEquiv p) t).val⟩ := by
    obtain ⟨κ, rc, hκ, hκ1, hrc, hrcq, hcontract⟩ := hNativeTangentContraction
    obtain ⟨rs, hrs, hrsq, hstep⟩ := hNativeGraphStep
    obtain ⟨rl, hrl, hrlq, hLip⟩ := hμsmallSlope 1 (by norm_num)
    let r := min rc (min rs (min rl (min b (ρnormal / 2))))
    have hr : 0 < r := by dsimp [r]; positivity
    have hrc' : r ≤ rc := min_le_left _ _
    have hrs' : r ≤ rs := (min_le_right _ _).trans (min_le_left _ _)
    have hrl' : r ≤ rl := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
    have hb' : r ≤ b := (min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _)))
    have hn' : r ≤ ρnormal / 2 := (min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_right _ _)))
    refine ⟨κ, r, hκ, hκ1, hr, hrc'.trans hrcq, ?_⟩
    intro p s hs
    have hμbound : ‖(μ p s).val‖ ≤ ‖s‖ := by
      have hh := (lipschitzOnWith_iff_norm_sub_le.mp (hLip p))
        (show s ∈ Metric.ball 0 rl by simpa using hs.trans_le hrl')
        (show (0 : H.stable.fibre p) ∈ Metric.ball 0 rl by simpa using hrl)
      simp only [hμzero, sub_zero, NNReal.coe_one, one_mul] at hh
      exact hh
    have hn : ‖s.val + (μ p s).val‖ ≤ ρnormal := by
      have hh : ‖s.val + (μ p s).val‖ ≤ ‖s‖ + ‖(μ p s).val‖ :=
        norm_add_le s.val (μ p s).val
      have hsn := hs.trans_le hn'
      nlinarith only [hh, hμbound, hsn]
    obtain ⟨t, ht, htr, hG⟩ := hstep p s (hs.trans_le hrs')
    refine ⟨hn, t, ht, ht.trans_lt hs, ?_, ?_⟩
    · rw [← hG]
      exact hcontract p s (hs.trans_le hrc')
    · have hνgraph : ν.value p (s.val + (μ p s).val) = ‖s‖ := by
        rw [hν, map_add, map_add,
          Submodule.projection_apply_of_mem_left (H.complementary p) s.property,
          Submodule.projection_apply_of_mem_right (H.complementary p) (μ p s).property,
          Submodule.projection_apply_of_mem_right (H.complementary p).symm s.property,
          Submodule.projection_apply_of_mem_left (H.complementary p).symm (μ p s).property,
          add_zero, zero_add]
        exact max_eq_left hμbound
      have hh := (hExp p (s.val + (μ p s).val) (by rw [hνgraph]; exact hs.le.trans hb')).2.2.2.2
      change riemannianExponential hAdapt ⟨f p, G p (s.val + (μ p s).val)⟩ = _ at hh
      rw [hG] at hh
      exact hh.symm
  have hNormalMetric (p : Λ) (v : TangentSpace 𝓘(ℝ, E) (p : M)) (hv : ‖v‖ ≤ ρnormal) :
      dAdapt.dist (p : M) (riemannianExponential hAdapt ⟨(p : M), v⟩) = ‖v‖ := by
    obtain ⟨hdom, heq⟩ := hNormalDistance p p.property v hv
    obtain ⟨J, hJ, hJconn, hseg, hgeod, hradialdom, hspeed⟩ :=
      (gallier_quaintance_gauss_lemma hAdapt).2.2.2.2.1 (p : M) v hdom
    let c := fun t : ℝ ↦ riemannianExponential hAdapt ⟨(p : M), t • v⟩
    have hc0 : c 0 = (p : M) := by
      simpa only [c, zero_smul] using (riemannianExponential_zero hAdapt (p : M)).2
    have hc1 : c 1 = riemannianExponential hAdapt ⟨(p : M), v⟩ := by simp only [c, one_smul]
    have hc : IsPreconnected (c '' Set.Icc (0 : ℝ) 1) :=
      isPreconnected_Icc.image c (hgeod.1.continuousOn.mono hseg)
    have hcomp : riemannianExponential hAdapt ⟨(p : M), v⟩ ∈ connectedComponent (p : M) :=
      hc.subset_connectedComponent ⟨0, ⟨le_rfl, zero_le_one⟩, hc0⟩
        ⟨1, ⟨zero_le_one, le_rfl⟩, hc1⟩
    have hd := (hdComp p _ hcomp).trans heq
    rw [@edist_dist M dAdapt.toPseudoMetricSpace] at hd
    exact (ENNReal.ofReal_eq_ofReal_iff (@dist_nonneg M dAdapt.toPseudoMetricSpace _ _)
      (norm_nonneg _)).mp hd
  have hNuOrdinary (p : Λ) (v : TangentSpace 𝓘(ℝ, E) (p : M)) :
      ν.value p v ≤ ‖sectionCoordinates.symm.toContinuousLinearMap‖ * ‖v‖ := by
    let w : B := lp.single ⊤ p v
    have hh := hNuCoordinatesLe (sectionCoordinates.symm w) p
    rw [sectionCoordinates.apply_symm_apply] at hh
    simp only [w, lp.single_apply_self] at hh
    apply hh.trans
    have hn := sectionCoordinates.symm.toContinuousLinearMap.le_opNorm w
    change ‖sectionCoordinates.symm w‖ ≤ _ at hn
    simpa only [w, lp.norm_single (by simp : (0 : ENNReal) < ⊤)] using hn
  have hStableMetricContraction (r₀ : ℝ) (hr₀ : 0 < r₀) : ∃ κ ε : ℝ, 0 < κ ∧ κ < 1 ∧ 0 < ε ∧
      ∀ x, ∀ hx : x ∈ Λ, ∀ y : M,
        (∀ n : ℕ, dAdapt.dist ((f : M → M)^[n] y) ((f : M → M)^[n] x) < ε) →
        ∃ s : H.stable.fibre ⟨x, hx⟩, ‖s‖ < r₀ ∧
          riemannianExponential hAdapt ⟨x, s.val + (μ ⟨x, hx⟩ s).val⟩ = y ∧
          dAdapt.dist (f y) (f x) ≤ κ * dAdapt.dist y x := by
    let : MetricSpace M := dAdapt.replaceTopology hdTop.symm
    obtain ⟨κ, r, hκ, hκ1, hr, hrq, hcontract⟩ := hNativeTangentContraction
    let D := ‖sectionCoordinates.symm.toContinuousLinearMap‖
    let c := min r₀ (min ρ (min ρnormal (min r (min (1 / 4) b))))
    have hc : 0 < c := by dsimp [c]; positivity
    have hD : 0 ≤ D := norm_nonneg sectionCoordinates.symm.toContinuousLinearMap
    have hDp : 0 < D + 1 := by positivity
    have hc₀ : c ≤ r₀ := min_le_left _ _
    have hcρ : c ≤ ρ := (min_le_right _ _).trans (min_le_left _ _)
    have hcn : c ≤ ρnormal := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
    have hcr : c ≤ r := (min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _)))
    have hcq : c ≤ 1 / 4 := (min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))
    have hcb : c ≤ b := (min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))))
    have hsmall {q : M} (v : TangentSpace 𝓘(ℝ, E) q) (hv : ‖v‖ < c / (D + 1)) :
        ‖v‖ < c ∧ D * ‖v‖ < c := by
      have hh : (D + 1) * ‖v‖ < c := by
        simpa only [mul_comm] using (lt_div_iff₀ hDp).mp hv
      constructor
      · nlinarith only [hh, mul_nonneg hD (norm_nonneg v)]
      · nlinarith only [hh, norm_nonneg v]
    obtain ⟨ε, hε, hcover⟩ := compact_uniform_exponential_ball_cover hAdapt Λ H.compact
      (c / (D + 1)) (div_pos hc hDp)
    refine ⟨κ, ε, hκ, hκ1, hε, ?_⟩
    intro x hx y hclose
    let p : ℕ → Λ := Nat.rec ⟨x, hx⟩ (fun _ q ↦ baseEquiv q)
    have hp (n : ℕ) : (p n).val = (f : M → M)^[n] x := by
      induction n with
      | zero => rfl
      | succ n ih =>
        change f (p n).val = (f : M → M)^[n + 1] x
        rw [Function.iterate_succ_apply', ih]
    have hcovered (n : ℕ) := hcover (p n).val (p n).property ((f : M → M)^[n] y) (by
      change dAdapt.dist (p n).val ((f : M → M)^[n] y) < ε
      rw [hp]
      simpa only [dAdapt.dist_comm] using hclose n)
    choose v hvnorm hvdom hvexp using hcovered
    have hvl (n : ℕ) : L (p n).val ((f : M → M)^[n] y) = v n := by
      rw [← hvexp n]
      exact (hL (p n).val (p n).property (v n) ((hsmall _ (hvnorm n)).1.trans_le hcρ)).2
    have hrec (n : ℕ) : G (p n) (v n) =
        (lp.single ⊤ (p (n + 1)) (v (n + 1)) : B) (baseEquiv (p n)) := by
      have he := hExp (p n) (v n) ((hNuOrdinary (p n) (v n)).trans
        ((hsmall _ (hvnorm n)).2.le.trans hcb))
      rw [show baseEquiv (p n) = p (n + 1) from rfl, lp.single_apply_self]
      have hh := he.2.2.2.1
      change G (p n) (v n) = L (f (p n).val) (f (riemannianExponential hAdapt ⟨(p n).val, v n⟩)) at hh
      rw [hvexp n, ← Function.iterate_succ_apply' (f : M → M) n y] at hh
      exact hh.trans (hvl (n + 1))
    have hcapture := hCaptureNative p (fun _ ↦ rfl) v
      (fun n ↦ (hsmall _ (hvnorm n)).2.trans_le hcq) hrec
    let s : H.stable.fibre (p 0) := (H.stable.fibre (p 0)).projectionOnto
      (H.unstable.fibre (p 0)) (H.complementary (p 0)) (v 0)
    have hsc : ‖s‖ < c := by
      have hh : ‖s‖ ≤ ν.value (p 0) (v 0) := by
        rw [hν]
        change ‖s.val‖ ≤ _
        rw [show s.val =
          (H.stable.fibre (p 0)).projection (H.unstable.fibre (p 0)) (H.complementary (p 0)) (v 0)
          from Submodule.coe_projectionOnto_apply _ _]
        exact le_max_left _ _
      exact (hh.trans (hNuOrdinary (p 0) (v 0))).trans_lt
        (hsmall _ (hvnorm 0)).2
    have hs : ‖s‖ < r := hsc.trans_le hcr
    have hgraph : s.val + (μ (p 0) s).val = v 0 := by
      have hsum := Submodule.projection_add_projection_eq_self (H.complementary (p 0)) (v 0)
      rw [hcapture] at hsum
      simpa only [s, Submodule.coe_projectionOnto_apply] using hsum
    have htan := hcontract (p 0) s hs
    rw [hgraph] at htan
    have hg : G (p 0) (v 0) = v 1 := by
      have hh := hrec 0
      change G (p 0) (v 0) = (lp.single ⊤ (p 1) (v 1) : B) (p 1) at hh
      exact hh.trans (lp.single_apply_self
        (E := fun q : Λ ↦ TangentSpace 𝓘(ℝ, E) q.val) ⊤ (p 1) (v 1))
    rw [hg] at htan
    have hd0 := hNormalMetric (p 0) (v 0) ((hsmall _ (hvnorm 0)).1.le.trans hcn)
    have hd1 := hNormalMetric (p 1) (v 1) ((hsmall _ (hvnorm 1)).1.le.trans hcn)
    rw [hvexp 0] at hd0
    rw [hvexp 1] at hd1
    change dAdapt.dist x y = ‖v 0‖ at hd0
    change dAdapt.dist (f x) (f y) = ‖v 1‖ at hd1
    refine ⟨s, hsc.trans_le hc₀, ?_, ?_⟩
    · change riemannianExponential hAdapt ⟨(p 0).val, s.val + (μ (p 0) s).val⟩ = y
      rw [hgraph]
      exact hvexp 0
    · rw [dAdapt.dist_comm (f y) (f x), dAdapt.dist_comm y x, hd0, hd1]
      exact htan
  refine ⟨μ, hμzero, hμsmallSlope, ?_, hStableMetricContraction⟩
  obtain ⟨κ, r, hκ, hκ1, hr, hrq, hstep⟩ := hNativeGraphGeometricStep
  refine ⟨κ, r, hκ, hκ1, hr, hrq, ?_⟩
  intro p s hs
  refine ⟨hNormalMetric p _ (hstep p s hs).1, ?_⟩
  let : MetricSpace M := dAdapt.replaceTopology hdTop.symm
  let b : (q : Λ) → H.stable.fibre q → M := fun q v ↦
    riemannianExponential hAdapt ⟨q.val, v.val + (μ q v).val⟩
  have hmetricStep (q : Λ) (v : H.stable.fibre q) (hv : ‖v‖ < r) :
      ∃ t : H.stable.fibre (baseEquiv q), ‖t‖ < r ∧
        dist (b (baseEquiv q) t) (baseEquiv q).val ≤ κ * dist (b q v) q.val ∧
        f (b q v) = b (baseEquiv q) t := by
    obtain ⟨hn, t, ht, htr, htc, he⟩ := hstep q v hv
    refine ⟨t, htr, ?_, he⟩
    change dAdapt.dist (b (baseEquiv q) t) (baseEquiv q).val ≤ κ * dAdapt.dist (b q v) q.val
    rw [dAdapt.dist_comm (b (baseEquiv q) t) _, dAdapt.dist_comm (b q v) _,
      hNormalMetric q _ hn, hNormalMetric (baseEquiv q) _ (hstep (baseEquiv q) t htr).1]
    exact htc
  exact native_graph_orbit_metric_g9 (f : M → M) baseEquiv (fun q : Λ ↦ q.val)
    (fun _ ↦ rfl) b κ r hκ.le hmetricStep p s hs

/-- Original-map local product structure for a locally maximal compact hyperbolic set.

Sources: Hirsch–Pugh (1969), Theorem 3.1 p.148; Shub, Global Stability (1987),
pp.72–78; HPS, Invariant Manifolds (1977), Corollary 5.4 and Theorem 5.5,
pp.60–63; Bowen, Markov Partitions, Fact 1 pp.726–727. The metric preparation
uses the explicitly imported smooth adapted-metric and componentwise length
metric theorems. The native normal-distance comparison uses the Gauss lemma
and the first-exit argument in `RadialGaussLengthG9`.

Proof. Choose the final smooth adapted Riemannian tensor and its strict
one-step tangent contraction constant. On each connected component use its
actual Riemannian length distance, then the compatible componentwise metric
construction. Its topology is the original topology and its distance agrees
with the original tensor's length distance on every component.

Apply `native_stable_graph_data_g9` first to f and then to its inverse with
the stable and unstable subbundles exchanged. This theorem constructs the
bounded-section splitting over the original compact set, binds the actual
cutoff exponential lift to HPS Corollary 5.4, and proves its graph is
fibrewise. The invariant graph derivative at zero vanishes by the strict
linear contraction inequality. Its C1 regularity therefore supplies uniform
arbitrarily small fibre slopes on positive native balls. Graph invariance
retains a smaller native core at every iterate. The small slope and adapted
tangent estimates give strict contraction of the full tangent graph vector.
The native Gauss/first-exit normal-distance theorem identifies its norm with
the actual metric distance and proves all forward orbit estimates; the
inverse construction gives the backward estimates.

The same section-graph capture theorem applies to any ambient orbit staying
uniformly close to a center orbit. The compact exponential-ball covering
lemma lifts every time of that orbit to an arbitrarily small native vector.
The original exponential inverse identities identify consecutive lifted
vectors with the actual nonlinear lift. Inserting these vectors as singleton
sections gives the bounded HPS orbit and hence native graph membership.
Consequently the final metric contracts once for every sufficiently close
forward pair centered in the invariant set, and likewise backward.

Take one quarter of the smaller of these two capture radii. For every smaller
plaque radius gamma, any two points of the same closed gamma plaque stay at
distance at most 2 gamma at every future time. Rebase one as the center in
the preceding estimate, then iterate. This proves the pair contraction
assertions, including all n and equality-boundary plaque points.

For existence, choose gamma also smaller than a uniform metric neighborhood
of the compact invariant set inside its isolating open neighborhood. Choose
a native graph radius below gamma and both retained core radii. The theorem
`native_small_graph_intersection` intersects the original exponential graphs
for nearby centers with parameters and full tangent graph vectors inside
that radius. Its proof uses continuous finite frames, the actual local
exponential two-point identity approximation, and a contraction on one fixed
closed product ball; no joint regularity of the native graph family is
assumed. The relative open center neighborhoods cover the compact diagonal.
A thickening of that diagonal gives a uniform positive closed-pair radius.
The resulting point stays within gamma of a forward center orbit and a
backward center orbit. Every integer iterate therefore belongs to the
original isolating neighborhood; local maximality places the point in the
original invariant set.

For uniqueness, two such intersection points have complete integer orbits
at distance at most 2 gamma. Apply the forward center contraction n times
starting at time minus n. Their present distance is at most
(2 gamma) times kappa to the n, hence is zero. Finally restrict the original
homeomorphism to the compact invariant set. Each finite-time closed distance
inequality is closed in the parameter and candidate intersection. The unique
intersection relation is therefore a closed graph with compact range, so
its selected bracket is continuous. These arguments include the empty
invariant set and zero-rank summands without extra hypotheses. -/
theorem hirschPughHyperbolicSetFactOne
    [FiniteDimensional ℝ E] [T2Space M] [CompactSpace M]
    (f : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞) (Λ : Set M)
    (H : HyperbolicSetFactOneDatum f Λ) :
    ∃ (h : Bundle.ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E
        (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x))
      (a : ℝ) (d : MetricSpace M) (κ γ ε₀ : ℝ),
      a < 1 ∧
      (∀ (x : Λ) (v : TangentSpace 𝓘(ℝ, E) (x : M)), v ∈ H.stable.fibre x →
        hyperbolicRiemannianNorm h (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) f x v) ≤
          a * hyperbolicRiemannianNorm h v) ∧
      (∀ (x : Λ) (v : TangentSpace 𝓘(ℝ, E) (x : M)), v ∈ H.unstable.fibre x →
        hyperbolicRiemannianNorm h (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) f.symm x v) ≤
          a * hyperbolicRiemannianNorm h v) ∧
      d.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace =
        (inferInstance : TopologicalSpace M) ∧
      (∀ x : M, ∃ V : Set M, IsOpen V ∧ x ∈ V ∧
        ∀ y ∈ V, ∀ z ∈ V,
          ENNReal.ofReal (d.dist y z) = piecewiseSmoothRiemannianEDist h y z) ∧
      0 < κ ∧ κ < 1 ∧ 0 < γ ∧ 0 < ε₀ ∧
      (∀ x ∈ Λ, ∀ y ∈ hyperbolicClosedStablePlaque f Λ d γ x,
        ∀ z ∈ hyperbolicClosedStablePlaque f Λ d γ x, ∀ n : ℕ,
          d.dist ((f : M → M)^[n] y) ((f : M → M)^[n] z) ≤ κ ^ n * d.dist y z) ∧
      (∀ x ∈ Λ, ∀ y ∈ hyperbolicClosedUnstablePlaque f Λ d γ x,
        ∀ z ∈ hyperbolicClosedUnstablePlaque f Λ d γ x, ∀ n : ℕ,
          d.dist ((f.symm : M → M)^[n] y) ((f.symm : M → M)^[n] z) ≤
            κ ^ n * d.dist y z) ∧
      ∃ bracket : hyperbolicClosedPairDomain Λ d ε₀ → Λ,
        Continuous bracket ∧
        ∀ p : hyperbolicClosedPairDomain Λ d ε₀,
          hyperbolicClosedStablePlaque f Λ d γ p.val.1 ∩
            hyperbolicClosedUnstablePlaque f Λ d γ p.val.2 = {(bracket p : M)} := by
  classical
  -- The adapted metric provider carries the original finite-energy construction.
  have hadapt := smooth_adapted_metric_of_hyperbolic_datum f Λ H
  obtain ⟨hAdapt, aAdapt, haAdapt, hsAdapt, huAdapt⟩ := hadapt
  let : Bundle.RiemannianBundle (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x) :=
    ⟨hAdapt.toRiemannianMetric⟩
  let : (x : M) → NormedAddCommGroup (TangentSpace 𝓘(ℝ, E) x) := fun x ↦ inferInstance
  let : (x : M) → InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, E) x) := fun x ↦ inferInstance
  obtain ⟨dAdapt, hdTop, hdComp⟩ :=
    Dynamics.ManningOriginalBasicSetSignedTraceG7.MetricAdapter.exists_componentwise_length_metric
      hAdapt
  let : LocallyConnectedSpace M := ChartedSpace.locallyConnectedSpace E M
  have hdLocal : ∀ x : M, ∃ V : Set M, IsOpen V ∧ x ∈ V ∧
      ∀ y ∈ V, ∀ z ∈ V,
        ENNReal.ofReal (dAdapt.dist y z) = piecewiseSmoothRiemannianEDist hAdapt y z := by
    intro x
    refine ⟨connectedComponent x, isOpen_connectedComponent, mem_connectedComponent, ?_⟩
    intro y hy z hz
    have hzy : z ∈ connectedComponent y := by
      rw [← connectedComponent_eq hy]
      exact hz
    have heq := (hdComp y z hzy).trans
      (riemannianEDist_eq_piecewiseSmoothRiemannianEDist hAdapt y z)
    simpa only [@edist_dist M dAdapt.toPseudoMetricSpace] using heq
  obtain ⟨μs, hμszero, hμsSlope, hμsStep, hμsCapture⟩ :=
    native_stable_graph_data_g9 f Λ H hAdapt aAdapt haAdapt hsAdapt huAdapt dAdapt hdTop hdComp
  let Hrev := reverse_hyperbolic_datum_g9 f Λ H
  obtain ⟨μu, hμuzero, hμuSlope, hμuStep, hμuCapture⟩ :=
    native_stable_graph_data_g9 f.symm Λ Hrev hAdapt aAdapt haAdapt huAdapt hsAdapt dAdapt hdTop hdComp
  suffices hgeometry : ∃ κ γ ε₀ : ℝ,
      0 < κ ∧ κ < 1 ∧ 0 < γ ∧ 0 < ε₀ ∧
      (∀ x ∈ Λ, ∀ y ∈ hyperbolicClosedStablePlaque f Λ dAdapt (2 * γ) x,
        dAdapt.dist (f y) (f x) ≤ κ * dAdapt.dist y x) ∧
      (∀ x ∈ Λ, ∀ y ∈ hyperbolicClosedUnstablePlaque f Λ dAdapt (2 * γ) x,
        dAdapt.dist (f.symm y) (f.symm x) ≤ κ * dAdapt.dist y x) ∧
      (∀ p : hyperbolicClosedPairDomain Λ dAdapt ε₀, ∃! z : Λ,
        (z : M) ∈ hyperbolicClosedStablePlaque f Λ dAdapt γ p.val.1 ∩
          hyperbolicClosedUnstablePlaque f Λ dAdapt γ p.val.2) by
    obtain ⟨κ, γ, ε₀, hκ, hκ1, hγ, hε₀, hcenterS, hcenterU, hintersection⟩ := hgeometry
    let : MetricSpace M := dAdapt.replaceTopology hdTop.symm
    let : CompactSpace Λ := isCompact_iff_compactSpace.mp H.compact
    have hcontractS : ∀ x ∈ Λ, ∀ y ∈ hyperbolicClosedStablePlaque f Λ dAdapt γ x,
        ∀ z ∈ hyperbolicClosedStablePlaque f Λ dAdapt γ x, ∀ n : ℕ,
          dAdapt.dist ((f : M → M)^[n] y) ((f : M → M)^[n] z) ≤
            κ ^ n * dAdapt.dist y z := by
      intro x _ y hy z hz n
      exact closed_orbit_plaque_pair_contraction (f : M → M) Λ H.forward_mem κ γ hκ.le
        (fun x hx y hy hclose ↦ hcenterS x hx y ⟨hy, hclose⟩)
        hy.1 hz.1 hy.2 hz.2 n
    have hcontractU : ∀ x ∈ Λ, ∀ y ∈ hyperbolicClosedUnstablePlaque f Λ dAdapt γ x,
        ∀ z ∈ hyperbolicClosedUnstablePlaque f Λ dAdapt γ x, ∀ n : ℕ,
          dAdapt.dist ((f.symm : M → M)^[n] y) ((f.symm : M → M)^[n] z) ≤
            κ ^ n * dAdapt.dist y z := by
      intro x _ y hy z hz n
      exact closed_orbit_plaque_pair_contraction (f.symm : M → M) Λ H.backward_mem κ γ hκ.le
        (fun x hx y hy hclose ↦ hcenterU x hx y ⟨hy, hclose⟩)
        hy.1 hz.1 hy.2 hz.2 n
    let F : Λ ≃ₜ Λ :=
      { toFun := fun x ↦ ⟨f x, H.forward_mem x.property⟩
        invFun := fun x ↦ ⟨f.symm x, H.backward_mem x.property⟩
        left_inv := fun x ↦ Subtype.ext (f.symm_apply_apply x)
        right_inv := fun x ↦ Subtype.ext (f.apply_symm_apply x)
        continuous_toFun := (f.continuous.comp continuous_subtype_val).subtype_mk _
        continuous_invFun := (f.symm.continuous.comp continuous_subtype_val).subtype_mk _ }
    have hFiter (n : ℕ) (x : Λ) :
        (((F : Λ → Λ)^[n] x : Λ) : M) = (f : M → M)^[n] x := by
      induction n with
      | zero => rfl
      | succ n ih =>
        rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
        change f (↑((F : Λ → Λ)^[n] x)) = f ((f : M → M)^[n] ↑x)
        exact congrArg f ih
    have hFback (n : ℕ) (x : Λ) :
        (((F.symm : Λ → Λ)^[n] x : Λ) : M) = (f.symm : M → M)^[n] x := by
      induction n with
      | zero => rfl
      | succ n ih =>
        rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
        change f.symm (↑((F.symm : Λ → Λ)^[n] x)) = f.symm ((f.symm : M → M)^[n] ↑x)
        exact congrArg f.symm ih
    let D := hyperbolicClosedPairDomain Λ dAdapt ε₀
    let c₁ : D → Λ := fun p ↦ ⟨p.val.1, p.property.1⟩
    let c₂ : D → Λ := fun p ↦ ⟨p.val.2, p.property.2.1⟩
    have hc₁ : Continuous c₁ :=
      (continuous_fst.comp continuous_subtype_val).subtype_mk _
    have hc₂ : Continuous c₂ :=
      (continuous_snd.comp continuous_subtype_val).subtype_mk _
    have hrel (p : D) (z : Λ) :
        ((∀ n : ℕ, dist ((F : Λ → Λ)^[n] z) ((F : Λ → Λ)^[n] (c₁ p)) ≤ γ) ∧
         (∀ n : ℕ, dist ((F.symm : Λ → Λ)^[n] z) ((F.symm : Λ → Λ)^[n] (c₂ p)) ≤ γ)) ↔
        (z : M) ∈ hyperbolicClosedStablePlaque f Λ dAdapt γ p.val.1 ∩
          hyperbolicClosedUnstablePlaque f Λ dAdapt γ p.val.2 := by
      simp only [Subtype.dist_eq, hFiter, hFback, c₁, c₂,
        hyperbolicClosedStablePlaque, hyperbolicClosedUnstablePlaque,
        Set.mem_inter_iff, Set.mem_ofPred_eq, z.property, true_and]
    have hunique (p : D) : ∃! z : Λ,
        (∀ n : ℕ, dist ((F : Λ → Λ)^[n] z) ((F : Λ → Λ)^[n] (c₁ p)) ≤ γ) ∧
        (∀ n : ℕ, dist ((F.symm : Λ → Λ)^[n] z) ((F.symm : Λ → Λ)^[n] (c₂ p)) ≤ γ) := by
      exact (existsUnique_congr (fun z ↦ hrel p z)).mpr (hintersection p)
    obtain ⟨bracket, hbracket, hspec⟩ :=
      continuous_unique_closed_orbit_intersection F c₁ c₂ hc₁ hc₂ γ hunique
    refine ⟨hAdapt, aAdapt, dAdapt, κ, γ, ε₀, haAdapt, hsAdapt, huAdapt, hdTop,
      hdLocal, hκ, hκ1, hγ, hε₀, hcontractS, hcontractU, bracket, hbracket, ?_⟩
    intro p
    ext z
    constructor
    · intro hz
      have hzΛ : z ∈ Λ := hz.1.1
      exact congrArg Subtype.val ((hspec p ⟨z, hzΛ⟩).mp ((hrel p ⟨z, hzΛ⟩).mpr hz))
    · intro hz
      have hz' : z = (bracket p : M) := hz
      rw [hz']
      exact (hrel p (bracket p)).mp ((hspec p (bracket p)).mpr rfl)
  let : MetricSpace M := dAdapt.replaceTopology hdTop.symm
  obtain ⟨κs, εs, hκs, hκs1, hεs, hcs⟩ := hμsCapture 1 zero_lt_one
  obtain ⟨κu, εu, hκu, hκu1, hεu, hcu⟩ := hμuCapture 1 zero_lt_one
  let κ := max κs κu
  have hκ : 0 < κ := hκs.trans_le (le_max_left _ _)
  have hκ1 : κ < 1 := max_lt hκs1 hκu1
  let τ := min εs εu / 4
  have hτ : 0 < τ := div_pos (lt_min hεs hεu) (by norm_num)
  have hS (γ : ℝ) (hγ : γ ≤ τ) (x : M) (hx : x ∈ Λ) (y : M)
      (hy : ∀ n : ℕ, dAdapt.dist ((f : M → M)^[n] y) ((f : M → M)^[n] x) ≤ 2 * γ) :
      dAdapt.dist (f y) (f x) ≤ κ * dAdapt.dist y x := by
    have hsmall : 2 * γ < εs := by
      have hh : γ * 4 ≤ min εs εu := (le_div_iff₀ (by norm_num : (0 : ℝ) < 4)).mp hγ
      nlinarith only [hh, min_le_left εs εu, hεs]
    obtain ⟨s, hs, he, hc⟩ := hcs x hx y (fun n ↦ (hy n).trans_lt hsmall)
    exact hc.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) dist_nonneg)
  have hU (γ : ℝ) (hγ : γ ≤ τ) (x : M) (hx : x ∈ Λ) (y : M)
      (hy : ∀ n : ℕ, dAdapt.dist ((f.symm : M → M)^[n] y) ((f.symm : M → M)^[n] x) ≤ 2 * γ) :
      dAdapt.dist (f.symm y) (f.symm x) ≤ κ * dAdapt.dist y x := by
    have hsmall : 2 * γ < εu := by
      have hh : γ * 4 ≤ min εs εu := (le_div_iff₀ (by norm_num : (0 : ℝ) < 4)).mp hγ
      nlinarith only [hh, min_le_right εs εu, hεu]
    obtain ⟨s, hs, he, hc⟩ := hcu x hx y (fun n ↦ (hy n).trans_lt hsmall)
    exact hc.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) dist_nonneg)
  suffices hexistence : ∃ γ ε₀ : ℝ, 0 < γ ∧ γ ≤ τ ∧ 0 < ε₀ ∧
      ∀ p : hyperbolicClosedPairDomain Λ dAdapt ε₀, ∃ z : Λ,
        (z : M) ∈ hyperbolicClosedStablePlaque f Λ dAdapt γ p.val.1 ∩
          hyperbolicClosedUnstablePlaque f Λ dAdapt γ p.val.2 by
    obtain ⟨γ, ε₀, hγ, hγτ, hε₀, hex⟩ := hexistence
    refine ⟨κ, γ, ε₀, hκ, hκ1, hγ, hε₀, ?_, ?_, ?_⟩
    · intro x hx y hy
      exact hS γ hγτ x hx y hy.2
    · intro x hx y hy
      exact hU γ hγτ x hx y hy.2
    · intro p
      obtain ⟨z, hz⟩ := hex p
      refine ⟨z, hz, ?_⟩
      intro w hw
      apply Subtype.ext
      exact closed_orbit_intersection_subsingleton f.toHomeomorph Λ H.forward_mem H.backward_mem
        κ γ hκ.le hκ1 (fun x hx y _ hy ↦ hS γ hγτ x hx y hy)
        w.property z.property hw.1.2 hz.1.2 hw.2.2 hz.2.2
  let : CompactSpace Λ := isCompact_iff_compactSpace.mp H.compact
  obtain ⟨ζ, hζ, hiso⟩ := H.compact.exists_thickening_subset_open H.isolating_open H.subset_isolating
  let γ := min τ (ζ / 2)
  have hγ : 0 < γ := lt_min hτ (half_pos hζ)
  have hγτ : γ ≤ τ := min_le_left _ _
  have hγζ : γ < ζ := (min_le_right _ _).trans_lt (by linarith only [hζ])
  obtain ⟨κsNative, rs, hκsNative, hκsNative1, hrs, _, hstepS⟩ := hμsStep
  obtain ⟨κuNative, ru, hκuNative, hκuNative1, hru, _, hstepU⟩ := hμuStep
  let ρ := min γ (min rs ru)
  have hρ : 0 < ρ := lt_min hγ (lt_min hrs hru)
  have hlocal := native_small_graph_intersection hAdapt H.stable H.unstable H.complementary
    μs μu hμszero hμuzero
    (fun η hη ↦ by obtain ⟨r, hr, _, hl⟩ := hμsSlope η hη; exact ⟨r, hr, hl⟩)
    (fun η hη ↦ by obtain ⟨r, hr, _, hl⟩ := hμuSlope η hη; exact ⟨r, hr, hl⟩)
  choose O hO hpO hinter using fun p : Λ ↦ hlocal p ρ hρ
  let A : Set (Λ × Λ) := ⋃ p : Λ, O p ×ˢ O p
  have hA : IsOpen A := isOpen_iUnion (fun p ↦ (hO p).prod (hO p))
  have hdiag : (fun p : Λ ↦ (p, p)) '' univ ⊆ A := by
    rintro _ ⟨p, _, rfl⟩
    exact mem_iUnion.mpr ⟨p, hpO p, hpO p⟩
  obtain ⟨ε, hε, hpair⟩ :=
    (isCompact_univ.image (continuous_id.prodMk continuous_id)).exists_thickening_subset_open hA hdiag
  refine ⟨γ, ε / 2, hγ, hγτ, half_pos hε, ?_⟩
  intro pair
  let x : Λ := ⟨pair.val.1, pair.property.1⟩
  let y : Λ := ⟨pair.val.2, pair.property.2.1⟩
  have hxy : (x, y) ∈ A := by
    apply hpair
    rw [Metric.mem_thickening_iff]
    refine ⟨(x, x), ⟨x, mem_univ _, rfl⟩, ?_⟩
    have hh : dist x y ≤ ε / 2 := pair.property.2.2
    have hh' : dist x y < ε := hh.trans_lt (by linarith only [hε])
    simpa only [Prod.dist_eq, dist_self, max_eq_right dist_nonneg, dist_comm] using hh'
  obtain ⟨p, hp⟩ := mem_iUnion.mp hxy
  obtain ⟨s, u, hs, hu, hsv, huv, he⟩ := hinter p x hp.1 y hp.2
  have hsrs : ‖s‖ < rs := hs.trans_le ((min_le_right γ (min rs ru)).trans (min_le_left rs ru))
  have huru : ‖u‖ < ru := hu.trans_le ((min_le_right γ (min rs ru)).trans (min_le_right rs ru))
  let z := riemannianExponential hAdapt ⟨x.val, s.val + (μs x s).val⟩
  have hzU : z = riemannianExponential hAdapt ⟨y.val, u.val + (μu y u).val⟩ := he
  have hzSdist : dAdapt.dist z x.val < γ := by
    rw [show dAdapt.dist z x.val = dAdapt.dist x.val z from dist_comm _ _, (hstepS x s hsrs).1]
    exact hsv.trans_le (min_le_left _ _)
  have hzUdist : dAdapt.dist z y.val < γ := by
    rw [hzU, show dAdapt.dist
      (riemannianExponential hAdapt ⟨y.val, u.val + (μu y u).val⟩) y.val = dAdapt.dist y.val
      (riemannianExponential hAdapt ⟨y.val, u.val + (μu y u).val⟩) from dist_comm _ _,
      (hstepU y u huru).1]
    exact huv.trans_le (min_le_left _ _)
  have hzS (n : ℕ) : dAdapt.dist ((f : M → M)^[n] z) ((f : M → M)^[n] x.val) ≤ γ := by
    exact ((hstepS x s hsrs).2 n).trans
      ((mul_le_mul_of_nonneg_right (pow_le_one₀ hκsNative.le hκsNative1.le) dist_nonneg).trans
        (by simpa only [one_mul] using hzSdist.le))
  have hzU (n : ℕ) : dAdapt.dist ((f.symm : M → M)^[n] z) ((f.symm : M → M)^[n] y.val) ≤ γ := by
    rw [hzU]
    exact ((hstepU y u huru).2 n).trans
      ((mul_le_mul_of_nonneg_right (pow_le_one₀ hκuNative.le hκuNative1.le) dist_nonneg).trans
        (by simpa only [one_mul, ← hzU] using hzUdist.le))
  have hclose_mem (v w : M) (hw : w ∈ Λ) (hd : dAdapt.dist v w ≤ γ) : v ∈ H.isolatingNeighborhood := by
    apply hiso
    rw [Metric.mem_thickening_iff]
    exact ⟨w, hw, hd.trans_lt hγζ⟩
  have hpow (F : M ≃ₜ M) (n : ℕ) (v : M) : (F ^ n) v = (F : M → M)^[n] v := by
    induction n with
    | zero => rfl
    | succ n ih => rw [pow_succ', Homeomorph.mul_apply, Function.iterate_succ_apply', ih]
  have hzΛ : z ∈ Λ := (H.locally_maximal z).mpr (by
    intro k
    obtain ⟨n, rfl | rfl⟩ := k.eq_nat_or_neg
    · unfold hyperbolicIntegerOrbit
      rw [zpow_natCast, hpow]
      exact hclose_mem _ _ (H.forward_mem.iterate n x.property) (hzS n)
    · unfold hyperbolicIntegerOrbit
      rw [zpow_neg, ← inv_zpow, zpow_natCast]
      rw [hpow]
      exact hclose_mem _ _ (H.backward_mem.iterate n y.property) (hzU n))
  exact ⟨⟨z, hzΛ⟩, ⟨hzΛ, hzS⟩, ⟨hzΛ, hzU⟩⟩

end

end HolomorphicAnosov

