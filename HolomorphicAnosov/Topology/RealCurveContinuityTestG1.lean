import Mathlib.Topology.Category.LightProfinite.Sequence
import Mathlib.Topology.TietzeExtension
import Mathlib.Topology.Sequences
import Mathlib.Topology.Path
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.OpenPartialHomeomorph.Basic

/-! A curve test for continuity in the finite dimensional transverse coordinates
used in Ghys Proposition 3.1, pp.590–593. -/

open Filter _root_.Topology OnePoint
namespace HolomorphicAnosov
universe v w

/-- A convergent sequence in a Tietze extension space lies on a continuous real
curve, with its limit at time zero and its nth value at time `1/(n+1)`.
Source: Munkres, Topology, §35, Tietze extension theorem. The compact space
`ℕ ∪ {∞}` maps continuously to the sequence and its limit. Its standard closed
embedding in the real line sends infinity to zero and n to `1/(n+1)`.
Tietze extension along this closed embedding gives the required curve. -/
theorem convergent_sequence_on_real_curve_g1
    {X : Type v} [TopologicalSpace X] [TietzeExtension.{0, v} X]
    (u : ℕ → X) (x : X) (hu : Tendsto u atTop (𝓝 x)) :
    ∃ c : C(ℝ, X), c 0 = x ∧ ∀ n : ℕ, c (1 / (n + 1 : ℝ)) = u n := by
  obtain ⟨c, hc⟩ := (OnePoint.continuousMapMkNat u x hu).exists_extension
    LightProfinite.isClosedEmbedding_natUnionInftyEmbedding
  refine ⟨c, ?_, ?_⟩
  · exact congrArg (fun g : C(OnePoint ℕ, X) ↦ g ∞) hc
  · intro n
    exact congrArg (fun g : C(OnePoint ℕ, X) ↦ g (OnePoint.some n)) hc

/-- On a sequential Tietze extension space (in particular a finite product of
real lines), continuity can be tested on continuous real curves.
Source: Munkres, Topology, §21 sequence lemma and §35 Tietze extension theorem.
Given a sequence converging to x, extend it to a real curve through x using the
preceding theorem. Curve continuity carries the times `1/(n+1)` tending to zero
to convergence of the image sequence. Sequentiality then gives continuity. -/
theorem continuous_of_real_curve_test_g1
    {X : Type v} {Y : Type w} [TopologicalSpace X] [SequentialSpace X]
    [TietzeExtension.{0, v} X]
    [TopologicalSpace Y] (f : X → Y)
    (hf : ∀ c : C(ℝ, X), Continuous (f ∘ c)) : Continuous f := by
  apply SeqContinuous.continuous
  intro u x hu
  obtain ⟨c, hc0, hcu⟩ := convergent_sequence_on_real_curve_g1 u x hu
  have ht := ((hf c).tendsto 0).comp tendsto_one_div_add_atTop_nhds_zero_nat
  simpa only [Function.comp_def, hc0, hcu] using ht

/-- Testing all paths suffices to test every continuous real curve locally:
restrict a real curve to the interval of radius one about the tested time,
then use the affine parameter and the interval retraction. -/
theorem continuous_real_curve_of_path_test_g1
    {X : Type v} {Y : Type w} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) (hf : ∀ {a b : X} (p : Path a b), Continuous (f ∘ p))
    (c : C(ℝ, X)) : Continuous (f ∘ c) := by
  rw [continuous_iff_continuousAt]
  intro t
  let p : Path (c (t - 1)) (c (t + 1)) := {
    toFun := fun r ↦ c (t - 1 + 2 * (r : ℝ))
    continuous_toFun := c.continuous.comp (by fun_prop)
    source' := by simp
    target' := by congr 1; norm_num; ring }
  let q : ℝ → unitInterval := fun s ↦ Set.projIcc 0 1 zero_le_one ((s - t + 1) / 2)
  have hq : Continuous q := continuous_projIcc.comp (by fun_prop)
  have he : (f ∘ p ∘ q) =ᶠ[𝓝 t] (f ∘ c) := by
    filter_upwards [Ioo_mem_nhds (show t - 1 < t by linarith)
      (show t < t + 1 by linarith)] with s hs
    have hm : (s - t + 1) / 2 ∈ Set.Icc (0 : ℝ) 1 := by
      constructor <;> linarith [hs.1, hs.2]
    change f (c (t - 1 + 2 * ((Set.projIcc 0 1 zero_le_one ((s - t + 1) / 2) : unitInterval) : ℝ))) = f (c s)
    rw [Set.projIcc_of_mem zero_le_one hm]
    congr 2
    dsimp
    ring
  exact ((hf p).comp hq).continuousAt.congr_of_eventuallyEq he.symm

/-- On a sequential Tietze extension space, a map is continuous if its
composition with every path is continuous. The preceding real-curve test and
the local interval reparametrization prove the claim; no uniform modulus for
the paths is required. -/
theorem continuous_of_path_test_g1
    {X : Type v} {Y : Type w} [TopologicalSpace X] [SequentialSpace X]
    [TietzeExtension.{0, v} X] [TopologicalSpace Y]
    (f : X → Y) (hf : ∀ {a b : X} (p : Path a b), Continuous (f ∘ p)) :
    Continuous f :=
  continuous_of_real_curve_test_g1 f (continuous_real_curve_of_path_test_g1 f hf)

/-- The curve test also permits a simultaneously moving first coordinate.
For a convergent sequence `(zₙ,tₙ)`, interpolate only `tₙ` by a real curve.
The assumed joint continuity along that curve applies to `(zₙ,1/(n+1))`.
This is the local-product continuity step of Ghys Proposition 3.1, pp.592–593. -/
theorem continuous_of_joint_real_curve_test_g1
    {Z : Type*} {X : Type v} {Y : Type w}
    [TopologicalSpace Z] [TopologicalSpace X] [TopologicalSpace Y]
    [SequentialSpace (Z × X)] [TietzeExtension.{0, v} X]
    (f : Z × X → Y)
    (hf : ∀ c : C(ℝ, X), Continuous (fun p : Z × ℝ ↦ f (p.1, c p.2))) :
    Continuous f := by
  apply SeqContinuous.continuous
  intro u x hu
  have ht : Tendsto (fun n ↦ (u n).2) atTop (𝓝 x.2) :=
    continuous_snd.continuousAt.tendsto.comp hu
  obtain ⟨c, hc0, hcu⟩ := convergent_sequence_on_real_curve_g1 _ _ ht
  have hz : Tendsto (fun n ↦ (u n).1) atTop (𝓝 x.1) :=
    continuous_fst.continuousAt.tendsto.comp hu
  have h := ((hf c).tendsto (x.1, 0)).comp
    (hz.prodMk_nhds tendsto_one_div_add_atTop_nhds_zero_nat)
  simpa only [Function.comp_def, hc0, hcu, Prod.mk.eta] using h

/-- Joint continuity along every path in the second coordinate detects full
product continuity. The real-curve test applies after restricting each real
curve near a tested time to a compact interval. -/
theorem continuous_of_joint_path_test_g1
    {Z : Type*} {X : Type v} {Y : Type w}
    [TopologicalSpace Z] [TopologicalSpace X] [TopologicalSpace Y]
    [SequentialSpace (Z × X)] [TietzeExtension.{0, v} X]
    (f : Z × X → Y)
    (hf : ∀ {a b : X} (p : Path a b),
      Continuous (fun q : Z × unitInterval ↦ f (q.1,p q.2))) :
    Continuous f := by
  apply continuous_of_joint_real_curve_test_g1 f
  intro c
  rw [continuous_iff_continuousAt]
  rintro ⟨z,t⟩
  let p : Path (c (t - 1)) (c (t + 1)) := {
    toFun := fun r ↦ c (t - 1 + 2 * (r : ℝ))
    continuous_toFun := c.continuous.comp (by fun_prop)
    source' := by simp
    target' := by congr 1; norm_num; ring }
  let q : ℝ → unitInterval := fun s ↦ Set.projIcc 0 1 zero_le_one ((s - t + 1) / 2)
  have hq : Continuous q := continuous_projIcc.comp (by fun_prop)
  have hcont := (hf p).comp (continuous_fst.prodMk (hq.comp continuous_snd))
  apply hcont.continuousAt.congr_of_eventuallyEq
  filter_upwards [continuous_snd.continuousAt.preimage_mem_nhds
    (Ioo_mem_nhds (show t - 1 < t by linarith) (show t < t + 1 by linarith))] with a ha
  have hm : (a.2 - t + 1) / 2 ∈ Set.Icc (0 : ℝ) 1 := by
    constructor <;> linarith [ha.1,ha.2]
  change f (a.1,c a.2) = f (a.1,c (t - 1 + 2 *
    ((Set.projIcc 0 1 zero_le_one ((a.2 - t + 1) / 2) : unitInterval) : ℝ)))
  rw [Set.projIcc_of_mem zero_le_one hm]
  congr 3
  dsimp
  ring

/-- The joint path test is local on an arbitrary open product domain.
A convergent sequence is tested by interpolating only its second coordinate;
near its limit, the interpolating path remains in the prescribed open domain. -/
theorem continuousOn_of_joint_path_test_g1
    {Z : Type*} {X : Type v} {Y : Type w}
    [TopologicalSpace Z] [TopologicalSpace X] [TopologicalSpace Y]
    [FrechetUrysohnSpace (Z × X)] [TietzeExtension.{0, v} X]
    (f : Z × X → Y) (Ω : Set (Z × X)) (hΩ : IsOpen Ω)
    (hf : ∀ {a b : X} (p : Path a b),
      ContinuousOn (fun q : Z × unitInterval ↦ f (q.1,p q.2))
        {q | (q.1,p q.2) ∈ Ω}) : ContinuousOn f Ω := by
  have hreal (c : C(ℝ,X)) (z : Z) (t : ℝ) (hzt : (z,c t) ∈ Ω) :
      ContinuousAt (fun q : Z × ℝ ↦ f (q.1,c q.2)) (z,t) := by
    let p : Path (c (t - 1)) (c (t + 1)) := {
      toFun := fun r ↦ c (t - 1 + 2 * (r : ℝ))
      continuous_toFun := c.continuous.comp (by fun_prop)
      source' := by simp
      target' := by congr 1; norm_num; ring }
    let q : ℝ → unitInterval := fun s ↦ Set.projIcc 0 1 zero_le_one ((s - t + 1) / 2)
    have hq : Continuous q := continuous_projIcc.comp (by fun_prop)
    have hqeq : p (q t) = c t := by
      dsimp [p,q]
      rw [Set.projIcc_of_mem zero_le_one (by constructor <;> linarith)]
      congr 1
      dsimp
      ring
    have hdom : IsOpen {r : Z × unitInterval | (r.1,p r.2) ∈ Ω} :=
      hΩ.preimage (continuous_fst.prodMk (p.continuous.comp continuous_snd))
    have hpt : (z,q t) ∈ {r : Z × unitInterval | (r.1,p r.2) ∈ Ω} := by
      change (z,p (q t)) ∈ Ω
      rwa [hqeq]
    have hcont : ContinuousAt (fun a : Z × ℝ ↦ f (a.1,p (q a.2))) (z,t) :=
      ((hf p).continuousAt (hdom.mem_nhds hpt)).comp (x := (z,t)) (f := fun a : Z × ℝ ↦ (a.1,q a.2)) (g := fun r : Z × unitInterval ↦ f (r.1,p r.2))
        (continuous_fst.prodMk (hq.comp continuous_snd)).continuousAt
    apply hcont.congr_of_eventuallyEq
    filter_upwards [continuous_snd.continuousAt.preimage_mem_nhds
      (Ioo_mem_nhds (show t - 1 < t by linarith) (show t < t + 1 by linarith))] with a ha
    have hm : (a.2 - t + 1) / 2 ∈ Set.Icc (0 : ℝ) 1 := by
      constructor <;> linarith [ha.1,ha.2]
    change f (a.1,c a.2) = f (a.1,c (t - 1 + 2 *
      ((Set.projIcc 0 1 zero_le_one ((a.2 - t + 1) / 2) : unitInterval) : ℝ)))
    rw [Set.projIcc_of_mem zero_le_one hm]
    congr 3
    dsimp
    ring
  intro x hx
  apply ContinuousAt.continuousWithinAt
  rw [ContinuousAt,tendsto_nhds_iff_seq_tendsto]
  intro u hu
  have ht : Tendsto (fun n ↦ (u n).2) atTop (𝓝 x.2) :=
    continuous_snd.continuousAt.tendsto.comp hu
  obtain ⟨c,hc0,hcu⟩ := convergent_sequence_on_real_curve_g1 _ _ ht
  have hz : Tendsto (fun n ↦ (u n).1) atTop (𝓝 x.1) :=
    continuous_fst.continuousAt.tendsto.comp hu
  have h := (hreal c x.1 0 (by simpa only [hc0,Prod.mk.eta] using hx)).tendsto.comp
    (hz.prodMk_nhds tendsto_one_div_add_atTop_nhds_zero_nat)
  simpa only [Function.comp_def,hc0,hcu,Prod.mk.eta] using h

/-- Local complex coordinates in the first variable may depend on the tested
path. A unit disk around each marked point still suffices for the joint path
test, since the inverse coordinate change is continuous on its actual domain. -/
theorem continuousOn_of_local_complex_path_charts_g1
    {Z : Type*} {X : Type v} {Y : Type w}
    [TopologicalSpace Z] [TopologicalSpace X] [TopologicalSpace Y]
    [FrechetUrysohnSpace (Z × X)] [TietzeExtension.{0, v} X]
    (f : Z × X → Y) (Ω : Set (Z × X)) (hΩ : IsOpen Ω)
    (hf : ∀ {a b : X} (p : Path a b) (z : Z),
      ∃ e : OpenPartialHomeomorph Z ℂ,
        z ∈ e.source ∧ e z = 0 ∧ Metric.ball (0 : ℂ) 1 ⊆ e.target ∧
        ContinuousOn (fun q : ℂ × unitInterval ↦ f (e.symm q.1,p q.2))
          ((Metric.ball 0 1 ×ˢ Set.univ) ∩ {q | (e.symm q.1,p q.2) ∈ Ω})) :
    ContinuousOn f Ω := by
  apply continuousOn_of_joint_path_test_g1 f Ω hΩ
  intro a b p
  rintro ⟨z,t⟩ hzt
  obtain ⟨e,hze,he0,het,hcont⟩ := hf p z
  have hez : e.symm 0 = z := by rw [← he0,e.left_inv hze]
  have hmap : ContinuousOn (fun q : ℂ × unitInterval ↦ (e.symm q.1,p q.2))
      (Metric.ball 0 1 ×ˢ Set.univ) :=
    (e.symm.continuousOn.comp continuous_fst.continuousOn (fun q hq ↦ het hq.1)).prodMk
      (p.continuous.comp continuous_snd).continuousOn
  have hopen := hmap.isOpen_inter_preimage (Metric.isOpen_ball.prod isOpen_univ) hΩ
  have hmem : ((0 : ℂ),t) ∈
      (Metric.ball 0 1 ×ˢ Set.univ) ∩ {q | (e.symm q.1,p q.2) ∈ Ω} :=
    ⟨⟨Metric.mem_ball_self (by norm_num),Set.mem_univ _⟩,by change (e.symm 0,p t) ∈ Ω; rw [hez]; exact hzt⟩
  have hchange : ContinuousAt (fun q : Z × unitInterval ↦ (e q.1,q.2)) (z,t) :=
    ((e.continuousOn.continuousAt (e.open_source.mem_nhds hze)).comp continuous_fst.continuousAt).prodMk continuous_snd.continuousAt
  have hat : ContinuousAt (fun q : ℂ × unitInterval ↦ f (e.symm q.1,p q.2)) (e z,t) := by
    rw [he0]
    exact hcont.continuousAt (hopen.mem_nhds hmem)
  have hout := hat.comp (x := (z,t)) (f := fun q : Z × unitInterval ↦ (e q.1,q.2)) hchange
  apply ContinuousAt.continuousWithinAt
  apply hout.congr_of_eventuallyEq
  filter_upwards [continuous_fst.continuousAt.preimage_mem_nhds (e.open_source.mem_nhds hze)]
    with q hq
  change f (q.1,p q.2) = f (e.symm (e q.1),p q.2)
  rw [e.left_inv hq]

end HolomorphicAnosov
