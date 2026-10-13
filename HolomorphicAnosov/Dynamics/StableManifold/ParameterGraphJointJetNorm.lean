import HolomorphicAnosov.Dynamics.StableManifold.FiniteRankAtlasFrameContinuity
import HolomorphicAnosov.Analysis.FrameMultilinearNormContinuity
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphClosedDiscCompactness
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphJointJetCriterion
import Mathlib.Analysis.Calculus.MeanValue

noncomputable section
open Set Filter _root_.Topology
open scoped ContDiff
namespace HolomorphicAnosov

/-- HPS pp.35 and 62: joint fibre regularity makes every actual original
jet evaluation continuous along continuous anchors and vector families.
Evaluate the given chart jet on the continuous source coordinate vectors;
linear chart transport identifies the result with the target coordinates of
the original derivative. The target chart recovers total-space continuity.
No derivative in the arbitrary parameter space is taken. -/
theorem parameter_graph_joint_jet_evaluation_continuous
    {A B Z : Type*} [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace Z]
    {E : A → Type*} {F : B → Type*}
    [∀ p, NormedAddCommGroup (E p)] [∀ p, NormedSpace ℝ (E p)]
    [∀ p, NormedAddCommGroup (F p)] [∀ p, NormedSpace ℝ (F p)]
    [TopologicalSpace (Sigma E)] [TopologicalSpace (Sigma F)]
    (e : FiniteRankNormedAtlas (E := E)) (f : FiniteRankNormedAtlas (E := F))
    (b : A → B) (hb : Continuous b) (g : ∀ p, E p → F (b p))
    (r m : ℕ) (hm : m ≤ r) (hg : JointFiberContDiff e f b r g)
    (p : Z → A) (hp : Continuous p) (x : ∀ z, E (p z))
    (hx : Continuous (fun z ↦ (⟨p z,x z⟩ : Sigma E)))
    (v : ∀ z, Fin m → E (p z))
    (hv : ∀ k, Continuous (fun z ↦ (⟨p z,v z k⟩ : Sigma E))) :
    Continuous (fun z ↦ (⟨b (p z), iteratedFDeriv ℝ m (g (p z)) (x z) (v z)⟩ : Sigma F)) := by
  apply continuous_iff_continuousAt.mpr
  intro z₀
  let i := p z₀
  let j := b (p z₀)
  let xc : Z → FiniteFiberModel (e.rank i) := fun z ↦ (e.chart i ⟨p z,x z⟩).2
  let vc : Z → Fin m → FiniteFiberModel (e.rank i) :=
    fun z k ↦ (e.chart i ⟨p z,v z k⟩).2
  have hxc : ContinuousAt xc z₀ :=
    ((e.chart i).continuousAt ((e.chart i).mem_source.mpr (e.mem_baseSet i))).snd.comp hx.continuousAt
  have hvc : ContinuousAt vc z₀ := by
    apply continuousAt_pi.mpr
    intro k
    exact ((e.chart i).continuousAt ((e.chart i).mem_source.mpr
      (e.mem_baseSet i))).snd.comp (hv k).continuousAt
  have hopen : IsOpen (((e.chart i).baseSet ∩ b ⁻¹' (f.chart j).baseSet) ×ˢ
      (univ : Set (FiniteFiberModel (e.rank i)))) :=
    ((e.chart i).open_baseSet.inter ((f.chart j).open_baseSet.preimage hb)).prod isOpen_univ
  have hmem : (p z₀,xc z₀) ∈ (((e.chart i).baseSet ∩ b ⁻¹' (f.chart j).baseSet) ×ˢ
      (univ : Set (FiniteFiberModel (e.rank i)))) :=
    ⟨⟨e.mem_baseSet i,f.mem_baseSet j⟩,mem_univ _⟩
  have hj := ((hg.2 i j m hm).continuousAt (hopen.mem_nhds hmem)).comp
    (f := fun z ↦ (p z,xc z)) (hp.continuousAt.prodMk hxc)
  have heval : ContinuousAt (fun z ↦
      FibreJet m (fibreChartExpression e f b g i j (p z)) (xc z) (vc z)) z₀ :=
    continuous_eval.continuousAt.comp (hj.prodMk hvc)
  apply (f.chart j).continuousAt_of_comp_left
    (show ContinuousAt (fun z : Z ↦
      (⟨b (p z), iteratedFDeriv ℝ m (g (p z)) (x z) (v z)⟩ : Sigma F).1) z₀ from
        (hb.comp hp).continuousAt) (f.mem_baseSet j)
  apply ((hb.comp hp).continuousAt.prodMk heval).congr_of_eventuallyEq
  have hne : ∀ᶠ z in 𝓝 z₀, p z ∈ (e.chart i).baseSet :=
    hp.continuousAt.eventually ((e.chart i).open_baseSet.mem_nhds (e.mem_baseSet i))
  have hnf : ∀ᶠ z in 𝓝 z₀, b (p z) ∈ (f.chart j).baseSet :=
    (hb.comp hp).continuousAt.eventually ((f.chart j).open_baseSet.mem_nhds (f.mem_baseSet j))
  filter_upwards [hne,hnf] with z he hf
  dsimp only [Function.comp_apply]
  rw [f.chart_apply j (b (p z)) hf]
  congr 1
  have hD := parameter_graph_atlas_iterated_derivative e f b g r hg.1 i j
    (p z) he hf m hm (xc z) (vc z)
  dsimp [xc,vc] at hD
  simp only [e.chart_apply i (p z) he, ContinuousLinearEquiv.symm_apply_apply] at hD
  simpa only [xc,vc,e.chart_apply i (p z) he] using hD.symm

/-- HPS pp.8,32–35,62: the original operator norm of every actual iterated
fibre derivative is jointly continuous. On an overlap chart, its evaluation
on source frame vectors is the target inverse frame applied to the supplied
continuous chart jet. Apply the multilinear compact-sphere norm formula to
these genuine evaluations, then use locality. -/
theorem parameter_graph_joint_jet_norm_continuous
    {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]
    {E : A → Type*} {F : B → Type*}
    [∀ p, NormedAddCommGroup (E p)] [∀ p, NormedSpace ℝ (E p)]
    [∀ p, NormedAddCommGroup (F p)] [∀ p, NormedSpace ℝ (F p)]
    [TopologicalSpace (Sigma E)] [TopologicalSpace (Sigma F)]
    (e : FiniteRankNormedAtlas (E := E)) (f : FiniteRankNormedAtlas (E := F))
    (b : A → B) (hb : Continuous b) (g : ∀ p, E p → F (b p))
    (r m : ℕ) (hm : m ≤ r) (hg : JointFiberContDiff e f b r g) :
    Continuous (fun z : Sigma E ↦ ‖iteratedFDeriv ℝ m (g z.1) z.2‖) := by
  have hproj : Continuous (fun z : Sigma E ↦ z.1) := by
    apply continuous_iff_continuousAt.mpr
    intro z
    exact (e.chart z.1).continuousAt_proj ((e.chart z.1).mem_source.mpr (e.mem_baseSet z.1))
  apply continuous_iff_continuousAt.mpr
  intro z₀
  let i := z₀.1
  let j := b z₀.1
  let U : Set (Sigma E) := {z | z.1 ∈ (e.chart i).baseSet ∧ b z.1 ∈ (f.chart j).baseSet}
  have hU : IsOpen U := ((e.chart i).open_baseSet.preimage hproj).inter
    ((f.chart j).open_baseSet.preimage (hb.comp hproj))
  have hz₀ : z₀ ∈ U := ⟨e.mem_baseSet i,f.mem_baseSet j⟩
  let J (z : U) := (e.coordinates i z.1.1 z.2.1).symm
  let L (z : U) := iteratedFDeriv ℝ m (g z.1.1) z.1.2
  have hbase : Continuous (fun z : U ↦ z.1.1) := hproj.comp continuous_subtype_val
  have hsrc : Continuous (fun z : U ↦ (⟨z.1.1,z.2.1⟩ : (e.chart i).baseSet)) :=
    hbase.subtype_mk _
  have hdst : Continuous (fun z : U ↦ (⟨b z.1.1,z.2.2⟩ : (f.chart j).baseSet)) :=
    (hb.comp hbase).subtype_mk _
  have hden : Continuous (fun z : U × FiniteFiberModel (e.rank i) ↦ ‖J z.1 z.2‖) :=
    e.continuous_norm.comp ((atlas_frame_continuous e i).comp
      ((hsrc.comp continuous_fst).prodMk continuous_snd))
  have hcoord : Continuous (fun z : U ↦ ((e.chart i) z.1).2) :=
    ((e.chart i).toOpenPartialHomeomorph.continuousOn.comp_continuous
      (continuous_subtype_val : Continuous (fun z : U ↦ (z.1 : Sigma E)))
      (fun z : U ↦ (e.chart i).mem_source.mpr z.2.1)).snd
  let Q (z : U) := FibreJet m (fibreChartExpression e f b g i j z.1.1) ((e.chart i) z.1).2
  have hQ : Continuous Q := (hg.2 i j m hm).comp_continuous
    (hbase.prodMk hcoord) (fun z ↦ ⟨z.2,mem_univ _⟩)
  have hnum : Continuous (fun z : U × (Fin m → FiniteFiberModel (e.rank i)) ↦
      ‖L z.1 (fun k ↦ J z.1 (z.2 k))‖) := by
    have heval : Continuous (fun z : U × (Fin m → FiniteFiberModel (e.rank i)) ↦ Q z.1 z.2) := by
      fun_prop
    have hout := f.continuous_norm.comp ((atlas_frame_continuous f j).comp
      ((hdst.comp continuous_fst).prodMk heval))
    apply hout.congr
    intro z
    change ‖(f.coordinates j (b z.1.1.1) z.1.2.2).symm (Q z.1 z.2)‖ = _
    apply congrArg norm
    apply (f.coordinates j (b z.1.1.1) z.1.2.2).injective
    rw [ContinuousLinearEquiv.apply_symm_apply]
    dsimp [Q,L,J]
    rw [e.chart_apply i z.1.1.1 z.1.2.1]
    simpa only [ContinuousLinearEquiv.symm_apply_apply] using
      parameter_graph_atlas_iterated_derivative e f b g r hg.1 i j
        z.1.1.1 z.1.2.1 z.1.2.2 m hm (e.coordinates i z.1.1.1 z.1.2.1 z.1.1.2) z.2
  have hn := continuous_multilinear_norm_of_frame m J L hden hnum
  have hon : ContinuousOn (fun z : Sigma E ↦ ‖iteratedFDeriv ℝ m (g z.1) z.2‖) U :=
    continuousOn_iff_continuous_domRestrict.mpr hn
  exact hon.continuousAt (hU.mem_nhds hz₀)

/-- The original jet norm is uniformly bounded on every closed original
input disc over a compact base. HPS pp.32–35,62: continuity of the actual
jet norm and compactness of the disc bound the known higher-order forcing. -/
theorem parameter_graph_joint_jet_norm_bounded
    {A B : Type*} [TopologicalSpace A] [CompactSpace A] [TopologicalSpace B]
    {E : A → Type*} {F : B → Type*}
    [∀ p, NormedAddCommGroup (E p)] [∀ p, NormedSpace ℝ (E p)]
    [∀ p, NormedAddCommGroup (F p)] [∀ p, NormedSpace ℝ (F p)]
    [TopologicalSpace (Sigma E)] [TopologicalSpace (Sigma F)]
    (e : FiniteRankNormedAtlas (E := E)) (f : FiniteRankNormedAtlas (E := F))
    (b : A → B) (hb : Continuous b) (g : ∀ p, E p → F (b p))
    (r m : ℕ) (hm : m ≤ r) (hg : JointFiberContDiff e f b r g) (R : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p (x : E p), ‖x‖ ≤ R → ‖iteratedFDeriv ℝ m (g p) x‖ ≤ C := by
  have hn := parameter_graph_joint_jet_norm_continuous e f b hb g r m hm hg
  obtain ⟨C,hC⟩ := (parameter_graph_closed_disc_isCompact e R).bddAbove_image hn.continuousOn
  refine ⟨max C 0,le_max_right _ _,?_⟩
  intro p x hx
  exact (hC ⟨⟨p,x⟩,hx,rfl⟩).trans (le_max_left _ _)

/-- HPS pp.32–35,62: on every original closed input disc, the actual first
derivative is uniformly Lipschitz over all fibres when joint fibre regularity
has order at least two. Bound the original second jet on the compact disc,
identify its norm with the derivative norm of fderiv by currying, and apply
the mean-value estimate on each convex original closed ball. -/
theorem parameter_graph_joint_fderiv_lipschitzOn
    {A B : Type*} [TopologicalSpace A] [CompactSpace A] [TopologicalSpace B]
    {E : A → Type*} {F : B → Type*}
    [∀ p, NormedAddCommGroup (E p)] [∀ p, NormedSpace ℝ (E p)]
    [∀ p, NormedAddCommGroup (F p)] [∀ p, NormedSpace ℝ (F p)]
    [TopologicalSpace (Sigma E)] [TopologicalSpace (Sigma F)]
    (e : FiniteRankNormedAtlas (E := E)) (f : FiniteRankNormedAtlas (E := F))
    (b : A → B) (hb : Continuous b) (g : ∀ p, E p → F (b p))
    (r : ℕ) (hr : 2 ≤ r) (hg : JointFiberContDiff e f b r g) (R : ℝ) :
    ∃ L : NNReal, ∀ p, LipschitzOnWith L (fderiv ℝ (g p)) (Metric.closedBall 0 R) := by
  obtain ⟨C,hC,hbound⟩ := parameter_graph_joint_jet_norm_bounded e f b hb g r 2 hr hg R
  refine ⟨⟨C,hC⟩,fun p ↦ ?_⟩
  have htwo : ContDiff ℝ (1 + 1 : ℕ∞ω) (g p) := (hg.1 p).of_le (by exact_mod_cast hr)
  have hd : Differentiable ℝ (fderiv ℝ (g p)) :=
    (contDiff_succ_iff_fderiv.mp htwo).2.2.differentiable (by decide)
  apply Convex.lipschitzOnWith_of_nnnorm_fderiv_le (fun x _ ↦ hd x) _ (convex_closedBall 0 R)
  intro x hx
  change ‖fderiv ℝ (fderiv ℝ (g p)) x‖ ≤ C
  rw [← norm_iteratedFDeriv_one (fderiv ℝ (g p)), norm_iteratedFDeriv_fderiv]
  exact hbound p x (by simpa only [Metric.mem_closedBall,dist_zero_right] using hx)

end HolomorphicAnosov
