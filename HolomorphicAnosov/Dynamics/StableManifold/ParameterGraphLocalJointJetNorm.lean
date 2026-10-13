import HolomorphicAnosov.Dynamics.StableManifold.FiniteRankAtlasFrameContinuity
import HolomorphicAnosov.Analysis.FrameMultilinearNormContinuity
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphClosedDiscCompactness
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphJointJetCriterion
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphLocalFiberRegularity

noncomputable section
open Set Filter _root_.Topology
open scoped ContDiff
namespace HolomorphicAnosov

/-- HPS pp.35 and 62: local joint fibre regularity makes every actual original
jet evaluation continuous along continuous anchors and vector families.
Evaluate the given chart jet on the continuous source coordinate vectors;
linear chart transport identifies the result with the target coordinates of
the original derivative. The target chart recovers total-space continuity.
All anchors lie in the given original open domain. No derivative in the parameter is taken. -/
theorem parameter_graph_local_jet_evaluation_continuous
    {A B Z : Type*} [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace Z]
    {E : A → Type*} {F : B → Type*}
    [∀ p, NormedAddCommGroup (E p)] [∀ p, NormedSpace ℝ (E p)]
    [∀ p, NormedAddCommGroup (F p)] [∀ p, NormedSpace ℝ (F p)]
    [TopologicalSpace (Sigma E)] [TopologicalSpace (Sigma F)]
    (e : FiniteRankNormedAtlas (E := E)) (f : FiniteRankNormedAtlas (E := F))
    (b : A → B) (hb : Continuous b) (g : ∀ p, E p → F (b p))
    (r m : ℕ) (hm : m ≤ r) (U : Set (Sigma E)) (hU : IsOpen U)
    (hg : JointFiberContDiffOn e f b r U g)
    (p : Z → A) (hp : Continuous p) (x : ∀ z, E (p z))
    (hx : Continuous (fun z ↦ (⟨p z,x z⟩ : Sigma E)))
    (hxU : ∀ z, (⟨p z,x z⟩ : Sigma E) ∈ U)
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
  have hanchor : (e.chart i).toOpenPartialHomeomorph.symm (p z₀,xc z₀) =
      (⟨p z₀,x z₀⟩ : Sigma E) := by
    have hpair : (p z₀,xc z₀) = e.chart i ⟨p z₀,x z₀⟩ := by
      dsimp [xc]
      rw [e.chart_apply i (p z₀) (e.mem_baseSet i)]
    rw [hpair]
    exact (e.chart i).toOpenPartialHomeomorph.left_inv
      ((e.chart i).mem_source.mpr (e.mem_baseSet i))
  have hinv : ContinuousAt (e.chart i).toOpenPartialHomeomorph.symm (p z₀,xc z₀) :=
    (e.chart i).toOpenPartialHomeomorph.continuousAt_symm
      ((e.chart i).mem_target.mpr (e.mem_baseSet i))
  have hnear : {z : A × FiniteFiberModel (e.rank i) |
      z.1 ∈ (e.chart i).baseSet ∩ b ⁻¹' (f.chart j).baseSet ∧
      (e.chart i).toOpenPartialHomeomorph.symm z ∈ U} ∈ 𝓝 (p z₀,xc z₀) := by
    have hbnear := hopen.mem_nhds hmem
    have hunear := hinv.preimage_mem_nhds (hU.mem_nhds (hanchor.symm ▸ hxU z₀))
    filter_upwards [hbnear,hunear] with z hz hu
    exact ⟨hz.1,hu⟩
  have hj := ((hg.2 i j m hm).continuousAt hnear).comp
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
  have hD := parameter_graph_atlas_iterated_derivative_of_equiv e f b g i j
    (p z) he hf m (xc z) (vc z)
  dsimp [xc,vc] at hD
  simp only [e.chart_apply i (p z) he, ContinuousLinearEquiv.symm_apply_apply] at hD
  simpa only [xc,vc,e.chart_apply i (p z) he] using hD.symm

/-- HPS pp.8,32–36,62: local joint jet regularity gives continuity of the
actual original jet norm on the same open domain. On source frame neighborhoods
use continuous original jet evaluation and the multilinear norm-ratio theorem.
All topology and norms remain the supplied ones. -/
theorem parameter_graph_local_jet_norm_continuousOn
    {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]
    {E : A → Type*} {F : B → Type*}
    [∀ p, NormedAddCommGroup (E p)] [∀ p, NormedSpace ℝ (E p)]
    [∀ p, NormedAddCommGroup (F p)] [∀ p, NormedSpace ℝ (F p)]
    [TopologicalSpace (Sigma E)] [TopologicalSpace (Sigma F)]
    (e : FiniteRankNormedAtlas (E := E)) (f : FiniteRankNormedAtlas (E := F))
    (b : A → B) (hb : Continuous b) (g : ∀ p, E p → F (b p))
    (r m : ℕ) (hm : m ≤ r) (U : Set (Sigma E)) (hU : IsOpen U)
    (hg : JointFiberContDiffOn e f b r U g) :
    ContinuousOn (fun z : Sigma E ↦ ‖iteratedFDeriv ℝ m (g z.1) z.2‖) U := by
  have hproj : Continuous (fun z : Sigma E ↦ z.1) := by
    apply continuous_iff_continuousAt.mpr
    intro z
    exact (e.chart z.1).continuousAt_proj ((e.chart z.1).mem_source.mpr (e.mem_baseSet z.1))
  intro z₀ hz₀
  let i := z₀.1
  let W : Set (Sigma E) := U ∩ {z | z.1 ∈ (e.chart i).baseSet}
  have hW : IsOpen W := hU.inter ((e.chart i).open_baseSet.preimage hproj)
  have hzW : z₀ ∈ W := ⟨hz₀,e.mem_baseSet i⟩
  let J (z : W) := (e.coordinates i z.1.1 z.2.2).symm
  let L (z : W) := iteratedFDeriv ℝ m (g z.1.1) z.1.2
  have hbase : Continuous (fun z : W ↦ z.1.1) := hproj.comp continuous_subtype_val
  have hsrc : Continuous (fun z : W ↦ (⟨z.1.1,z.2.2⟩ : (e.chart i).baseSet)) :=
    hbase.subtype_mk _
  have hden : Continuous (fun z : W × FiniteFiberModel (e.rank i) ↦ ‖J z.1 z.2‖) :=
    e.continuous_norm.comp ((atlas_frame_continuous e i).comp
      ((hsrc.comp continuous_fst).prodMk continuous_snd))
  have hx : Continuous (fun z : W × (Fin m → FiniteFiberModel (e.rank i)) ↦
      (⟨z.1.1.1,z.1.1.2⟩ : Sigma E)) := continuous_subtype_val.comp continuous_fst
  have hv (k : Fin m) : Continuous
      (fun z : W × (Fin m → FiniteFiberModel (e.rank i)) ↦
        (⟨z.1.1.1,J z.1 (z.2 k)⟩ : Sigma E)) :=
    (atlas_frame_continuous e i).comp ((hsrc.comp continuous_fst).prodMk
      ((continuous_apply k).comp continuous_snd))
  have heval := parameter_graph_local_jet_evaluation_continuous e f b hb g r m hm U hU hg
    (fun z : W × (Fin m → FiniteFiberModel (e.rank i)) ↦ z.1.1.1)
    (hbase.comp continuous_fst) (fun z ↦ z.1.1.2) hx (fun z ↦ z.1.2.1)
    (fun z k ↦ J z.1 (z.2 k)) hv
  have hnum : Continuous (fun z : W × (Fin m → FiniteFiberModel (e.rank i)) ↦
      ‖L z.1 (fun k ↦ J z.1 (z.2 k))‖) := f.continuous_norm.comp heval
  have hn := continuous_multilinear_norm_of_frame m J L hden hnum
  have hon : ContinuousOn (fun z : Sigma E ↦ ‖iteratedFDeriv ℝ m (g z.1) z.2‖) W :=
    continuousOn_iff_continuous_domRestrict.mpr hn
  exact (hon.continuousAt (hW.mem_nhds hzW)).continuousWithinAt

/-- HPS pp.32–36,62: each known local jet has a uniform original norm bound
on any closed original disc contained in its regularity domain. Compactness
of the original disc and continuity of the local jet norm provide the bound. -/
theorem parameter_graph_local_jet_norm_bounded
    {A B : Type*} [TopologicalSpace A] [CompactSpace A] [TopologicalSpace B]
    {E : A → Type*} {F : B → Type*}
    [∀ p, NormedAddCommGroup (E p)] [∀ p, NormedSpace ℝ (E p)]
    [∀ p, NormedAddCommGroup (F p)] [∀ p, NormedSpace ℝ (F p)]
    [TopologicalSpace (Sigma E)] [TopologicalSpace (Sigma F)]
    (e : FiniteRankNormedAtlas (E := E)) (f : FiniteRankNormedAtlas (E := F))
    (b : A → B) (hb : Continuous b) (g : ∀ p, E p → F (b p))
    (r m : ℕ) (hm : m ≤ r) (U : Set (Sigma E)) (hU : IsOpen U)
    (hg : JointFiberContDiffOn e f b r U g) (R : ℝ)
    (hR : {z : Sigma E | ‖z.2‖ ≤ R} ⊆ U) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p (x : E p), ‖x‖ ≤ R → ‖iteratedFDeriv ℝ m (g p) x‖ ≤ C := by
  have hn := (parameter_graph_local_jet_norm_continuousOn e f b hb g r m hm U hU hg).mono hR
  obtain ⟨C,hC⟩ := (parameter_graph_closed_disc_isCompact e R).bddAbove_image hn
  refine ⟨max C 0,le_max_right _ _,?_⟩
  intro p x hx
  exact (hC ⟨⟨p,x⟩,hx,rfl⟩).trans (le_max_left _ _)

end HolomorphicAnosov
