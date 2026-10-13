import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphHomAtlas

noncomputable section
open Set Topology Filter
namespace HolomorphicAnosov.ParameterGraphPullbackAtlas
attribute [local instance] Classical.propDecidable
variable {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]
  {F : B → Type*} [∀p,NormedAddCommGroup (F p)] [∀p,NormedSpace ℝ (F p)]
  [TopologicalSpace (Sigma F)]
  (f : FiniteRankNormedAtlas (E := F)) (b : A → B) (hb : Continuous b)

def prechart (i : A) : Bundle.Pretrivialization (FiniteFiberModel (f.rank (b i)))
    (fun z : Sigma (fun p ↦ F (b p)) ↦ z.1) where
  toFun z := (z.1,if hz : b z.1 ∈ (f.chart (b i)).baseSet then
    f.coordinates (b i) (b z.1) hz z.2 else 0)
  invFun z := ⟨z.1,if hz : b z.1 ∈ (f.chart (b i)).baseSet then
    (f.coordinates (b i) (b z.1) hz).symm z.2 else 0⟩
  source := (fun z : Sigma (fun p ↦ F (b p)) ↦ b z.1) ⁻¹' (f.chart (b i)).baseSet
  target := (b ⁻¹' (f.chart (b i)).baseSet) ×ˢ univ
  map_source' := fun z hz ↦ ⟨hz,mem_univ _⟩
  map_target' := fun z hz ↦ hz.1
  left_inv' := by
    intro z hz
    simp only [mem_preimage] at hz
    simp only [dite_eq_left hz,ContinuousLinearEquiv.symm_apply_apply]
  right_inv' := by
    intro z hz
    simp only [mem_prod,mem_univ,and_true,mem_preimage] at hz
    simp only [dite_eq_left hz,ContinuousLinearEquiv.apply_symm_apply]
  open_target := ((f.chart (b i)).open_baseSet.preimage hb).prod isOpen_univ
  baseSet := b ⁻¹' (f.chart (b i)).baseSet
  open_baseSet := (f.chart (b i)).open_baseSet.preimage hb
  source_eq := rfl
  target_eq := rfl
  proj_toFun _ _ := rfl

lemma compatible (i j : A) : ContinuousOn
    ((prechart f b hb i) ∘ (prechart f b hb j).toPartialEquiv.symm)
    ((prechart f b hb j).target ∩
      (prechart f b hb j).toPartialEquiv.symm ⁻¹' (prechart f b hb i).source) := by
  rw [continuousOn_iff_continuous_domRestrict]
  let S := (prechart f b hb j).target ∩
    (prechart f b hb j).toPartialEquiv.symm ⁻¹' (prechart f b hb i).source
  have hmem (z : S) : b z.1.1 ∈ (f.chart (b j)).baseSet ∩ (f.chart (b i)).baseSet :=
    ⟨z.2.1.1,z.2.2⟩
  have hbase : Continuous (fun z : S ↦ b z.1.1) := hb.comp continuous_subtype_val.fst
  have hL := (f.continuous_transition (b j) (b i)).comp (hbase.subtype_mk hmem)
  have hres := continuous_subtype_val.fst.prodMk (hL.clm_apply continuous_subtype_val.snd)
  apply hres.congr
  intro z
  change (z.1.1,f.coordinates (b i) (b z.1.1) (hmem z).2
      ((f.coordinates (b j) (b z.1.1) (hmem z).1).symm z.1.2)) =
    (z.1.1,if hi : b z.1.1∈(f.chart (b i)).baseSet then
      f.coordinates (b i) (b z.1.1) hi
        (if hj : b z.1.1∈(f.chart (b j)).baseSet then
          (f.coordinates (b j) (b z.1.1) hj).symm z.1.2 else 0) else 0)
  simp only [dite_eq_left (hmem z).1,dite_eq_left (hmem z).2]

@[instance_reducible]
def topology : TopologicalSpace (Sigma (fun p ↦ F (b p))) :=
  ParameterGraphVaryingCharts.topology (fun i ↦ FiniteFiberModel (f.rank (b i)))
    (fun z ↦ z.1) (prechart f b hb)

def chart (i : A) : @Bundle.Trivialization A (FiniteFiberModel (f.rank (b i)))
    (Sigma (fun p ↦ F (b p))) _ _ (topology f b hb) (fun z ↦ z.1) :=
  ParameterGraphVaryingCharts.trivialization _ _ (prechart f b hb) (compatible f b hb) i

lemma chart_apply (i p : A) (hp : b p ∈ (f.chart (b i)).baseSet) (v : F (b p)) :
    chart f b hb i ⟨p,v⟩ = (p,f.coordinates (b i) (b p) hp v) := by
  change (p,if h : b p∈(f.chart (b i)).baseSet then f.coordinates (b i) (b p) h v else 0)=_
  simp only [dite_eq_left hp]

lemma fibre_inducing (p : A) :
    @Topology.IsInducing (F (b p)) _ _ (topology f b hb) (fun v ↦ ⟨p,v⟩) := by
  let := topology f b hb
  have hp := f.mem_baseSet (b p)
  have hm (v : F (b p)) : (⟨p,v⟩ : Sigma (fun p ↦ F (b p))) ∈
      (chart f b hb p).source := hp
  have hi : Topology.IsInducing (fun v : F (b p) ↦ chart f b hb p ⟨p,v⟩) := by
    have heq : (fun v : F (b p) ↦ chart f b hb p ⟨p,v⟩) =
      fun v ↦ (p,f.coordinates (b p) (b p) hp v) := funext (chart_apply f b hb p p hp)
    rw [heq]
    exact Topology.isInducing_const_prod.mpr (f.coordinates (b p) (b p) hp).toHomeomorph.isInducing
  have hc : Continuous (fun v : F (b p) ↦ (⟨p,v⟩ : Sigma (fun p ↦ F (b p)))) := by
    rw [(chart f b hb p).toOpenPartialHomeomorph.continuous_iff_continuous_comp_left
      (Set.eq_univ_of_forall hm)]
    exact hi.continuous
  change Topology.IsInducing ((chart f b hb p) ∘ (fun v : F (b p) ↦ ⟨p,v⟩)) at hi
  rw [← Set.domRestrict_comp_codRestrict hm] at hi
  apply Topology.IsInducing.of_codRestrict hm
  exact hi.of_comp (hc.codRestrict hm)
    (continuousOn_iff_continuous_domRestrict.mp (chart f b hb p).toOpenPartialHomeomorph.continuousOn)

lemma continuous_original : @Continuous _ _ (topology f b hb) _
    (fun z : Sigma (fun p ↦ F (b p)) ↦ (⟨b z.1,z.2⟩ : Sigma F)) := by
  change @Continuous _ _ (⨆i,TopologicalSpace.coinduced (prechart f b hb i).setSymm _) _ _
  rw [continuous_iSup_dom]
  intro i
  rw [continuous_coinduced_dom]
  let S := (prechart f b hb i).target
  have hbase : Continuous (fun z : S ↦ b z.1.1) := hb.comp continuous_subtype_val.fst
  have hmem (z : S) : b z.1.1∈(f.chart (b i)).baseSet := z.2.1
  have hs : Continuous (fun z : S ↦ (⟨b z.1.1,hmem z⟩ : (f.chart (b i)).baseSet)) :=
    hbase.subtype_mk _
  have hc := (atlas_frame_continuous f (b i)).comp
    (hs.prodMk continuous_subtype_val.snd)
  apply hc.congr
  intro z
  change (⟨b z.1.1,(f.coordinates (b i) (b z.1.1) (hmem z)).symm z.1.2⟩ : Sigma F) =
    ⟨b z.1.1,if hz : b z.1.1∈(f.chart (b i)).baseSet then
      (f.coordinates (b i) (b z.1.1) hz).symm z.1.2 else 0⟩
  simp only [dite_eq_left (hmem z)]

/-- Pull back the original finite-rank normed bundle along any continuous base
map. The topology is generated by the pulled-back original linear charts;
fibre norms and coordinate equivalences are unchanged. -/
def atlas : @FiniteRankNormedAtlas A _ (fun p ↦ F (b p)) _ _ (topology f b hb) := by
  letI := topology f b hb
  exact {
    rank := fun p ↦ f.rank (b p)
    chart := chart f b hb
    mem_baseSet := fun p ↦ f.mem_baseSet (b p)
    rank_eq := fun i p hp ↦ f.rank_eq (b i) (b p) hp
    coordinates := fun i p hp ↦ f.coordinates (b i) (b p) hp
    chart_apply := chart_apply f b hb
    fibre_inducing := fibre_inducing f b hb
    continuous_norm := f.continuous_norm.comp (continuous_original f b hb)
    continuous_transition := fun i j ↦
      (f.continuous_transition (b i) (b j)).comp
        ((hb.comp continuous_subtype_val).subtype_mk (fun p ↦ p.2)) }

/-- The pulled-back topology is exactly the topology detected by the base and
original bundle evaluations, so it agrees with the usual pullback subspace
topology. This also supplies the total-map continuity rule for action families. -/
theorem continuous_mk_iff {Z : Type*} [TopologicalSpace Z]
    (p : Z → A) (v : ∀z,F (b (p z))) :
    @Continuous Z _ _ (topology f b hb) (fun z ↦ (⟨p z,v z⟩ : Sigma (fun p ↦ F (b p)))) ↔
      Continuous p ∧ Continuous (fun z ↦ (⟨b (p z),v z⟩ : Sigma F)) := by
  let := topology f b hb
  have hproj : Continuous (fun z : Sigma (fun p ↦ F (b p)) ↦ z.1) := by
    apply continuous_iff_continuousAt.mpr
    intro z
    exact (chart f b hb z.1).continuousAt_proj
      ((chart f b hb z.1).mem_source.mpr (f.mem_baseSet (b z.1)))
  constructor
  · intro h
    exact ⟨hproj.comp h,(continuous_original f b hb).comp h⟩
  · rintro ⟨hp,hv⟩
    apply continuous_iff_continuousAt.mpr
    intro z₀
    let i := p z₀
    have hi : b (p z₀)∈(f.chart (b i)).baseSet := f.mem_baseSet (b i)
    have hc := ((f.chart (b i)).toOpenPartialHomeomorph.continuousAt
      ((f.chart (b i)).mem_source.mpr hi)).comp hv.continuousAt
    apply (chart f b hb i).continuousAt_of_comp_left
      (show ContinuousAt (fun z ↦ (⟨p z,v z⟩ : Sigma (fun p ↦ F (b p))).1) z₀ from hp.continuousAt) hi
    apply (hp.continuousAt.prodMk hc.snd).congr_of_eventuallyEq
    have hnear : ∀ᶠz in nhds z₀,b (p z)∈(f.chart (b i)).baseSet :=
      (hb.comp hp).continuousAt.preimage_mem_nhds ((f.chart (b i)).open_baseSet.mem_nhds hi)
    filter_upwards [hnear] with z hz
    simp only [Function.comp_apply]
    rw [chart_apply f b hb i (p z) hz]
    change (p z,f.coordinates (b i) (b (p z)) hz (v z)) =
      (p z,((f.chart (b i)) ⟨b (p z),v z⟩).2)
    rw [f.chart_apply (b i) (b (p z)) hz]

end HolomorphicAnosov.ParameterGraphPullbackAtlas
