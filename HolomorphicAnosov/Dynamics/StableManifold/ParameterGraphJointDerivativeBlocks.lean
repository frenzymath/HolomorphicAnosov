import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphAtlasOperations
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphJointBilinearOperations
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphJointComposition
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphJointDerivativeCriterion
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphJointProductPullback
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphLocalFiberRegularity
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphLocalJointJetCriterion
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphLocalJointJetNorm
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphJointTangentAction
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphJointDerivativeEvaluation

noncomputable section
open Set _root_.Topology
namespace HolomorphicAnosov

/-- Pairing jointly regular original fibre maps into the original split total
atlas preserves their joint order. Original jets pair componentwise;
continuity is exactly the original split-pairing law applied to the two
continuous evaluated jets. -/
theorem parameter_graph_local_joint_split_pair
    {A : Type*} [TopologicalSpace A] {Z X Y : A→Type*}
    [∀p,NormedAddCommGroup (Z p)] [∀p,NormedSpace ℝ (Z p)]
    [∀p,NormedAddCommGroup (X p)] [∀p,NormedSpace ℝ (X p)]
    [∀p,NormedAddCommGroup (Y p)] [∀p,NormedSpace ℝ (Y p)]
    [TopologicalSpace (Sigma Z)] [TopologicalSpace (Sigma X)] [TopologicalSpace (Sigma Y)]
    [TopologicalSpace (Sigma (fun p ↦ X p×Y p))]
    (ez : FiniteRankNormedAtlas (E := Z)) (e : SplitFiniteRankNormedAtlas (E₁:=X) (E₂:=Y))
    (r:ℕ) (U:Set (Sigma Z)) (hU:IsOpen U) (u:∀p,Z p→X p) (v:∀p,Z p→Y p)
    (hu:JointFiberContDiffOn ez e.first id r U u)
    (hv:JointFiberContDiffOn ez e.second id r U v) :
    JointFiberContDiffOn ez e.total id r U (fun p a ↦ (u p a,v p a)) := by
  apply parameter_graph_local_joint_jet_criterion
  · intro z hz
    exact (hu.1 z hz).prodMk (hv.1 z hz)
  ·
    intro i m hm
    rw [continuousOn_iff_continuous_domRestrict]
    let S : Set ((ez.chart i).baseSet ×
        (FiniteFiberModel (ez.rank i) × (Fin m → FiniteFiberModel (ez.rank i)))) :=
      {z | (⟨z.1.val,(ez.coordinates i z.1.val z.1.property).symm z.2.1⟩ : Sigma Z) ∈ U}
    let p : S → A := fun z ↦ z.1.1.1
    let x (a : S) := (ez.coordinates i a.1.1.1 a.1.1.2).symm a.1.2.1
    let dirs (a : S) (j : Fin m) := (ez.coordinates i a.1.1.1 a.1.1.2).symm (a.1.2.2 j)
    have hp : Continuous p := continuous_subtype_val.comp continuous_subtype_val.fst
    have hx : Continuous (fun z : S ↦ (⟨p z,x z⟩ : Sigma Z)) :=
      (atlas_frame_continuous ez i).comp
        (continuous_subtype_val.fst.prodMk continuous_subtype_val.snd.fst)
    have hdirs (a : Fin m) : Continuous (fun z : S ↦ (⟨p z,dirs z a⟩ : Sigma Z)) :=
      (atlas_frame_continuous ez i).comp (continuous_subtype_val.fst.prodMk
        ((continuous_apply a).comp continuous_subtype_val.snd.snd))
    have huj := parameter_graph_local_jet_evaluation_continuous ez e.first id continuous_id u r m hm U hU hu
      p hp x hx (fun z ↦ z.2) dirs hdirs
    have hvj := parameter_graph_local_jet_evaluation_continuous ez e.second id continuous_id v r m hm U hU hv
      p hp x hx (fun z ↦ z.2) dirs hdirs
    have hc := parameter_graph_atlas_pair_continuous e (fun z ↦ p z)
      (fun z ↦ iteratedFDeriv ℝ m (u (p z)) (x z) (dirs z))
      (fun z ↦ iteratedFDeriv ℝ m (v (p z)) (x z) (dirs z)) huj hvj
    apply hc.congr
    intro z
    change (⟨id (p z),(_,_)⟩ : Sigma (fun p ↦ X p × Y p)) =
      ⟨id (p z),iteratedFDeriv ℝ m (fun y ↦ (u (p z) y,v (p z) y)) (x z) (dirs z)⟩
    rw [iteratedFDeriv_prodMk (hu.1 _ z.2) (hv.1 _ z.2) (by exact_mod_cast hm)]
    rfl

/-- Extract the four actual derivative blocks along an arbitrary jointly
regular original graph map. Differentiation loses one order, and conjugating
with native inclusions and pulled-back original projections preserves the
remaining joint order. No graph invariance or derivative of the graph map is
assumed or used. -/
theorem parameter_graph_local_joint_derivative_blocks
    {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]
    {Z X Y : A→Type*} {X' Y' : B→Type*}
    [∀p,NormedAddCommGroup (Z p)] [∀p,NormedSpace ℝ (Z p)]
    [∀p,NormedAddCommGroup (X p)] [∀p,NormedSpace ℝ (X p)]
    [∀p,NormedAddCommGroup (Y p)] [∀p,NormedSpace ℝ (Y p)]
    [∀p,NormedAddCommGroup (X' p)] [∀p,NormedSpace ℝ (X' p)]
    [∀p,NormedAddCommGroup (Y' p)] [∀p,NormedSpace ℝ (Y' p)]
    [TopologicalSpace (Sigma Z)] [TopologicalSpace (Sigma X)] [TopologicalSpace (Sigma Y)]
    [TopologicalSpace (Sigma X')] [TopologicalSpace (Sigma Y')]
    [TopologicalSpace (Sigma (fun p ↦ X p×Y p))]
    [TopologicalSpace (Sigma (fun p ↦ X' p×Y' p))]
    (z:FiniteRankNormedAtlas (E:=Z)) (e:SplitFiniteRankNormedAtlas (E₁:=X) (E₂:=Y))
    (f:SplitFiniteRankNormedAtlas (E₁:=X') (E₂:=Y')) (b:A→B) (hb:Continuous b)
    (n:ℕ) (U:Set (Sigma Z)) (hU:IsOpen U)
    (V:Set (Sigma (fun p ↦ X p×Y p))) (hV:IsOpen V)
    (G:∀p,X p×Y p→X' (b p)×Y' (b p)) (g:∀p,Z p→X p×Y p)
    (hG:JointFiberContDiffOn e.total f.total b (n+1) V G)
    (hg:JointFiberContDiffOn z e.total id n U g)
    (hmap:∀a∈U,(⟨a.1,g a.1 a.2⟩:Sigma (fun p ↦ X p×Y p))∈V) :
    letI := ParameterGraphPullbackAtlas.topology f.first b hb
    letI := ParameterGraphPullbackAtlas.topology f.second b hb
    let fx := ParameterGraphPullbackAtlas.atlas f.first b hb
    let fy := ParameterGraphPullbackAtlas.atlas f.second b hb
    let DG := fun p a ↦ fderiv ℝ (G p) (g p a)
    (letI := ParameterGraphHomAtlas.topology e.first fx;
      JointFiberContDiffOn z (ParameterGraphHomAtlas.atlas e.first fx) id n U
        (fun p a ↦ ((ContinuousLinearMap.fst ℝ (X' (b p)) (Y' (b p))).comp (DG p a)).comp
          (ContinuousLinearMap.inl ℝ (X p) (Y p)))) ∧
    (letI := ParameterGraphHomAtlas.topology e.second fx;
      JointFiberContDiffOn z (ParameterGraphHomAtlas.atlas e.second fx) id n U
        (fun p a ↦ ((ContinuousLinearMap.fst ℝ (X' (b p)) (Y' (b p))).comp (DG p a)).comp
          (ContinuousLinearMap.inr ℝ (X p) (Y p)))) ∧
    (letI := ParameterGraphHomAtlas.topology e.first fy;
      JointFiberContDiffOn z (ParameterGraphHomAtlas.atlas e.first fy) id n U
        (fun p a ↦ ((ContinuousLinearMap.snd ℝ (X' (b p)) (Y' (b p))).comp (DG p a)).comp
          (ContinuousLinearMap.inl ℝ (X p) (Y p)))) ∧
    (letI := ParameterGraphHomAtlas.topology e.second fy;
      JointFiberContDiffOn z (ParameterGraphHomAtlas.atlas e.second fy) id n U
        (fun p a ↦ ((ContinuousLinearMap.snd ℝ (X' (b p)) (Y' (b p))).comp (DG p a)).comp
          (ContinuousLinearMap.inr ℝ (X p) (Y p)))) := by
  let := ParameterGraphPullbackAtlas.topology f.first b hb
  let := ParameterGraphPullbackAtlas.topology f.second b hb
  let := ParameterGraphPullbackAtlas.topology f.total b hb
  let fx := ParameterGraphPullbackAtlas.atlas f.first b hb
  let fy := ParameterGraphPullbackAtlas.atlas f.second b hb
  let ft := ParameterGraphPullbackAtlas.atlas f.total b hb
  have hG' := (parameter_graph_local_joint_pullback_iff e.total f.total b hb (n+1) V hV G).mpr hG
  let := ParameterGraphHomAtlas.topology e.total ft
  have hd := parameter_graph_local_joint_derivative e.total ft G n V hV hG'
  have hDG := parameter_graph_local_joint_comp z e.total (ParameterGraphHomAtlas.atlas e.total ft)
    id continuous_id id continuous_id g (fun p ↦ fderiv ℝ (G p)) n U V hU hV hg hd hmap
  let := ParameterGraphHomAtlas.topology e.first e.total
  let := ParameterGraphHomAtlas.topology e.second e.total
  let := ParameterGraphHomAtlas.topology ft fx
  let := ParameterGraphHomAtlas.topology ft fy
  have hIL := parameter_graph_joint_constant_operator z e.first e.total
    (fun p ↦ ContinuousLinearMap.inl ℝ (X p) (Y p))
    (parameter_graph_atlas_pair_continuous e Sigma.fst Sigma.snd (fun _ ↦ 0) continuous_id
      (parameter_graph_atlas_zero_continuous e.second _ (parameter_graph_atlas_projection_continuous e.first))) n
  have hIR := parameter_graph_joint_constant_operator z e.second e.total
    (fun p ↦ ContinuousLinearMap.inr ℝ (X p) (Y p))
    (parameter_graph_atlas_pair_continuous e Sigma.fst (fun _ ↦ 0) Sigma.snd
      (parameter_graph_atlas_zero_continuous e.first _ (parameter_graph_atlas_projection_continuous e.second)) continuous_id) n
  have hproj := parameter_graph_atlas_projection_continuous ft
  have horig := ParameterGraphPullbackAtlas.continuous_original f.total b hb
  have hcomponents := parameter_graph_atlas_split_projections_continuous f
  have hOL := parameter_graph_joint_constant_operator z ft fx
    (fun p ↦ ContinuousLinearMap.fst ℝ (X' (b p)) (Y' (b p)))
    ((ParameterGraphPullbackAtlas.continuous_mk_iff f.first b hb Sigma.fst
      (fun a : Sigma (fun p:A ↦ X' (b p)×Y' (b p)) ↦ a.2.1)).mpr ⟨hproj,hcomponents.1.comp horig⟩) n
  have hOR := parameter_graph_joint_constant_operator z ft fy
    (fun p ↦ ContinuousLinearMap.snd ℝ (X' (b p)) (Y' (b p)))
    ((ParameterGraphPullbackAtlas.continuous_mk_iff f.second b hb Sigma.fst
      (fun a : Sigma (fun p:A ↦ X' (b p)×Y' (b p)) ↦ a.2.2)).mpr ⟨hproj,hcomponents.2.comp horig⟩) n
  have hIL' := (jointFiberContDiffOn_univ_iff.mpr hIL).mono (subset_univ U)
  have hIR' := (jointFiberContDiffOn_univ_iff.mpr hIR).mono (subset_univ U)
  have hOL' := (jointFiberContDiffOn_univ_iff.mpr hOL).mono (subset_univ U)
  have hOR' := (jointFiberContDiffOn_univ_iff.mpr hOR).mono (subset_univ U)
  let := ParameterGraphHomAtlas.topology e.total fx
  let := ParameterGraphHomAtlas.topology e.total fy
  have htop := parameter_graph_local_joint_clm_comp z e.total ft fx n U hU _ _ hOL' hDG
  have hbottom := parameter_graph_local_joint_clm_comp z e.total ft fy n U hU _ _ hOR' hDG
  exact ⟨parameter_graph_local_joint_clm_comp z e.first e.total fx n U hU _ _ htop hIL',
    parameter_graph_local_joint_clm_comp z e.second e.total fx n U hU _ _ htop hIR',
    parameter_graph_local_joint_clm_comp z e.first e.total fy n U hU _ _ hbottom hIL',
    parameter_graph_local_joint_clm_comp z e.second e.total fy n U hU _ _ hbottom hIR'⟩

end HolomorphicAnosov
