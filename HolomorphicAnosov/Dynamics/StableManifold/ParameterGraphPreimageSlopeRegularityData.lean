import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphHorizontalInverse
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphJointComposition
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphJointDerivativeCriterion
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphJointDerivativeEvaluation
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphJointProductPullback
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphJointTangentAction
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphLocalFiberRegularity
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphJointDerivativeBlocks
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphJointSlopeAction
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphGlobalSectionRegularity
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphPreimageDerivativeSlope
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphDerivativeBlocks
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphVerticalEstimate
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphSlopeComparison

noncomputable section
open Set _root_.Topology
namespace HolomorphicAnosov

/-- HPS pp.32–36,55–58,62: an actual invariant preimage graph gains one
joint fibre order under the strong contracting-return inequality. Differentiate
the exact graph equation, extract the four actual ambient derivative blocks,
and use the horizontal perturbation inverse to obtain the rational invariant
slope equation. Its unit-ball contraction and strict interior slope bound let
the global invariant-section regularity theorem give order n for Dt. The
successor criterion gives order n+1 for t. Only already known order n graph
jets enter the action; no invertibility of the lower block is required. -/
theorem parameter_graph_preimage_regularity_step
    {A : Type*} [TopologicalSpace A] [CompactSpace A] {X Y : A → Type*}
    [∀p,NormedAddCommGroup (X p)] [∀p,NormedSpace ℝ (X p)] [∀p,CompleteSpace (X p)]
    [∀p,NormedAddCommGroup (Y p)] [∀p,NormedSpace ℝ (Y p)]
    [TopologicalSpace (Sigma X)] [TopologicalSpace (Sigma Y)]
    [TopologicalSpace (Sigma (fun p ↦ X p×Y p))]
    (e : SplitFiniteRankNormedAtlas (E₁ := X) (E₂ := Y))
    (h : A → A) (hh : Continuous h)
    (T : ∀p,X p ≃L[ℝ] X (h p)) (S : ∀p,Y p →L[ℝ] Y (h p))
    (G : ∀p,X p×Y p → X (h p)×Y (h p))
    (t : ∀p,Y p → X p) (n : ℕ) (hn : 1≤n)
    (hG : JointFiberContDiff e.total e.total h (n+1) G)
    (ht : JointFiberContDiff e.second e.first id n t)
    (hzero : ∀p,G p 0=0) (htzero : ∀p,t p 0=0)
    (htL : ∀p,LipschitzWith 1 (t p))
    (hgraph : ∀p y,(G p (t p y,y)).1=t (h p) (G p (t p y,y)).2)
    (a k ε : NNReal) (ha : ∀p,‖(T p).symm.toContinuousLinearMap‖≤a)
    (hk : ∀p,‖S p‖≤k)
    (hsmall : 2*(a:ℝ)*ε<1)
    (hjet : (a:ℝ)*(k+2*ε)/(1-2*(a:ℝ)*ε)<1)
    (hstrong : (k:ℝ)+ε<1)
    (hpert : ∀p,LipschitzWith ε (fun z ↦ G p z-(T p z.1,S p z.2))) :
    JointFiberContDiff e.second e.first id (n+1) t := by
  have ht1 : JointFiberContDiff e.second e.first id 1 t :=
    ⟨fun p ↦ (ht.1 p).of_le (by exact_mod_cast hn),
      fun i j m hm ↦ ht.2 i j m (hm.trans hn)⟩
  have htd (p:A) : Differentiable ℝ (t p) := (ht1.1 p).differentiable (by simp)
  have hGd (p:A) : Differentiable ℝ (G p) := (hG.1 p).differentiable (by simp)
  let R := fun p y ↦ (G p (t p y,y)).2
  let DG := fun p y ↦ fderiv ℝ (G p) (t p y,y)
  let AA := fun p y ↦ ((ContinuousLinearMap.fst ℝ (X (h p)) (Y (h p))).comp
    (DG p y)).comp (ContinuousLinearMap.inl ℝ (X p) (Y p))
  let BB := fun p y ↦ ((ContinuousLinearMap.fst ℝ (X (h p)) (Y (h p))).comp
    (DG p y)).comp (ContinuousLinearMap.inr ℝ (X p) (Y p))
  let CC := fun p y ↦ ((ContinuousLinearMap.snd ℝ (X (h p)) (Y (h p))).comp
    (DG p y)).comp (ContinuousLinearMap.inl ℝ (X p) (Y p))
  let DD := fun p y ↦ ((ContinuousLinearMap.snd ℝ (X (h p)) (Y (h p))).comp
    (DG p y)).comp (ContinuousLinearMap.inr ℝ (X p) (Y p))
  let P := fun p ↦ fderiv ℝ (t p)
  have hblock (p:A) (y:Y p) : ‖AA p y-(T p).toContinuousLinearMap‖≤ε ∧
      ‖BB p y‖≤ε ∧ ‖CC p y‖≤ε ∧ ‖DD p y‖≤(k:ℝ)+ε := by
    obtain ⟨hA,hB,hC,hD⟩ := parameter_graph_derivative_blocks
      (T p).toContinuousLinearMap (S p) (G p) ε (hpert p) (t p y,y)
      (DG p y) (hGd p _).hasFDerivAt
    refine ⟨hA,hB,hC,?_⟩
    calc
      ‖DD p y‖ ≤ ‖DD p y-S p‖+‖S p‖ := norm_le_norm_sub_add _ _
      _ ≤ (ε:ℝ)+k := add_le_add hD (hk p)
      _ = _ := add_comm _ _
  have hfirst (p:A) (y:Y p) (x:X p) (v:Y p) :
      (DG p y (x,v)).1=AA p y x+BB p y v := by
    have he : (x,v)=(x,0)+(0,v) := by simp
    conv_lhs => rw [he,map_add]
    rfl
  have hsecond (p:A) (y:Y p) (x:X p) (v:Y p) :
      (DG p y (x,v)).2=CC p y x+DD p y v := by
    have he : (x,v)=(x,0)+(0,v) := by simp
    conv_lhs => rw [he,map_add]
    rfl
  have heq (p:A) (y:Y p) :
      (AA p y-(P (h p) (R p y)).comp (CC p y)).comp (P p y)=
        (P (h p) (R p y)).comp (DD p y)-BB p y :=
    parameter_graph_preimage_derivative_equation (G p) (t p) (t (h p)) y (DG p y)
      (hGd p _).hasFDerivAt (htd p y) (htd (h p) _) (hgraph p)
      (AA p y) (BB p y) (CC p y) (DD p y) (hfirst p y) (hsecond p y)
  have hPunit (p:A) (y:Y p) : ‖P p y‖≤1 := by
    simpa using norm_fderiv_le_of_lipschitz ℝ (htL p) (x₀ := y)
  let b : NNReal := ⟨(a:ℝ)/(1-2*(a:ℝ)*ε),div_nonneg a.2 (sub_pos.mpr hsmall).le⟩
  let q : NNReal := b*(k+2*ε)
  have hqeq : (q:ℝ)=(a:ℝ)*(k+2*ε)/(1-2*(a:ℝ)*ε) := by
    change ((a:ℝ)/(1-2*(a:ℝ)*ε))*((k:ℝ)+2*ε)=_
    ring
  have hq : (q:ℝ)<1 := hqeq ▸ hjet
  have hPn (p:A) (y:Y p) : ‖P p y‖≤q := by
    rw [hqeq]
    exact (parameter_graph_preimage_slope_interior (T p) (AA p y) (BB p y)
      (CC p y) (DD p y) a k ε (ha p) (hblock p y).1 (hblock p y).2.1
      (hblock p y).2.2.1 (hblock p y).2.2.2 hsmall hjet _ _
      (hPunit (h p) (R p y)) (heq p y)).1
  let F (p:A) (w:Y p×(Y (h p)→L[ℝ] X (h p))) :=
    (AA p w.1-w.2.comp (CC p w.1)).inverse.comp (w.2.comp (DD p w.1)-BB p w.1)
  have hInv (p:A) (y:Y p) (V:Y (h p)→L[ℝ] X (h p)) (hV:‖V‖≤1) :
      ∃J:X p≃L[ℝ]X (h p),J.toContinuousLinearMap=AA p y-V.comp (CC p y) ∧
        ‖J.symm.toContinuousLinearMap‖≤b :=
    (parameter_graph_horizontal_inverse (T p) (AA p y) (BB p y) (CC p y)
      a ε (ha p) hsmall (hblock p y).1 (hblock p y).2.1 (hblock p y).2.2.1).2 V hV
  have hFeq (p:A) (y:Y p) (V:Y (h p)→L[ℝ] X (h p)) (hV:‖V‖≤1) :
      (AA p y-V.comp (CC p y)).comp (F p (y,V))=V.comp (DD p y)-BB p y := by
    obtain ⟨J,hJ,_⟩ := hInv p y V hV
    dsimp [F]
    rw [←hJ,ContinuousLinearMap.inverse_equiv]
    ext v
    simp
  have hFn (p:A) (y:Y p) (V:Y (h p)→L[ℝ] X (h p)) (hV:‖V‖≤1) :
      ‖F p (y,V)‖≤q := by
    rw [hqeq]
    exact (parameter_graph_preimage_slope_interior (T p) (AA p y) (BB p y)
      (CC p y) (DD p y) a k ε (ha p) (hblock p y).1 (hblock p y).2.1
      (hblock p y).2.2.1 (hblock p y).2.2.2 hsmall hjet V _ hV (hFeq p y V hV)).1
  have hFv (p:A) (y:Y p) (V W:Y (h p)→L[ℝ]X (h p)) (hV:‖V‖≤1) (hW:‖W‖≤1) :
      ‖F p (y,V)-F p (y,W)‖≤(q:ℝ)*‖V-W‖ := by
    obtain ⟨J,hJ,hJn⟩ := hInv p y V hV
    have hc := (parameter_graph_slope_comparison (AA p y) (BB p y) (CC p y) (DD p y)
      b (k+ε) ε (by simpa using (hblock p y).2.2.2)).2 V W (F p (y,V)) (F p (y,W))
      J hJ hJn (hFeq p y V hV) (hFeq p y W hW) ((hFn p y W hW).trans hq.le)
      (hblock p y).2.2.1
    convert hc using 1
    dsimp [q]
    ring
  have hfix (p:A) (y:Y p) : P p y=F p (y,P (h p) (R p y)) := by
    obtain ⟨J,hJ,_⟩ := hInv p y _ (hPunit (h p) (R p y))
    have he := heq p y
    rw [←hJ] at he
    dsimp [F]
    rw [←hJ,ContinuousLinearMap.inverse_equiv]
    ext v
    have hv := congrArg J.symm (DFunLike.congr_fun he v)
    simpa using hv
  have hRL (p:A) : LipschitzWith (k+ε) (R p) := by
    apply lipschitzWith_iff_norm_sub_le.mpr
    intro y z
    have htz : ‖t p y-t p z‖≤‖y-z‖ := by simpa using (htL p).norm_sub_le y z
    have hv := parameter_graph_vertical_estimate (T p).toContinuousLinearMap (S p)
      (G p) k ε (hk p) (hpert p) (t p y) (t p z) y z
    simpa only [max_eq_right htz,NNReal.coe_add,add_mul] using hv
  have hRzero (p:A) : R p 0=0 := by
    change (G p (t p 0,0)).2=0
    rw [htzero]
    exact congrArg Prod.snd (hzero p)
  have htgraph : JointFiberContDiff e.second e.total id n (fun p y ↦ (t p y,y)) :=
    jointFiberContDiffOn_univ_iff.mp (parameter_graph_local_joint_split_pair
      e.second e n univ isOpen_univ t (fun _ y ↦ y)
      (jointFiberContDiffOn_univ_iff.mpr ht)
      (jointFiberContDiffOn_univ_iff.mpr (parameter_graph_joint_id e.second n)))
  have hGn : JointFiberContDiff e.total e.total h n G :=
    ⟨fun p ↦ (hG.1 p).of_le (by exact_mod_cast Nat.le_succ n),
      fun i j m hm ↦ hG.2 i j m (hm.trans (Nat.le_succ n))⟩
  have hGgraph := parameter_graph_joint_comp e.second e.total e.total id continuous_id h hh
    (fun p y ↦ (t p y,y)) G n htgraph hGn
  have hsnd := parameter_graph_joint_linear e.total e.second id continuous_id
    (fun p ↦ ContinuousLinearMap.snd ℝ (X p) (Y p))
    (parameter_graph_atlas_split_projections_continuous e).2 n
  have hRjoint : JointFiberContDiff e.second e.second h n R :=
    parameter_graph_joint_comp e.second e.total e.second h hh id continuous_id
      (fun p y ↦ G p (t p y,y)) (fun _ z ↦ z.2) n hGgraph hsnd
  let := ParameterGraphHomAtlas.topology e.second e.first
  let qatlas := ParameterGraphHomAtlas.atlas e.second e.first
  have hPzero : JointFiberContDiff e.second qatlas id 0 P :=
    jointFiberContDiffOn_univ_iff.mp (parameter_graph_local_joint_derivative e.second e.first
      t 0 univ isOpen_univ (jointFiberContDiffOn_univ_iff.mpr ht1))
  have hPc := parameter_graph_joint_value_continuous e.second qatlas id continuous_id P 0 hPzero
  let := ParameterGraphPullbackAtlas.topology e.first h hh
  let := ParameterGraphPullbackAtlas.topology e.second h hh
  let xp := ParameterGraphPullbackAtlas.atlas e.first h hh
  let yp := ParameterGraphPullbackAtlas.atlas e.second h hh
  obtain ⟨hAA,hBB,hCC,hDD⟩ := parameter_graph_local_joint_derivative_blocks e.second e e h hh n
    univ isOpen_univ univ isOpen_univ G (fun p y ↦ (t p y,y))
    (jointFiberContDiffOn_univ_iff.mpr hG) (jointFiberContDiffOn_univ_iff.mpr htgraph)
    (fun _ _ ↦ mem_univ _)
  let qp := ParameterGraphPullbackAtlas.atlas qatlas h hh
  let := ParameterGraphPullbackAtlas.topology qatlas h hh
  let := ParameterGraphProductAtlas.topology (E := Y) (F := fun p ↦ Y (h p)→L[ℝ]X (h p))
  let z := ParameterGraphProductAtlas.atlas e.second qp
  have hQ := parameter_graph_joint_comp z qp (ParameterGraphHomAtlas.atlas yp xp)
    id continuous_id id continuous_id (fun _ w ↦ w.2) (fun _ Q ↦ Q) n
    (parameter_graph_joint_native_snd e.second qp n)
    (parameter_graph_joint_hom_pullback e.second e.first h hh n)
  let := ParameterGraphHomAtlas.topology e.first xp
  let := ParameterGraphHomAtlas.topology e.second xp
  let := ParameterGraphHomAtlas.topology e.first yp
  let := ParameterGraphHomAtlas.topology e.second yp
  obtain ⟨hW,hF⟩ := parameter_graph_local_joint_preimage_rational z e.first e.second xp yp
    n univ isOpen_univ (fun p w ↦ AA p w.1) (fun p w ↦ BB p w.1)
    (fun p w ↦ CC p w.1) (fun p w ↦ DD p w.1) (fun _ w ↦ w.2)
    (parameter_graph_local_joint_comp_fst e.second qp (ParameterGraphHomAtlas.atlas e.first xp)
      n univ isOpen_univ AA hAA)
    (parameter_graph_local_joint_comp_fst e.second qp (ParameterGraphHomAtlas.atlas e.second xp)
      n univ isOpen_univ BB hBB)
    (parameter_graph_local_joint_comp_fst e.second qp (ParameterGraphHomAtlas.atlas e.first yp)
      n univ isOpen_univ CC hCC)
    (parameter_graph_local_joint_comp_fst e.second qp (ParameterGraphHomAtlas.atlas e.second yp)
      n univ isOpen_univ DD hDD)
    (jointFiberContDiffOn_univ_iff.mpr hQ)
  have hregular := parameter_graph_global_section_regularity e.second qatlas h hh R F P n
    (k+ε) q (by simpa using hstrong) hq hRL hRzero hRjoint hPc (q:ℝ) 1 hq hPn hfix
    (by
      intro p y
      apply LipschitzOnWith.of_dist_le_mul
      intro V hV W hW
      simpa only [dist_eq_norm] using hFv p y V W
        (by simpa using hV) (by simpa using hW))
    _ hW hF (by
      intro p y V hV
      obtain ⟨J,hJ,_⟩ := hInv p y V hV
      exact ⟨mem_univ _,⟨J,hJ⟩⟩)
  exact parameter_graph_joint_of_derivative e.second e.first t n
    (parameter_graph_joint_value_continuous e.second e.first id continuous_id t n ht)
    htd hregular

end HolomorphicAnosov
