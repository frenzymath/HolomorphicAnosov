import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphAtlasOperations
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphJointJetCriterion
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphLocalFiberRegularity
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphLocalJointJetCriterion
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphLocalJointJetNorm
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphProductAtlas
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphHomAtlas
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphJointComposition
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphJointProductPullback

noncomputable section
open scoped ContDiff
namespace HolomorphicAnosov
open Set _root_.Topology
section Formula
open scoped BigOperators ContDiff
variable {W H : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
 [NormedAddCommGroup H] [NormedSpace ℝ H]
def parameterGraphBilinearMultilinear (B : W →L[ℝ] W →L[ℝ] H) : W [×2]→L[ℝ] H :=
  (((continuousMultilinearCurryFin1 ℝ W H).symm.toContinuousLinearEquiv.toContinuousLinearMap).comp B).uncurryLeft
lemma parameterGraphBilinearMultilinear_apply (B : W →L[ℝ] W →L[ℝ] H) (v : Fin 2 → W) :
    parameterGraphBilinearMultilinear B v = B (v 0) (v 1) := by
  simp [parameterGraphBilinearMultilinear, ContinuousLinearMap.uncurryLeft_apply, Fin.tail_def]
lemma parameter_graph_bilinear_diagonal_jet (B : W →L[ℝ] W →L[ℝ] H) (m : ℕ) (x : W) (v : Fin m → W) :
    iteratedFDeriv ℝ m (fun x ↦ B x x) x v =
    ∑ e : Fin m ↪ Fin 2, B
      (if h : (0 : Fin 2) ∈ Set.range e then v (e.toEquivRange.symm ⟨0,h⟩) else x)
      (if h : (1 : Fin 2) ∈ Set.range e then v (e.toEquivRange.symm ⟨1,h⟩) else x) := by
  classical
  let d : W →L[ℝ] (Fin 2 → W) := ContinuousLinearMap.pi (fun _ ↦ ContinuousLinearMap.id ℝ W)
  have he : (fun x ↦ B x x) = (parameterGraphBilinearMultilinear B) ∘ d := by
    funext x
    simp [parameterGraphBilinearMultilinear_apply,d]
  have hq : ContDiff ℝ (m : ℕ∞ω) (parameterGraphBilinearMultilinear B) := by
    convert (B.contDiff.comp (contDiff_apply ℝ W (0 : Fin 2))).clm_apply
      (contDiff_apply ℝ W (1 : Fin 2)) using 1
    ext w
    exact parameterGraphBilinearMultilinear_apply B w
  rw [he,d.iteratedFDeriv_comp_right hq x le_rfl]
  simp only [ContinuousMultilinearMap.iteratedFDeriv_eq,ContinuousMultilinearMap.iteratedFDeriv,
    ContinuousMultilinearMap.compContinuousLinearMap_apply,sum_apply,
    ContinuousMultilinearMap.iteratedFDerivComponent_apply,parameterGraphBilinearMultilinear_apply,d]
  apply Finset.sum_congr rfl
  intro e _
  split_ifs <;> simp only [ContinuousLinearMap.pi_apply, ContinuousLinearMap.id_apply, Pi.compRightL_apply] <;> congr 2
  all_goals (congr 4; exact Subsingleton.elim _ _)

end Formula

/-- A continuous family of bilinear forms has jointly continuous fibre jets
of every order on its diagonal. The multilinear Taylor formula expresses each
jet as a finite sum indexed by embeddings into two slots. In each summand a
slot is either the anchor or one of the tested tangent vectors, so original
evaluation continuity suffices. -/
theorem parameter_graph_joint_diagonal_bilinear
    {A : Type*} [TopologicalSpace A] {W H : A → Type*}
    [∀p,NormedAddCommGroup (W p)] [∀p,NormedSpace ℝ (W p)]
    [∀p,NormedAddCommGroup (H p)] [∀p,NormedSpace ℝ (H p)]
    [TopologicalSpace (Sigma W)] [TopologicalSpace (Sigma H)]
    (w : FiniteRankNormedAtlas (E := W)) (h : FiniteRankNormedAtlas (E := H))
    (B : ∀p,W p →L[ℝ] W p →L[ℝ] H p)
    (hB : letI := ParameterGraphProductAtlas.topology (E := W) (F := W)
      Continuous (fun z : Sigma (fun p ↦ W p × W p) ↦
        (⟨z.1,B z.1 z.2.1 z.2.2⟩ : Sigma H))) (r : ℕ) :
    JointFiberContDiff w h id r (fun p x ↦ B p x x) := by
  classical
  apply parameter_graph_joint_jet_criterion
  · intro p
    exact ((B p).contDiff.comp contDiff_id).clm_apply contDiff_id
  intro i m hm
  let Z := (w.chart i).baseSet ×
    (FiniteFiberModel (w.rank i) × (Fin m → FiniteFiberModel (w.rank i)))
  let p : Z → A := fun z ↦ z.1.1
  let x : ∀z:Z,W (p z) := fun z ↦ (w.coordinates i z.1.1 z.1.2).symm z.2.1
  let v : ∀z:Z,Fin m → W (p z) := fun z j ↦ (w.coordinates i z.1.1 z.1.2).symm (z.2.2 j)
  have hp : Continuous p := continuous_subtype_val.comp continuous_fst
  have hx : Continuous (fun z:Z ↦ (⟨p z,x z⟩ : Sigma W)) :=
    (atlas_frame_continuous w i).comp (continuous_fst.prodMk continuous_snd.fst)
  have hv (j:Fin m) : Continuous (fun z:Z ↦ (⟨p z,v z j⟩ : Sigma W)) :=
    (atlas_frame_continuous w i).comp (continuous_fst.prodMk
      ((continuous_apply j).comp continuous_snd.snd))
  let a (e : Fin m ↪ Fin 2) (j : Fin 2) (z : Z) : W (p z) :=
    if hj : j∈Set.range e then v z (e.toEquivRange.symm ⟨j,hj⟩) else x z
  have ha (e : Fin m ↪ Fin 2) (j : Fin 2) :
      Continuous (fun z:Z ↦ (⟨p z,a e j z⟩ : Sigma W)) := by
    dsimp [a]
    split_ifs with hj
    · exact hv _
    · exact hx
  have ht (e : Fin m ↪ Fin 2) :
      Continuous (fun z:Z ↦ (⟨p z,B (p z) (a e 0 z) (a e 1 z)⟩ : Sigma H)) := by
    let := ParameterGraphProductAtlas.topology (E := W) (F := W)
    exact hB.comp (ParameterGraphProductAtlas.continuous_mk p (a e 0) (a e 1) (ha e 0) (ha e 1))
  have hs := parameter_graph_atlas_sum_continuous h p hp Finset.univ
    (fun e z ↦ B (p z) (a e 0 z) (a e 1 z)) (fun e _ ↦ ht e)
  change Continuous (fun z:Z ↦ (⟨p z,
    iteratedFDeriv ℝ m (fun x ↦ B (p z) x x) (x z) (v z)⟩ : Sigma H))
  apply hs.congr
  intro z
  congr 1
  exact (parameter_graph_bilinear_diagonal_jet (B (p z)) m (x z) (v z)).symm



/-- Native operator application is jointly smooth in the genuine Hom and
product atlases. Its bilinear evaluation is continuous by the Hom-atlas
continuity theorem, and hence every spatial jet is continuous. -/
theorem parameter_graph_joint_native_apply
    {A : Type*} [TopologicalSpace A] {E F : A → Type*}
    [∀p,NormedAddCommGroup (E p)] [∀p,NormedSpace ℝ (E p)]
    [∀p,NormedAddCommGroup (F p)] [∀p,NormedSpace ℝ (F p)]
    [TopologicalSpace (Sigma E)] [TopologicalSpace (Sigma F)]
    (e : FiniteRankNormedAtlas (E := E)) (f : FiniteRankNormedAtlas (E := F)) (r : ℕ) :
    letI := ParameterGraphHomAtlas.topology e f
    letI := ParameterGraphProductAtlas.topology (E := fun p ↦ E p →L[ℝ] F p) (F := E)
    JointFiberContDiff (ParameterGraphProductAtlas.atlas (ParameterGraphHomAtlas.atlas e f) e)
      f id r (fun _ z ↦ z.1 z.2) := by
  let := ParameterGraphHomAtlas.topology e f
  let W := fun p ↦ (E p →L[ℝ] F p) × E p
  let := ParameterGraphProductAtlas.topology (E := fun p ↦ E p →L[ℝ] F p) (F := E)
  let w : FiniteRankNormedAtlas (E := W) :=
    ParameterGraphProductAtlas.atlas (ParameterGraphHomAtlas.atlas e f) e
  let B (p:A) : W p →L[ℝ] W p →L[ℝ] F p :=
    (ContinuousLinearMap.id ℝ (E p →L[ℝ] F p)).bilinearComp
      (ContinuousLinearMap.fst ℝ _ _) (ContinuousLinearMap.snd ℝ _ _)
  apply parameter_graph_joint_diagonal_bilinear w f B ?_ r
  let := ParameterGraphProductAtlas.topology (E := W) (F := W)
  let Z := Sigma (fun p ↦ W p × W p)
  have h₁ : Continuous (fun z:Z ↦ (⟨z.1,z.2.1⟩ : Sigma W)) :=
    ParameterGraphProductAtlas.fst_continuous
  have h₂ : Continuous (fun z:Z ↦ (⟨z.1,z.2.2⟩ : Sigma W)) :=
    ParameterGraphProductAtlas.snd_continuous
  have hp : Continuous (fun z:Z ↦ z.1) :=
    (parameter_graph_atlas_projection_continuous w).comp h₁
  exact ParameterGraphHomAtlas.continuous_apply e f (fun z:Z ↦ z.1) hp
    (fun z ↦ z.2.1.1) (fun z ↦ z.2.2.2)
    (ParameterGraphProductAtlas.fst_continuous.comp h₁)
    (ParameterGraphProductAtlas.snd_continuous.comp h₂)

/-- Composition of two continuous original operator families is continuous in
the genuine Hom topology, since applying the composite to a frame vector is
two successive continuous evaluations. -/
theorem parameter_graph_hom_comp_continuous
    {A Z : Type*} [TopologicalSpace A] [TopologicalSpace Z] {E F H : A → Type*}
    [∀p,NormedAddCommGroup (E p)] [∀p,NormedSpace ℝ (E p)]
    [∀p,NormedAddCommGroup (F p)] [∀p,NormedSpace ℝ (F p)]
    [∀p,NormedAddCommGroup (H p)] [∀p,NormedSpace ℝ (H p)]
    [TopologicalSpace (Sigma E)] [TopologicalSpace (Sigma F)] [TopologicalSpace (Sigma H)]
    (e : FiniteRankNormedAtlas (E := E)) (f : FiniteRankNormedAtlas (E := F))
    (h : FiniteRankNormedAtlas (E := H))
    (p:Z→A) (hp:Continuous p) (L:∀z,F (p z)→L[ℝ] H (p z))
    (M:∀z,E (p z)→L[ℝ] F (p z))
    (hL : letI := ParameterGraphHomAtlas.topology f h
      Continuous (fun z ↦ (⟨p z,L z⟩ : Sigma (fun p ↦ F p →L[ℝ] H p))))
    (hM : letI := ParameterGraphHomAtlas.topology e f
      Continuous (fun z ↦ (⟨p z,M z⟩ : Sigma (fun p ↦ E p →L[ℝ] F p)))) :
    letI := ParameterGraphHomAtlas.topology e h
    Continuous (fun z ↦ (⟨p z,(L z).comp (M z)⟩ : Sigma (fun p ↦ E p →L[ℝ] H p))) := by
  let := ParameterGraphHomAtlas.topology e h
  apply ParameterGraphHomAtlas.continuous_of_evaluation e h p hp
  intro i v
  let S := {z:Z // p z∈(e.chart i).baseSet}
  have hp' : Continuous (fun z:S ↦ p z.1) := hp.comp continuous_subtype_val
  have hv : Continuous (fun z:S ↦
      (⟨p z.1,(e.coordinates i (p z.1) z.2).symm v⟩ : Sigma E)) :=
    (atlas_frame_continuous e i).comp
      ((hp'.subtype_mk (fun z:S ↦ z.2)).prodMk continuous_const)
  let := ParameterGraphHomAtlas.topology e f
  let := ParameterGraphHomAtlas.topology f h
  exact ParameterGraphHomAtlas.continuous_apply f h (fun z:S ↦ p z.1) hp'
    (fun z ↦ L z.1) (fun z ↦ M z.1 ((e.coordinates i (p z.1) z.2).symm v))
    (hL.comp continuous_subtype_val)
    (ParameterGraphHomAtlas.continuous_apply e f (fun z:S ↦ p z.1) hp'
      (fun z ↦ M z.1) _ (hM.comp continuous_subtype_val) hv)

/-- Native operator composition is jointly smooth. The bilinear coefficient
is the usual continuous-linear composition map; continuity of its original
bundle evaluation follows by testing on source frame vectors. -/
theorem parameter_graph_joint_native_comp
    {A : Type*} [TopologicalSpace A] {E F H : A → Type*}
    [∀p,NormedAddCommGroup (E p)] [∀p,NormedSpace ℝ (E p)]
    [∀p,NormedAddCommGroup (F p)] [∀p,NormedSpace ℝ (F p)]
    [∀p,NormedAddCommGroup (H p)] [∀p,NormedSpace ℝ (H p)]
    [TopologicalSpace (Sigma E)] [TopologicalSpace (Sigma F)] [TopologicalSpace (Sigma H)]
    (e : FiniteRankNormedAtlas (E := E)) (f : FiniteRankNormedAtlas (E := F))
    (h : FiniteRankNormedAtlas (E := H)) (r : ℕ) :
    letI := ParameterGraphHomAtlas.topology f h
    letI := ParameterGraphHomAtlas.topology e f
    letI := ParameterGraphHomAtlas.topology e h
    letI := ParameterGraphProductAtlas.topology
      (E := fun p ↦ F p →L[ℝ] H p) (F := fun p ↦ E p →L[ℝ] F p)
    JointFiberContDiff (ParameterGraphProductAtlas.atlas (ParameterGraphHomAtlas.atlas f h)
      (ParameterGraphHomAtlas.atlas e f)) (ParameterGraphHomAtlas.atlas e h)
      id r (fun _ z ↦ z.1.comp z.2) := by
  let := ParameterGraphHomAtlas.topology f h
  let := ParameterGraphHomAtlas.topology e f
  let := ParameterGraphHomAtlas.topology e h
  let W := fun p ↦ (F p →L[ℝ] H p) × (E p →L[ℝ] F p)
  let := ParameterGraphProductAtlas.topology
    (E := fun p ↦ F p →L[ℝ] H p) (F := fun p ↦ E p →L[ℝ] F p)
  let w : FiniteRankNormedAtlas (E := W) :=
    ParameterGraphProductAtlas.atlas (ParameterGraphHomAtlas.atlas f h)
      (ParameterGraphHomAtlas.atlas e f)
  let B (p:A) : W p →L[ℝ] W p →L[ℝ] (E p →L[ℝ] H p) :=
    (ContinuousLinearMap.compL ℝ (E p) (F p) (H p)).bilinearComp
      (ContinuousLinearMap.fst ℝ _ _) (ContinuousLinearMap.snd ℝ _ _)
  apply parameter_graph_joint_diagonal_bilinear w (ParameterGraphHomAtlas.atlas e h) B ?_ r
  let := ParameterGraphProductAtlas.topology (E := W) (F := W)
  let Z := Sigma (fun p ↦ W p × W p)
  have h₁ : Continuous (fun z:Z ↦ (⟨z.1,z.2.1⟩ : Sigma W)) :=
    ParameterGraphProductAtlas.fst_continuous
  have h₂ : Continuous (fun z:Z ↦ (⟨z.1,z.2.2⟩ : Sigma W)) :=
    ParameterGraphProductAtlas.snd_continuous
  have hp : Continuous (fun z:Z ↦ z.1) :=
    (parameter_graph_atlas_projection_continuous w).comp h₁
  exact parameter_graph_hom_comp_continuous e f h (fun z:Z ↦ z.1) hp
    (fun z ↦ z.2.1.1) (fun z ↦ z.2.2.2)
    (ParameterGraphProductAtlas.fst_continuous.comp h₁)
    (ParameterGraphProductAtlas.snd_continuous.comp h₂)


/-- Application of a jointly C^r original operator family to a jointly C^r
vector family is jointly C^r on their common open original domain. -/
theorem parameter_graph_local_joint_clm_apply
    {A : Type*} [TopologicalSpace A] {X E F : A → Type*}
    [∀p,NormedAddCommGroup (X p)] [∀p,NormedSpace ℝ (X p)]
    [∀p,NormedAddCommGroup (E p)] [∀p,NormedSpace ℝ (E p)]
    [∀p,NormedAddCommGroup (F p)] [∀p,NormedSpace ℝ (F p)]
    [TopologicalSpace (Sigma X)] [TopologicalSpace (Sigma E)] [TopologicalSpace (Sigma F)]
    (x : FiniteRankNormedAtlas (E := X)) (e : FiniteRankNormedAtlas (E := E))
    (f : FiniteRankNormedAtlas (E := F)) (r : ℕ) (U : Set (Sigma X)) (hU : IsOpen U)
    (L : ∀p,X p → E p →L[ℝ] F p) (v : ∀p,X p → E p)
    (hL : letI := ParameterGraphHomAtlas.topology e f
      JointFiberContDiffOn x (ParameterGraphHomAtlas.atlas e f) id r U L)
    (hv : JointFiberContDiffOn x e id r U v) :
    JointFiberContDiffOn x f id r U (fun p z ↦ L p z (v p z)) := by
  let := ParameterGraphHomAtlas.topology e f
  let := ParameterGraphProductAtlas.topology (E := fun p ↦ E p →L[ℝ] F p) (F := E)
  exact parameter_graph_local_joint_comp x
    (ParameterGraphProductAtlas.atlas (ParameterGraphHomAtlas.atlas e f) e) f
    id continuous_id id continuous_id (fun p z ↦ (L p z,v p z)) (fun _ z ↦ z.1 z.2)
    r U univ hU isOpen_univ
    (parameter_graph_local_joint_pair x (ParameterGraphHomAtlas.atlas e f) e
      id continuous_id r U hU L v hL hv)
    (jointFiberContDiffOn_univ_iff.mpr (parameter_graph_joint_native_apply e f r))
    (fun _ _ ↦ mem_univ _)

/-- Composition of jointly C^r original operator families is jointly C^r in
the genuine Hom atlas on their common open original domain. -/
theorem parameter_graph_local_joint_clm_comp
    {A : Type*} [TopologicalSpace A] {X E F H : A → Type*}
    [∀p,NormedAddCommGroup (X p)] [∀p,NormedSpace ℝ (X p)]
    [∀p,NormedAddCommGroup (E p)] [∀p,NormedSpace ℝ (E p)]
    [∀p,NormedAddCommGroup (F p)] [∀p,NormedSpace ℝ (F p)]
    [∀p,NormedAddCommGroup (H p)] [∀p,NormedSpace ℝ (H p)]
    [TopologicalSpace (Sigma X)] [TopologicalSpace (Sigma E)]
    [TopologicalSpace (Sigma F)] [TopologicalSpace (Sigma H)]
    (x : FiniteRankNormedAtlas (E := X)) (e : FiniteRankNormedAtlas (E := E))
    (f : FiniteRankNormedAtlas (E := F)) (h : FiniteRankNormedAtlas (E := H))
    (r : ℕ) (U : Set (Sigma X)) (hU : IsOpen U)
    (L : ∀p,X p → F p →L[ℝ] H p) (M : ∀p,X p → E p →L[ℝ] F p)
    (hL : letI := ParameterGraphHomAtlas.topology f h
      JointFiberContDiffOn x (ParameterGraphHomAtlas.atlas f h) id r U L)
    (hM : letI := ParameterGraphHomAtlas.topology e f
      JointFiberContDiffOn x (ParameterGraphHomAtlas.atlas e f) id r U M) :
    letI := ParameterGraphHomAtlas.topology e h
    JointFiberContDiffOn x (ParameterGraphHomAtlas.atlas e h) id r U
      (fun p z ↦ (L p z).comp (M p z)) := by
  let := ParameterGraphHomAtlas.topology f h
  let := ParameterGraphHomAtlas.topology e f
  let := ParameterGraphHomAtlas.topology e h
  let := ParameterGraphProductAtlas.topology
    (E := fun p ↦ F p →L[ℝ] H p) (F := fun p ↦ E p →L[ℝ] F p)
  exact parameter_graph_local_joint_comp x
    (ParameterGraphProductAtlas.atlas (ParameterGraphHomAtlas.atlas f h)
      (ParameterGraphHomAtlas.atlas e f)) (ParameterGraphHomAtlas.atlas e h)
    id continuous_id id continuous_id (fun p z ↦ (L p z,M p z)) (fun _ z ↦ z.1.comp z.2)
    r U univ hU isOpen_univ
    (parameter_graph_local_joint_pair x (ParameterGraphHomAtlas.atlas f h)
      (ParameterGraphHomAtlas.atlas e f) id continuous_id r U hU L M hL hM)
    (jointFiberContDiffOn_univ_iff.mpr (parameter_graph_joint_native_comp e f h r))
    (fun _ _ ↦ mem_univ _)


/-- Addition preserves local joint fibre regularity in any original finite-rank
atlas, including the genuine Hom atlas. Each original iterated derivative is
the sum of the two input jets, and original bundle addition is continuous. -/
theorem parameter_graph_local_joint_add
    {A : Type*} [TopologicalSpace A] {E F : A → Type*}
    [∀p,NormedAddCommGroup (E p)] [∀p,NormedSpace ℝ (E p)]
    [∀p,NormedAddCommGroup (F p)] [∀p,NormedSpace ℝ (F p)]
    [TopologicalSpace (Sigma E)] [TopologicalSpace (Sigma F)]
    (e : FiniteRankNormedAtlas (E := E)) (f : FiniteRankNormedAtlas (E := F))
    (r : ℕ) (U : Set (Sigma E)) (hU : IsOpen U) (g k : ∀p,E p → F p)
    (hg : JointFiberContDiffOn e f id r U g) (hk : JointFiberContDiffOn e f id r U k) :
    JointFiberContDiffOn e f id r U (fun p x ↦ g p x + k p x) := by
  apply parameter_graph_local_joint_jet_criterion
  · intro z hz
    exact (hg.1 z hz).add (hk.1 z hz)
  intro i m hm
  rw [continuousOn_iff_continuous_domRestrict]
  let S : Set ((e.chart i).baseSet ×
      (FiniteFiberModel (e.rank i) × (Fin m → FiniteFiberModel (e.rank i)))) :=
    {z | (⟨z.1.val,(e.coordinates i z.1.val z.1.property).symm z.2.1⟩ : Sigma E) ∈ U}
  let p : S → A := fun z ↦ z.1.1.1
  let x (z : S) := (e.coordinates i z.1.1.1 z.1.1.2).symm z.1.2.1
  let v (z : S) (a : Fin m) := (e.coordinates i z.1.1.1 z.1.1.2).symm (z.1.2.2 a)
  have hp : Continuous p := continuous_subtype_val.comp continuous_subtype_val.fst
  have hx : Continuous (fun z : S ↦ (⟨p z,x z⟩ : Sigma E)) :=
    (atlas_frame_continuous e i).comp
      (continuous_subtype_val.fst.prodMk continuous_subtype_val.snd.fst)
  have hv (a : Fin m) : Continuous (fun z : S ↦ (⟨p z,v z a⟩ : Sigma E)) :=
    (atlas_frame_continuous e i).comp (continuous_subtype_val.fst.prodMk
      ((continuous_apply a).comp continuous_subtype_val.snd.snd))
  have hjg := parameter_graph_local_jet_evaluation_continuous e f id continuous_id
    g r m hm U hU hg p hp x hx (fun z ↦ z.2) v hv
  have hjk := parameter_graph_local_jet_evaluation_continuous e f id continuous_id
    k r m hm U hU hk p hp x hx (fun z ↦ z.2) v hv
  have hc := parameter_graph_atlas_add_continuous f p hp
    (fun z ↦ iteratedFDeriv ℝ m (g (p z)) (x z) (v z))
    (fun z ↦ iteratedFDeriv ℝ m (k (p z)) (x z) (v z)) hjg hjk
  apply hc.congr
  intro z
  change (⟨p z,_+_⟩ : Sigma F) = ⟨p z,
    iteratedFDeriv ℝ m (g (p z) + k (p z)) (x z) (v z)⟩
  rw [iteratedFDeriv_add_apply ((hg.1 _ z.2).of_le (by exact_mod_cast hm))
    ((hk.1 _ z.2).of_le (by exact_mod_cast hm))]
  rfl

end HolomorphicAnosov
