import HolomorphicAnosov.Dynamics.StableManifold.FiniteRankAtlasFrameContinuity
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphHomAtlas
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphJointComposition
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphJointProductPullback
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphLocalFiberRegularity
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphProductAtlas
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphPullbackAtlas
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphJointBilinearOperations
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphJointDerivativeCriterion

noncomputable section
open Set _root_.Topology
open scoped ContDiff
namespace HolomorphicAnosov

/-- Pulling back the original Hom bundle and taking Hom between the two
pulled-back bundles give compatible joint smooth structures. The identity
operator on each fibre is jointly smooth: test its evaluation on pulled-back
source frames, forget to the original total spaces, apply original Hom
evaluation, then restore the receiving pullback topology. -/
theorem parameter_graph_joint_hom_pullback
    {A B : Type*} [TopologicalSpace A] [TopologicalSpace B] {E F : B → Type*}
    [∀p,NormedAddCommGroup (E p)] [∀p,NormedSpace ℝ (E p)]
    [∀p,NormedAddCommGroup (F p)] [∀p,NormedSpace ℝ (F p)]
    [TopologicalSpace (Sigma E)] [TopologicalSpace (Sigma F)]
    (e : FiniteRankNormedAtlas (E := E)) (f : FiniteRankNormedAtlas (E := F))
    (b : A → B) (hb : Continuous b) (r : ℕ) :
    letI := ParameterGraphHomAtlas.topology e f
    letI := ParameterGraphPullbackAtlas.topology e b hb
    letI := ParameterGraphPullbackAtlas.topology f b hb
    letI := ParameterGraphPullbackAtlas.topology (ParameterGraphHomAtlas.atlas e f) b hb
    let ep := ParameterGraphPullbackAtlas.atlas e b hb
    let fp := ParameterGraphPullbackAtlas.atlas f b hb
    @JointFiberContDiff A _ (fun p ↦ E (b p) →L[ℝ] F (b p)) _ _
      (ParameterGraphPullbackAtlas.topology (ParameterGraphHomAtlas.atlas e f) b hb)
      A _ (fun p ↦ E (b p) →L[ℝ] F (b p)) _ _ (ParameterGraphHomAtlas.topology ep fp)
      (ParameterGraphPullbackAtlas.atlas (ParameterGraphHomAtlas.atlas e f) b hb)
      (ParameterGraphHomAtlas.atlas ep fp) id r (fun _ L ↦ L) := by
  let := ParameterGraphHomAtlas.topology e f
  let := ParameterGraphPullbackAtlas.topology e b hb
  let := ParameterGraphPullbackAtlas.topology f b hb
  let ep := ParameterGraphPullbackAtlas.atlas e b hb
  let fp := ParameterGraphPullbackAtlas.atlas f b hb
  let qp := ParameterGraphPullbackAtlas.atlas (ParameterGraphHomAtlas.atlas e f) b hb
  let := ParameterGraphPullbackAtlas.topology (ParameterGraphHomAtlas.atlas e f) b hb
  apply parameter_graph_joint_linear qp (ParameterGraphHomAtlas.atlas ep fp)
    id continuous_id (fun p ↦ ContinuousLinearMap.id ℝ _) ?_ r
  let Z := Sigma (fun p:A ↦ E (b p) →L[ℝ] F (b p))
  have hp : Continuous (fun z:Z ↦ z.1) := parameter_graph_atlas_projection_continuous qp
  apply ParameterGraphHomAtlas.continuous_of_evaluation ep fp (fun z:Z ↦ z.1) hp
  intro i v
  let S := {z:Z // z.1∈(ep.chart i).baseSet}
  have hp' : Continuous (fun z:S ↦ z.1.1) := hp.comp continuous_subtype_val
  have hv : Continuous (fun z:S ↦
      (⟨z.1.1,(ep.coordinates i z.1.1 z.2).symm v⟩ : Sigma (fun p ↦ E (b p)))) :=
    (atlas_frame_continuous ep i).comp
      ((hp'.subtype_mk (fun z:S ↦ z.2)).prodMk continuous_const)
  apply (ParameterGraphPullbackAtlas.continuous_mk_iff f b hb (fun z:S ↦ z.1.1) _).mpr
  refine ⟨hp',?_⟩
  exact ParameterGraphHomAtlas.continuous_apply e f (fun z:S ↦ b z.1.1) (hb.comp hp')
    (fun z ↦ z.1.2) (fun z ↦ (ep.coordinates i z.1.1 z.2).symm v)
    ((ParameterGraphPullbackAtlas.continuous_original (ParameterGraphHomAtlas.atlas e f) b hb).comp
      continuous_subtype_val)
    ((ParameterGraphPullbackAtlas.continuous_original e b hb).comp hv)


/-- The reverse identity between the Hom of pullbacks and the pullback Hom
is jointly smooth. Original source frames lift continuously to the pulled-back
source; evaluation there is continuous and forgetting the pulled-back target
recovers original evaluation. -/
theorem parameter_graph_joint_hom_pullback_symm
    {A B : Type*} [TopologicalSpace A] [TopologicalSpace B] {E F : B → Type*}
    [∀p,NormedAddCommGroup (E p)] [∀p,NormedSpace ℝ (E p)]
    [∀p,NormedAddCommGroup (F p)] [∀p,NormedSpace ℝ (F p)]
    [TopologicalSpace (Sigma E)] [TopologicalSpace (Sigma F)]
    (e : FiniteRankNormedAtlas (E := E)) (f : FiniteRankNormedAtlas (E := F))
    (b : A → B) (hb : Continuous b) (r : ℕ) :
    letI := ParameterGraphHomAtlas.topology e f
    letI := ParameterGraphPullbackAtlas.topology e b hb
    letI := ParameterGraphPullbackAtlas.topology f b hb
    let ep := ParameterGraphPullbackAtlas.atlas e b hb
    let fp := ParameterGraphPullbackAtlas.atlas f b hb
    @JointFiberContDiff A _ (fun p ↦ E (b p) →L[ℝ] F (b p)) _ _
      (ParameterGraphHomAtlas.topology ep fp)
      A _ (fun p ↦ E (b p) →L[ℝ] F (b p)) _ _
      (ParameterGraphPullbackAtlas.topology (ParameterGraphHomAtlas.atlas e f) b hb)
      (ParameterGraphHomAtlas.atlas ep fp)
      (ParameterGraphPullbackAtlas.atlas (ParameterGraphHomAtlas.atlas e f) b hb)
      id r (fun _ L ↦ L) := by
  let := ParameterGraphHomAtlas.topology e f
  let := ParameterGraphPullbackAtlas.topology e b hb
  let := ParameterGraphPullbackAtlas.topology f b hb
  let ep := ParameterGraphPullbackAtlas.atlas e b hb
  let fp := ParameterGraphPullbackAtlas.atlas f b hb
  let qp := ParameterGraphPullbackAtlas.atlas (ParameterGraphHomAtlas.atlas e f) b hb
  let := ParameterGraphHomAtlas.topology ep fp
  apply parameter_graph_joint_linear (ParameterGraphHomAtlas.atlas ep fp) qp
    id continuous_id (fun p ↦ ContinuousLinearMap.id ℝ _) ?_ r
  let Z := Sigma (fun p:A ↦ E (b p) →L[ℝ] F (b p))
  have hp : Continuous (fun z:Z ↦ z.1) :=
    parameter_graph_atlas_projection_continuous (ParameterGraphHomAtlas.atlas ep fp)
  apply (ParameterGraphPullbackAtlas.continuous_mk_iff
    (ParameterGraphHomAtlas.atlas e f) b hb (fun z:Z ↦ z.1) _).mpr
  refine ⟨hp,?_⟩
  apply ParameterGraphHomAtlas.continuous_of_evaluation e f (fun z:Z ↦ b z.1) (hb.comp hp)
  intro i v
  let S := {z:Z // b z.1∈(e.chart i).baseSet}
  have hp' : Continuous (fun z:S ↦ z.1.1) := hp.comp continuous_subtype_val
  have hv : Continuous (fun z:S ↦
      (⟨z.1.1,(e.coordinates i (b z.1.1) z.2).symm v⟩ : Sigma (fun p ↦ E (b p)))) := by
    apply (ParameterGraphPullbackAtlas.continuous_mk_iff e b hb (fun z:S ↦ z.1.1) _).mpr
    refine ⟨hp',?_⟩
    exact (atlas_frame_continuous e i).comp
      (((hb.comp hp').subtype_mk (fun z:S ↦ z.2)).prodMk continuous_const)
  exact (ParameterGraphPullbackAtlas.continuous_original f b hb).comp
    (ParameterGraphHomAtlas.continuous_apply ep fp (fun z:S ↦ z.1.1) hp'
      (fun z ↦ z.1.2) (fun z ↦ (e.coordinates i (b z.1.1) z.2).symm v)
      continuous_subtype_val hv)

/-- A continuous original family of linear operators, regarded as constant in
an auxiliary spatial variable, has every joint fibre order in the Hom atlas.
Differentiate its jointly smooth native linear evaluation, then pull that
constant derivative field back along the auxiliary zero section. -/
theorem parameter_graph_joint_constant_operator
    {A : Type*} [TopologicalSpace A] {S E F : A → Type*}
    [∀p,NormedAddCommGroup (S p)] [∀p,NormedSpace ℝ (S p)]
    [∀p,NormedAddCommGroup (E p)] [∀p,NormedSpace ℝ (E p)]
    [∀p,NormedAddCommGroup (F p)] [∀p,NormedSpace ℝ (F p)]
    [TopologicalSpace (Sigma S)] [TopologicalSpace (Sigma E)] [TopologicalSpace (Sigma F)]
    (s : FiniteRankNormedAtlas (E := S)) (e : FiniteRankNormedAtlas (E := E))
    (f : FiniteRankNormedAtlas (E := F)) (L : ∀p,E p →L[ℝ] F p)
    (hL : Continuous (fun z:Sigma E ↦ (⟨z.1,L z.1 z.2⟩ : Sigma F))) (r:ℕ) :
    letI := ParameterGraphHomAtlas.topology e f
    JointFiberContDiff s (ParameterGraphHomAtlas.atlas e f) id r (fun p _ ↦ L p) := by
  let := ParameterGraphHomAtlas.topology e f
  have hd := parameter_graph_local_joint_derivative e f (fun p ↦ L p) r univ isOpen_univ
    (jointFiberContDiffOn_univ_iff.mpr
      (parameter_graph_joint_linear e f id continuous_id L hL (r+1)))
  have hd' : JointFiberContDiff e (ParameterGraphHomAtlas.atlas e f) id r
      (fun p _ ↦ L p) := by
    have he : (fun p ↦ fderiv ℝ (L p)) = (fun p _ ↦ L p) := by
      funext p a
      exact (L p).fderiv
    rw [he] at hd
    exact jointFiberContDiffOn_univ_iff.mp hd
  exact parameter_graph_joint_comp s e (ParameterGraphHomAtlas.atlas e f)
    id continuous_id id continuous_id (fun _ _ ↦ 0) (fun p _ ↦ L p) r
    (parameter_graph_joint_zero s e id continuous_id r) hd'

/-- The tangent affine action loses exactly one fibre order. Here T is the
already known receiving value family; no derivative of T is used. Pair x with
T(x), evaluate DF there, and compose it with the sum of the horizontal
inclusion and the vertical inclusion composed with Q and DR. Every operation
is one of the proved original joint bundle calculus rules. -/
theorem parameter_graph_local_joint_tangent_action_core
    {A : Type*} [TopologicalSpace A] {X V Z Y : A → Type*}
    [∀p,NormedAddCommGroup (X p)] [∀p,NormedSpace ℝ (X p)]
    [∀p,NormedAddCommGroup (V p)] [∀p,NormedSpace ℝ (V p)]
    [∀p,NormedAddCommGroup (Z p)] [∀p,NormedSpace ℝ (Z p)]
    [∀p,NormedAddCommGroup (Y p)] [∀p,NormedSpace ℝ (Y p)]
    [TopologicalSpace (Sigma X)] [TopologicalSpace (Sigma V)]
    [TopologicalSpace (Sigma Z)] [TopologicalSpace (Sigma Y)]
    (x : FiniteRankNormedAtlas (E := X)) (v : FiniteRankNormedAtlas (E := V))
    (z : FiniteRankNormedAtlas (E := Z)) (y : FiniteRankNormedAtlas (E := Y))
    (n:ℕ) (U:Set (Sigma X)) (hU:IsOpen U)
    (R:∀p,X p→Z p) (T:∀p,X p→V p) (F:∀p,X p×V p→Y p)
    (hR:JointFiberContDiffOn x z id (n+1) U R)
    (hT:JointFiberContDiffOn x v id n U T)
    (W:Set (Sigma (fun p ↦ X p×V p)))
    (hW: letI := ParameterGraphProductAtlas.topology (E := X) (F := V); IsOpen W)
    (hF: letI := ParameterGraphProductAtlas.topology (E := X) (F := V)
      JointFiberContDiffOn (ParameterGraphProductAtlas.atlas x v) y id (n+1) W F)
    (hmap:∀a∈U,(⟨a.1,(a.2,T a.1 a.2)⟩:Sigma (fun p ↦ X p×V p))∈W) :
    letI := ParameterGraphHomAtlas.topology z v
    letI := ParameterGraphProductAtlas.topology (E := X) (F := fun p ↦ Z p→L[ℝ] V p)
    letI := ParameterGraphHomAtlas.topology x y
    JointFiberContDiffOn (ParameterGraphProductAtlas.atlas x (ParameterGraphHomAtlas.atlas z v))
      (ParameterGraphHomAtlas.atlas x y) id n
      {a:Sigma (fun p ↦ X p×(Z p→L[ℝ] V p)) | (⟨a.1,a.2.1⟩:Sigma X)∈U}
      (fun p a ↦ (fderiv ℝ (F p) (a.1,T p a.1)).comp
        ((ContinuousLinearMap.id ℝ (X p)).prod (a.2.comp (fderiv ℝ (R p) a.1)))) := by
  let := ParameterGraphProductAtlas.topology (E := X) (F := V)
  let d := ParameterGraphProductAtlas.atlas x v
  let := ParameterGraphHomAtlas.topology z v
  let q := ParameterGraphHomAtlas.atlas z v
  let := ParameterGraphProductAtlas.topology (E := X) (F := fun p ↦ Z p→L[ℝ] V p)
  let s := ParameterGraphProductAtlas.atlas x q
  let Ω := {a:Sigma (fun p ↦ X p×(Z p→L[ℝ] V p)) | (⟨a.1,a.2.1⟩:Sigma X)∈U}
  have hΩ : IsOpen Ω := hU.preimage ParameterGraphProductAtlas.fst_continuous
  have hfst : JointFiberContDiffOn s x id n Ω (fun _ a ↦ a.1) :=
    (jointFiberContDiffOn_univ_iff.mpr (parameter_graph_joint_native_fst x q n)).mono (subset_univ _)
  have hsnd : JointFiberContDiffOn s q id n Ω (fun _ a ↦ a.2) :=
    (jointFiberContDiffOn_univ_iff.mpr (parameter_graph_joint_native_snd x q n)).mono (subset_univ _)
  have hT' := parameter_graph_local_joint_comp s x v id continuous_id id continuous_id
    (fun _ a ↦ a.1) T n Ω U hΩ hU hfst hT (fun a ha ↦ ha)
  have hgraph : JointFiberContDiffOn s d id n Ω (fun p a ↦ (a.1,T p a.1)) :=
    parameter_graph_local_joint_pair s x v id continuous_id n Ω hΩ _ _ hfst hT'
  let := ParameterGraphHomAtlas.topology d y
  let := ParameterGraphHomAtlas.topology x z
  let := ParameterGraphHomAtlas.topology x v
  let := ParameterGraphHomAtlas.topology v d
  let := ParameterGraphHomAtlas.topology x d
  let := ParameterGraphHomAtlas.topology x y
  have hDF := parameter_graph_local_joint_derivative d y F n W hW hF
  have hDF' := parameter_graph_local_joint_comp s d (ParameterGraphHomAtlas.atlas d y)
    id continuous_id id continuous_id (fun p a ↦ (a.1,T p a.1))
    (fun p ↦ fderiv ℝ (F p)) n Ω W hΩ hW hgraph hDF
    (fun a ha ↦ hmap ⟨a.1,a.2.1⟩ ha)
  have hDR := parameter_graph_local_joint_derivative x z R n U hU hR
  have hDR' := parameter_graph_local_joint_comp s x (ParameterGraphHomAtlas.atlas x z)
    id continuous_id id continuous_id (fun _ a ↦ a.1) (fun p ↦ fderiv ℝ (R p))
    n Ω U hΩ hU hfst hDR (fun a ha ↦ ha)
  have hQDR := parameter_graph_local_joint_clm_comp s x z v n Ω hΩ
    (fun _ a ↦ a.2) (fun p a ↦ fderiv ℝ (R p) a.1) hsnd hDR'
  have hinl : JointFiberContDiffOn s (ParameterGraphHomAtlas.atlas x d) id n Ω
      (fun p _ ↦ ContinuousLinearMap.inl ℝ (X p) (V p)) := by
    apply (jointFiberContDiffOn_univ_iff.mpr
      (parameter_graph_joint_constant_operator s x d _ ?_ n)).mono (subset_univ _)
    exact ParameterGraphProductAtlas.continuous_mk (fun a:Sigma X ↦ a.1)
      (fun a ↦ a.2) (fun _ ↦ 0) continuous_id
      (parameter_graph_atlas_zero_continuous v _ (parameter_graph_atlas_projection_continuous x))
  have hinr : JointFiberContDiffOn s (ParameterGraphHomAtlas.atlas v d) id n Ω
      (fun p _ ↦ ContinuousLinearMap.inr ℝ (X p) (V p)) := by
    apply (jointFiberContDiffOn_univ_iff.mpr
      (parameter_graph_joint_constant_operator s v d _ ?_ n)).mono (subset_univ _)
    exact ParameterGraphProductAtlas.continuous_mk (fun a:Sigma V ↦ a.1)
      (fun _ ↦ 0) (fun a ↦ a.2)
      (parameter_graph_atlas_zero_continuous x _ (parameter_graph_atlas_projection_continuous v)) continuous_id
  have hvertical := parameter_graph_local_joint_clm_comp s x v d n Ω hΩ
    (fun p _ ↦ ContinuousLinearMap.inr ℝ (X p) (V p))
    (fun p a ↦ a.2.comp (fderiv ℝ (R p) a.1)) hinr hQDR
  have hJ := parameter_graph_local_joint_add s (ParameterGraphHomAtlas.atlas x d)
    n Ω hΩ _ _ hinl hvertical
  have hout := parameter_graph_local_joint_clm_comp s x d y n Ω hΩ
    (fun p a ↦ fderiv ℝ (F p) (a.1,T p a.1))
    (fun p a ↦ ContinuousLinearMap.inl ℝ (X p) (V p) +
      (ContinuousLinearMap.inr ℝ (X p) (V p)).comp (a.2.comp (fderiv ℝ (R p) a.1))) hDF' hJ
  convert hout using 1
  funext p a
  apply congrArg (fun L ↦ (fderiv ℝ (F p) (a.1,T p a.1)).comp L)
  apply ContinuousLinearMap.ext
  intro u
  change (u,a.2 ((fderiv ℝ (R p) a.1) u)) =
    (u,0) + (0,a.2 ((fderiv ℝ (R p) a.1) u))
  simp


/-- The actual receiving-operator tangent action for a return over a continuous
base map has joint fibre order n. Only P of order n is used; F and R have order
n+1. The source operator bundle is literally the pullback of the original Hom
bundle, and the output is the original Hom bundle. -/
theorem parameter_graph_local_joint_tangent_action
    {A : Type*} [TopologicalSpace A] {E F : A → Type*}
    [∀p,NormedAddCommGroup (E p)] [∀p,NormedSpace ℝ (E p)]
    [∀p,NormedAddCommGroup (F p)] [∀p,NormedSpace ℝ (F p)]
    [TopologicalSpace (Sigma E)] [TopologicalSpace (Sigma F)]
    (e : FiniteRankNormedAtlas (E := E)) (f : FiniteRankNormedAtlas (E := F))
    (h:A→A) (hh:Continuous h) (n:ℕ) (U:Set (Sigma E)) (hU:IsOpen U)
    (R:∀p,E p→E (h p)) (P:∀p,E p→F p)
    (hR:JointFiberContDiffOn e e h (n+1) U R)
    (hP:JointFiberContDiffOn e f id n U P)
    (hRU:∀a∈U,(⟨h a.1,R a.1 a.2⟩:Sigma E)∈U)
    (G:∀p,E p×F (h p)→F p) (W:Set (Sigma (fun p ↦ E p×F (h p)))) :
    letI := ParameterGraphHomAtlas.topology e f
    letI := ParameterGraphPullbackAtlas.topology e h hh
    letI := ParameterGraphPullbackAtlas.topology f h hh
    let _ep := ParameterGraphPullbackAtlas.atlas e h hh
    let fp := ParameterGraphPullbackAtlas.atlas f h hh
    letI := ParameterGraphProductAtlas.topology (E := E) (F := fun p ↦ F (h p))
    IsOpen W → JointFiberContDiffOn (ParameterGraphProductAtlas.atlas e fp) f id (n+1) W G →
    (∀a∈U,(⟨a.1,(a.2,P (h a.1) (R a.1 a.2))⟩:Sigma (fun p ↦ E p×F (h p)))∈W) →
    letI := ParameterGraphPullbackAtlas.topology (ParameterGraphHomAtlas.atlas e f) h hh
    let qp := ParameterGraphPullbackAtlas.atlas (ParameterGraphHomAtlas.atlas e f) h hh
    letI := ParameterGraphProductAtlas.topology (E := E) (F := fun p ↦ E (h p)→L[ℝ] F (h p))
    JointFiberContDiffOn (ParameterGraphProductAtlas.atlas e qp)
      (ParameterGraphHomAtlas.atlas e f) id n
      {a:Sigma (fun p ↦ E p×(E (h p)→L[ℝ] F (h p))) | (⟨a.1,a.2.1⟩:Sigma E)∈U}
      (fun p a ↦ (fderiv ℝ (G p) (a.1,P (h p) (R p a.1))).comp
        ((ContinuousLinearMap.id ℝ (E p)).prod (a.2.comp (fderiv ℝ (R p) a.1)))) := by
  let := ParameterGraphHomAtlas.topology e f
  let := ParameterGraphPullbackAtlas.topology e h hh
  let := ParameterGraphPullbackAtlas.topology f h hh
  let ep := ParameterGraphPullbackAtlas.atlas e h hh
  let fp := ParameterGraphPullbackAtlas.atlas f h hh
  let := ParameterGraphProductAtlas.topology (E := E) (F := fun p ↦ F (h p))
  dsimp only
  intro hW hG hmap
  have hR' : JointFiberContDiffOn e ep id (n+1) U R :=
    (parameter_graph_local_joint_pullback_iff e e h hh (n+1) U hU R).mpr hR
  have hT : JointFiberContDiffOn e fp id n U (fun p a ↦ P (h p) (R p a)) := by
    apply (parameter_graph_local_joint_pullback_iff e f h hh n U hU _).mpr
    exact parameter_graph_local_joint_comp e e f h hh id continuous_id R P n U U hU hU
      (hR.of_le (Nat.le_succ n)) hP hRU
  have hcore := parameter_graph_local_joint_tangent_action_core e fp ep f n U hU R
    (fun p a ↦ P (h p) (R p a)) G hR' hT W hW hG hmap
  let := ParameterGraphPullbackAtlas.topology (ParameterGraphHomAtlas.atlas e f) h hh
  let qp := ParameterGraphPullbackAtlas.atlas (ParameterGraphHomAtlas.atlas e f) h hh
  let := ParameterGraphProductAtlas.topology (E := E) (F := fun p ↦ E (h p)→L[ℝ] F (h p))
  let s := ParameterGraphProductAtlas.atlas e qp
  let Ω := {a:Sigma (fun p ↦ E p×(E (h p)→L[ℝ] F (h p))) | (⟨a.1,a.2.1⟩:Sigma E)∈U}
  have hΩ : IsOpen Ω := hU.preimage ParameterGraphProductAtlas.fst_continuous
  have hfst : JointFiberContDiffOn s e id n Ω (fun _ a ↦ a.1) :=
    (jointFiberContDiffOn_univ_iff.mpr (parameter_graph_joint_native_fst e qp n)).mono (subset_univ _)
  have hsnd : JointFiberContDiffOn s qp id n Ω (fun _ a ↦ a.2) :=
    (jointFiberContDiffOn_univ_iff.mpr (parameter_graph_joint_native_snd e qp n)).mono (subset_univ _)
  let qh := ParameterGraphHomAtlas.atlas ep fp
  have hqmap := parameter_graph_joint_hom_pullback e f h hh n
  have hQ := parameter_graph_local_joint_comp s qp qh id continuous_id id continuous_id
    (fun _ a ↦ a.2) (fun _ Q ↦ Q) n Ω univ hΩ isOpen_univ hsnd
    (jointFiberContDiffOn_univ_iff.mpr hqmap) (fun _ _ ↦ mem_univ _)
  let := ParameterGraphHomAtlas.topology ep fp
  let := ParameterGraphProductAtlas.topology (E := E) (F := fun p ↦ E (h p)→L[ℝ] F (h p))
  let sh := ParameterGraphProductAtlas.atlas e qh
  have hΩ' : IsOpen Ω := hU.preimage ParameterGraphProductAtlas.fst_continuous
  have hpair := parameter_graph_local_joint_pair s e qh id continuous_id n Ω hΩ
    (fun _ a ↦ a.1) (fun _ a ↦ a.2) hfst hQ
  exact parameter_graph_local_joint_comp s sh (ParameterGraphHomAtlas.atlas e f)
    id continuous_id id continuous_id (fun _ a ↦ (a.1,a.2))
    (fun p a ↦ (fderiv ℝ (G p) (a.1,P (h p) (R p a.1))).comp
      ((ContinuousLinearMap.id ℝ (E p)).prod (a.2.comp (fderiv ℝ (R p) a.1))))
    n Ω Ω hΩ hΩ' hpair hcore (fun a ha ↦ ha)

end HolomorphicAnosov

