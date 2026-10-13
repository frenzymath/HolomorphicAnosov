import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphJointJetCriterion
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphLocalJointJetCriterion
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphLocalJointJetNorm
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphProductAtlas
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphPullbackAtlas
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphAtlasOperations

noncomputable section
open Set _root_.Topology
open scoped ContDiff
namespace HolomorphicAnosov

/-- Pairing local joint fibre maps preserves all finite orders in the genuine
product atlas. Original iterated jets pair componentwise; their total
continuity follows from the original product topology. HPS pp.8,32–36,62. -/
theorem parameter_graph_local_joint_pair
    {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]
    {E : A → Type*} {F K : B → Type*}
    [∀p,NormedAddCommGroup (E p)] [∀p,NormedSpace ℝ (E p)]
    [∀p,NormedAddCommGroup (F p)] [∀p,NormedSpace ℝ (F p)]
    [∀p,NormedAddCommGroup (K p)] [∀p,NormedSpace ℝ (K p)]
    [TopologicalSpace (Sigma E)] [TopologicalSpace (Sigma F)] [TopologicalSpace (Sigma K)]
    (e : FiniteRankNormedAtlas (E := E)) (f : FiniteRankNormedAtlas (E := F))
    (k : FiniteRankNormedAtlas (E := K)) (b : A → B) (hb : Continuous b)
    (r : ℕ) (U : Set (Sigma E)) (hU : IsOpen U)
    (u : ∀p,E p → F (b p)) (w : ∀p,E p → K (b p))
    (hu : JointFiberContDiffOn e f b r U u) (hw : JointFiberContDiffOn e k b r U w) :
    let : TopologicalSpace (Sigma (fun p ↦ F p × K p)) := ParameterGraphProductAtlas.topology
    JointFiberContDiffOn e (ParameterGraphProductAtlas.atlas f k) b r U
      (fun p x ↦ (u p x,w p x)) := by
  let : TopologicalSpace (Sigma (fun p ↦ F p × K p)) := ParameterGraphProductAtlas.topology
  apply parameter_graph_local_joint_jet_criterion
  · intro z hz
    exact (hu.1 z hz).prodMk (hw.1 z hz)
  ·
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
    have huj := parameter_graph_local_jet_evaluation_continuous e f b hb u r m hm U hU hu
      p hp x hx (fun z ↦ z.2) v hv
    have hwj := parameter_graph_local_jet_evaluation_continuous e k b hb w r m hm U hU hw
      p hp x hx (fun z ↦ z.2) v hv
    have hc := ParameterGraphProductAtlas.continuous_mk (fun z ↦ b (p z))
      (fun z ↦ iteratedFDeriv ℝ m (u (p z)) (x z) (v z))
      (fun z ↦ iteratedFDeriv ℝ m (w (p z)) (x z) (v z)) huj hwj
    apply hc.congr
    intro z
    change (⟨b (p z),(_,_)⟩ : Sigma (fun p ↦ F p × K p)) =
      ⟨b (p z),iteratedFDeriv ℝ m (fun y ↦ (u (p z) y,w (p z) y)) (x z) (v z)⟩
    rw [iteratedFDeriv_prodMk (hu.1 _ z.2) (hw.1 _ z.2) (by exact_mod_cast hm)]
    rfl

/-- Taking the fst component of a local joint fibre map into the genuine
product atlas preserves every finite order. Apply the original continuous
projection to each jet, using the local linear postcomposition chain rule. -/
theorem parameter_graph_local_joint_fst
    {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]
    {E : A → Type*} {F K : B → Type*}
    [∀p,NormedAddCommGroup (E p)] [∀p,NormedSpace ℝ (E p)]
    [∀p,NormedAddCommGroup (F p)] [∀p,NormedSpace ℝ (F p)]
    [∀p,NormedAddCommGroup (K p)] [∀p,NormedSpace ℝ (K p)]
    [TopologicalSpace (Sigma E)] [TopologicalSpace (Sigma F)] [TopologicalSpace (Sigma K)]
    (e : FiniteRankNormedAtlas (E := E)) (f : FiniteRankNormedAtlas (E := F))
    (k : FiniteRankNormedAtlas (E := K)) (b : A → B) (hb : Continuous b)
    (r : ℕ) (U : Set (Sigma E)) (hU : IsOpen U)
    (g : ∀p,E p → F (b p) × K (b p)) :
    let : TopologicalSpace (Sigma (fun p ↦ F p × K p)) := ParameterGraphProductAtlas.topology
    JointFiberContDiffOn e (ParameterGraphProductAtlas.atlas f k) b r U g →
      JointFiberContDiffOn e f b r U (fun p x ↦ (g p x).1) := by
  let : TopologicalSpace (Sigma (fun p ↦ F p × K p)) := ParameterGraphProductAtlas.topology
  dsimp only
  intro hg
  apply parameter_graph_local_joint_jet_criterion
  · intro z hz
    exact ContDiffAt.continuousLinearMap_comp (ContinuousLinearMap.fst ℝ (F (b z.1)) (K (b z.1))) (hg.1 z hz)
  ·
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
    have hgj := parameter_graph_local_jet_evaluation_continuous e
      (ParameterGraphProductAtlas.atlas f k) b hb g r m hm U hU hg
      p hp x hx (fun z ↦ z.2) v hv
    have hc := (ParameterGraphProductAtlas.fst_continuous (E := F) (F := K)).comp hgj
    apply hc.congr
    intro z
    have he := (ContinuousLinearMap.fst ℝ (F (b (p z))) (K (b (p z)))).iteratedFDerivWithin_comp_left
      (hg.1 _ z.2).contDiffWithinAt uniqueDiffOn_univ (mem_univ (x z)) (i := m)
      (by exact_mod_cast hm)
    simp only [iteratedFDerivWithin_univ] at he
    change (⟨b (p z),(iteratedFDeriv ℝ m (g (p z)) (x z) (v z)).1⟩ : Sigma F) =
      ⟨b (p z),iteratedFDeriv ℝ m (fun y ↦ (g (p z) y).1) (x z) (v z)⟩
    exact congrArg (Sigma.mk (b (p z))) ((congrArg (fun L ↦ L (v z)) he).symm)

/-- Taking the snd component of a local joint fibre map into the genuine
product atlas preserves every finite order. Apply the original continuous
projection to each jet, using the local linear postcomposition chain rule. -/
theorem parameter_graph_local_joint_snd
    {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]
    {E : A → Type*} {F K : B → Type*}
    [∀p,NormedAddCommGroup (E p)] [∀p,NormedSpace ℝ (E p)]
    [∀p,NormedAddCommGroup (F p)] [∀p,NormedSpace ℝ (F p)]
    [∀p,NormedAddCommGroup (K p)] [∀p,NormedSpace ℝ (K p)]
    [TopologicalSpace (Sigma E)] [TopologicalSpace (Sigma F)] [TopologicalSpace (Sigma K)]
    (e : FiniteRankNormedAtlas (E := E)) (f : FiniteRankNormedAtlas (E := F))
    (k : FiniteRankNormedAtlas (E := K)) (b : A → B) (hb : Continuous b)
    (r : ℕ) (U : Set (Sigma E)) (hU : IsOpen U)
    (g : ∀p,E p → F (b p) × K (b p)) :
    let : TopologicalSpace (Sigma (fun p ↦ F p × K p)) := ParameterGraphProductAtlas.topology
    JointFiberContDiffOn e (ParameterGraphProductAtlas.atlas f k) b r U g →
      JointFiberContDiffOn e k b r U (fun p x ↦ (g p x).2) := by
  let : TopologicalSpace (Sigma (fun p ↦ F p × K p)) := ParameterGraphProductAtlas.topology
  dsimp only
  intro hg
  apply parameter_graph_local_joint_jet_criterion
  · intro z hz
    exact ContDiffAt.continuousLinearMap_comp (ContinuousLinearMap.snd ℝ (F (b z.1)) (K (b z.1))) (hg.1 z hz)
  ·
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
    have hgj := parameter_graph_local_jet_evaluation_continuous e
      (ParameterGraphProductAtlas.atlas f k) b hb g r m hm U hU hg
      p hp x hx (fun z ↦ z.2) v hv
    have hc := (ParameterGraphProductAtlas.snd_continuous (E := F) (F := K)).comp hgj
    apply hc.congr
    intro z
    have he := (ContinuousLinearMap.snd ℝ (F (b (p z))) (K (b (p z)))).iteratedFDerivWithin_comp_left
      (hg.1 _ z.2).contDiffWithinAt uniqueDiffOn_univ (mem_univ (x z)) (i := m)
      (by exact_mod_cast hm)
    simp only [iteratedFDerivWithin_univ] at he
    change (⟨b (p z),(iteratedFDeriv ℝ m (g (p z)) (x z) (v z)).2⟩ : Sigma K) =
      ⟨b (p z),iteratedFDeriv ℝ m (fun y ↦ (g (p z) y).2) (x z) (v z)⟩
    exact congrArg (Sigma.mk (b (p z))) ((congrArg (fun L ↦ L (v z)) he).symm)

/-- Pulling the receiving bundle back along its base map preserves local joint
regularity exactly. The original fibre functions and jets are unchanged, and
the pullback topology detects precisely base and original-vector continuity. -/
theorem parameter_graph_local_joint_pullback_iff
    {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]
    {E : A → Type*} {F : B → Type*}
    [∀p,NormedAddCommGroup (E p)] [∀p,NormedSpace ℝ (E p)]
    [∀p,NormedAddCommGroup (F p)] [∀p,NormedSpace ℝ (F p)]
    [TopologicalSpace (Sigma E)] [TopologicalSpace (Sigma F)]
    (e : FiniteRankNormedAtlas (E := E)) (f : FiniteRankNormedAtlas (E := F))
    (b : A → B) (hb : Continuous b) (r : ℕ) (U : Set (Sigma E)) (hU : IsOpen U)
    (g : ∀p,E p → F (b p)) :
    let : TopologicalSpace (Sigma (fun p ↦ F (b p))) := ParameterGraphPullbackAtlas.topology f b hb
    JointFiberContDiffOn e (ParameterGraphPullbackAtlas.atlas f b hb) id r U g ↔
      JointFiberContDiffOn e f b r U g := by
  let : TopologicalSpace (Sigma (fun p ↦ F (b p))) := ParameterGraphPullbackAtlas.topology f b hb
  dsimp only
  constructor
  · intro hg
    apply parameter_graph_local_joint_jet_criterion _ _ _ _ _ _ hg.1
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
    have hj := parameter_graph_local_jet_evaluation_continuous e
      (ParameterGraphPullbackAtlas.atlas f b hb) id continuous_id g r m hm U hU hg
      p hp x hx (fun z ↦ z.2) v hv
    exact (ParameterGraphPullbackAtlas.continuous_original f b hb).comp hj
  · intro hg
    apply parameter_graph_local_joint_jet_criterion (F := fun p ↦ F (b p))
      e (ParameterGraphPullbackAtlas.atlas f b hb) id g r U hg.1
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
    have hj := parameter_graph_local_jet_evaluation_continuous e f b hb g r m hm U hU hg
      p hp x hx (fun z ↦ z.2) v hv
    exact (ParameterGraphPullbackAtlas.continuous_mk_iff f b hb p
      (fun z ↦ iteratedFDeriv ℝ m (g (p z)) (x z) (v z))).mpr ⟨hp,hj⟩

/-- A continuous family of original continuous linear maps is jointly smooth
of every finite order. Its zeroth and first jets are evaluations of the same
family; every higher jet is zero. The proof works also in zero-rank fibres. -/
theorem parameter_graph_joint_linear
    {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]
    {E : A → Type*} {F : B → Type*}
    [∀p,NormedAddCommGroup (E p)] [∀p,NormedSpace ℝ (E p)]
    [∀p,NormedAddCommGroup (F p)] [∀p,NormedSpace ℝ (F p)]
    [TopologicalSpace (Sigma E)] [TopologicalSpace (Sigma F)]
    (e : FiniteRankNormedAtlas (E := E)) (f : FiniteRankNormedAtlas (E := F))
    (b : A → B) (hb : Continuous b) (L : ∀p,E p →L[ℝ] F (b p))
    (hL : Continuous (fun z : Sigma E ↦ (⟨b z.1,L z.1 z.2⟩ : Sigma F))) (r : ℕ) :
    JointFiberContDiff e f b r (fun p ↦ L p) := by
  apply parameter_graph_joint_jet_criterion _ _ _ _ _ (fun p ↦ (L p).contDiff)
  intro i m _hm
  let Z := (e.chart i).baseSet ×
    (FiniteFiberModel (e.rank i) × (Fin m → FiniteFiberModel (e.rank i)))
  have hp : Continuous (fun z : Z ↦ b z.1.val) := hb.comp (continuous_subtype_val.comp continuous_fst)
  rcases m with _ | m
  · have hx : Continuous (fun z : Z ↦
        (⟨z.1.val,(e.coordinates i z.1.val z.1.property).symm z.2.1⟩ : Sigma E)) :=
      (atlas_frame_continuous e i).comp (continuous_fst.prodMk continuous_snd.fst)
    simpa only [iteratedFDeriv_zero_apply, Function.comp_def] using hL.comp hx
  · rcases m with _ | m
    · have hv : Continuous (fun z : Z ↦
          (⟨z.1.val,(e.coordinates i z.1.val z.1.property).symm (z.2.2 0)⟩ : Sigma E)) :=
        (atlas_frame_continuous e i).comp
          (continuous_fst.prodMk ((continuous_apply 0).comp continuous_snd.snd))
      apply (hL.comp hv).congr
      intro z
      apply congrArg (Sigma.mk (b z.1.val))
      simp only [iteratedFDeriv_succ_apply_right, iteratedFDeriv_zero_apply,
        ContinuousLinearMap.fderiv]
      rfl
    · have hz := parameter_graph_atlas_zero_continuous f (fun z : Z ↦ b z.1.val) hp
      apply hz.congr
      intro z
      apply congrArg (Sigma.mk (b z.1.val))
      simp [iteratedFDeriv_succ_apply_right, ContinuousLinearMap.fderiv,
        iteratedFDeriv_succ_const]

/-- The identity original fibre map is jointly smooth to every order. -/
theorem parameter_graph_joint_id
    {A : Type*} [TopologicalSpace A] {E : A → Type*}
    [∀p,NormedAddCommGroup (E p)] [∀p,NormedSpace ℝ (E p)]
    [TopologicalSpace (Sigma E)] (e : FiniteRankNormedAtlas (E := E)) (r : ℕ) :
    JointFiberContDiff e e id r (fun _ x ↦ x) :=
  parameter_graph_joint_linear e e id continuous_id (fun p ↦ ContinuousLinearMap.id ℝ (E p))
    continuous_id r

/-- The original zero fibre map is jointly smooth to every order. -/
theorem parameter_graph_joint_zero
    {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]
    {E : A → Type*} {F : B → Type*}
    [∀p,NormedAddCommGroup (E p)] [∀p,NormedSpace ℝ (E p)]
    [∀p,NormedAddCommGroup (F p)] [∀p,NormedSpace ℝ (F p)]
    [TopologicalSpace (Sigma E)] [TopologicalSpace (Sigma F)]
    (e : FiniteRankNormedAtlas (E := E)) (f : FiniteRankNormedAtlas (E := F))
    (b : A → B) (hb : Continuous b) (r : ℕ) :
    JointFiberContDiff e f b r (fun _ _ ↦ 0) :=
  parameter_graph_joint_linear e f b hb (fun _ ↦ 0)
    (parameter_graph_atlas_zero_continuous f (fun z : Sigma E ↦ b z.1)
      (hb.comp (parameter_graph_atlas_projection_continuous e))) r

/-- Native original fst projection is jointly smooth in the product atlas. -/
theorem parameter_graph_joint_native_fst
    {A : Type*} [TopologicalSpace A] {E F : A → Type*}
    [∀p,NormedAddCommGroup (E p)] [∀p,NormedSpace ℝ (E p)]
    [∀p,NormedAddCommGroup (F p)] [∀p,NormedSpace ℝ (F p)]
    [TopologicalSpace (Sigma E)] [TopologicalSpace (Sigma F)]
    (e : FiniteRankNormedAtlas (E := E)) (f : FiniteRankNormedAtlas (E := F)) (r : ℕ) :
    let : TopologicalSpace (Sigma (fun p ↦ E p × F p)) := ParameterGraphProductAtlas.topology
    JointFiberContDiff (ParameterGraphProductAtlas.atlas e f) e id r (fun _ z ↦ z.1) := by
  let : TopologicalSpace (Sigma (fun p ↦ E p × F p)) := ParameterGraphProductAtlas.topology
  exact parameter_graph_joint_linear (ParameterGraphProductAtlas.atlas e f) e id continuous_id
    (fun p ↦ ContinuousLinearMap.fst ℝ (E p) (F p)) ParameterGraphProductAtlas.fst_continuous r

/-- Native original snd projection is jointly smooth in the product atlas. -/
theorem parameter_graph_joint_native_snd
    {A : Type*} [TopologicalSpace A] {E F : A → Type*}
    [∀p,NormedAddCommGroup (E p)] [∀p,NormedSpace ℝ (E p)]
    [∀p,NormedAddCommGroup (F p)] [∀p,NormedSpace ℝ (F p)]
    [TopologicalSpace (Sigma E)] [TopologicalSpace (Sigma F)]
    (e : FiniteRankNormedAtlas (E := E)) (f : FiniteRankNormedAtlas (E := F)) (r : ℕ) :
    let : TopologicalSpace (Sigma (fun p ↦ E p × F p)) := ParameterGraphProductAtlas.topology
    JointFiberContDiff (ParameterGraphProductAtlas.atlas e f) f id r (fun _ z ↦ z.2) := by
  let : TopologicalSpace (Sigma (fun p ↦ E p × F p)) := ParameterGraphProductAtlas.topology
  exact parameter_graph_joint_linear (ParameterGraphProductAtlas.atlas e f) f id continuous_id
    (fun p ↦ ContinuousLinearMap.snd ℝ (E p) (F p)) ParameterGraphProductAtlas.snd_continuous r

/-- Native original inl inclusion is jointly smooth in the product atlas. -/
theorem parameter_graph_joint_native_inl
    {A : Type*} [TopologicalSpace A] {E F : A → Type*}
    [∀p,NormedAddCommGroup (E p)] [∀p,NormedSpace ℝ (E p)]
    [∀p,NormedAddCommGroup (F p)] [∀p,NormedSpace ℝ (F p)]
    [TopologicalSpace (Sigma E)] [TopologicalSpace (Sigma F)]
    (e : FiniteRankNormedAtlas (E := E)) (f : FiniteRankNormedAtlas (E := F)) (r : ℕ) :
    let : TopologicalSpace (Sigma (fun p ↦ E p × F p)) := ParameterGraphProductAtlas.topology
    JointFiberContDiff e (ParameterGraphProductAtlas.atlas e f) id r
      (fun _ z ↦ (z,0)) := by
  let : TopologicalSpace (Sigma (fun p ↦ E p × F p)) := ParameterGraphProductAtlas.topology
  apply parameter_graph_joint_linear e (ParameterGraphProductAtlas.atlas e f) id continuous_id
    (fun p ↦ ContinuousLinearMap.inl ℝ (E p) (F p)) _ r
  exact ParameterGraphProductAtlas.continuous_mk (fun z : Sigma E ↦ z.1)
    (fun z ↦ z.2) (fun z ↦ 0)
    continuous_id
    (parameter_graph_atlas_zero_continuous f _ (parameter_graph_atlas_projection_continuous e))

/-- Native original inr inclusion is jointly smooth in the product atlas. -/
theorem parameter_graph_joint_native_inr
    {A : Type*} [TopologicalSpace A] {E F : A → Type*}
    [∀p,NormedAddCommGroup (E p)] [∀p,NormedSpace ℝ (E p)]
    [∀p,NormedAddCommGroup (F p)] [∀p,NormedSpace ℝ (F p)]
    [TopologicalSpace (Sigma E)] [TopologicalSpace (Sigma F)]
    (e : FiniteRankNormedAtlas (E := E)) (f : FiniteRankNormedAtlas (E := F)) (r : ℕ) :
    let : TopologicalSpace (Sigma (fun p ↦ E p × F p)) := ParameterGraphProductAtlas.topology
    JointFiberContDiff f (ParameterGraphProductAtlas.atlas e f) id r
      (fun _ z ↦ (0,z)) := by
  let : TopologicalSpace (Sigma (fun p ↦ E p × F p)) := ParameterGraphProductAtlas.topology
  apply parameter_graph_joint_linear f (ParameterGraphProductAtlas.atlas e f) id continuous_id
    (fun p ↦ ContinuousLinearMap.inr ℝ (E p) (F p)) _ r
  exact ParameterGraphProductAtlas.continuous_mk (fun z : Sigma F ↦ z.1)
    (fun z ↦ 0) (fun z ↦ z.2)
    (parameter_graph_atlas_zero_continuous e _ (parameter_graph_atlas_projection_continuous f))
    continuous_id


section OriginalSplit
variable {A : Type*} [TopologicalSpace A] {E F : A → Type*}
  [∀p,NormedAddCommGroup (E p)] [∀p,NormedSpace ℝ (E p)]
  [∀p,NormedAddCommGroup (F p)] [∀p,NormedSpace ℝ (F p)]
  [TopologicalSpace (Sigma E)] [TopologicalSpace (Sigma F)]
  [t : TopologicalSpace (Sigma (fun p ↦ E p×F p))]
  (e : SplitFiniteRankNormedAtlas (E₁ := E) (E₂ := F))

/-- The identity from the genuine product atlas to the original split atlas
is jointly smooth. Both total topologies detect the original component maps. -/
theorem parameter_graph_joint_product_to_split (r : ℕ) :
    @JointFiberContDiff A _ (fun p ↦ E p×F p) _ _
      (ParameterGraphProductAtlas.topology (E := E) (F := F))
      A _ (fun p ↦ E p×F p) _ _ t
      (ParameterGraphProductAtlas.atlas e.first e.second) e.total id r (fun _ z ↦ z) := by
  have ht : t = ParameterGraphProductAtlas.topology (E := E) (F := F) :=
    e.split_inducing.eq_induced
  cases ht
  let := ParameterGraphProductAtlas.topology (E := E) (F := F)
  exact parameter_graph_joint_linear (ParameterGraphProductAtlas.atlas e.first e.second)
    e.total id continuous_id (fun p ↦ ContinuousLinearMap.id ℝ (E p×F p)) continuous_id r

/-- The identity from the original split atlas to the genuine product atlas
is jointly smooth, by continuity of both original split projections. -/
theorem parameter_graph_joint_split_to_product (r : ℕ) :
    @JointFiberContDiff A _ (fun p ↦ E p×F p) _ _ t
      A _ (fun p ↦ E p×F p) _ _ (ParameterGraphProductAtlas.topology (E := E) (F := F))
      e.total (ParameterGraphProductAtlas.atlas e.first e.second) id r (fun _ z ↦ z) := by
  have ht : t = ParameterGraphProductAtlas.topology (E := E) (F := F) :=
    e.split_inducing.eq_induced
  cases ht
  let := ParameterGraphProductAtlas.topology (E := E) (F := F)
  exact parameter_graph_joint_linear e.total (ParameterGraphProductAtlas.atlas e.first e.second)
    id continuous_id (fun p ↦ ContinuousLinearMap.id ℝ (E p×F p)) continuous_id r

/-- Native first projection from the original split atlas is jointly smooth. -/
theorem parameter_graph_joint_split_fst (r : ℕ) :
    JointFiberContDiff e.total e.first id r (fun _ z ↦ z.1) :=
  parameter_graph_joint_linear e.total e.first id continuous_id
    (fun p ↦ ContinuousLinearMap.fst ℝ (E p) (F p))
    (parameter_graph_atlas_split_projections_continuous e).1 r

/-- Native second projection from the original split atlas is jointly smooth. -/
theorem parameter_graph_joint_split_snd (r : ℕ) :
    JointFiberContDiff e.total e.second id r (fun _ z ↦ z.2) :=
  parameter_graph_joint_linear e.total e.second id continuous_id
    (fun p ↦ ContinuousLinearMap.snd ℝ (E p) (F p))
    (parameter_graph_atlas_split_projections_continuous e).2 r

end OriginalSplit

end HolomorphicAnosov
