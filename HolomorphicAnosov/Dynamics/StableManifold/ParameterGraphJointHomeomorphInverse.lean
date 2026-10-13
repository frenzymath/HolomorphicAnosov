import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphLocalFiberRegularity
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphLocalJointJetCriterion
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphLocalJointJetNorm
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphPullbackAtlas
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphJointInverse
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphJointComposition
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphLocalJointContinuity
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphJointDerivativeCriterion
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphJointProductPullback

noncomputable section
open Set Filter _root_.Topology
open scoped ContDiff
namespace HolomorphicAnosov

/-- Local joint regularity on an original open domain depends only on the map
there. Equality on the domain gives eventual equality in each original fibre,
hence equality of every actual derivative at its points. The local original-jet
criterion transfers the known jet continuity across that equality. -/
theorem parameter_graph_local_joint_congr
    {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]
    {E : A → Type*} {F : B → Type*}
    [∀p,NormedAddCommGroup (E p)] [∀p,NormedSpace ℝ (E p)]
    [∀p,NormedAddCommGroup (F p)] [∀p,NormedSpace ℝ (F p)]
    [TopologicalSpace (Sigma E)] [TopologicalSpace (Sigma F)]
    (e : FiniteRankNormedAtlas (E := E)) (f : FiniteRankNormedAtlas (E := F))
    (b : A → B) (hb : Continuous b) (g k : ∀p,E p→F (b p))
    (r : ℕ) (U : Set (Sigma E)) (hU : IsOpen U)
    (hg : JointFiberContDiffOn e f b r U g)
    (heq : ∀z∈U,g z.1 z.2 = k z.1 z.2) :
    JointFiberContDiffOn e f b r U k := by
  have hnear (z : Sigma E) (hz : z∈U) : g z.1 =ᶠ[nhds z.2] k z.1 := by
    have hN := (hU.preimage (e.fibre_inducing z.1).continuous).mem_nhds hz
    filter_upwards [hN] with x hx
    exact heq ⟨z.1,x⟩ hx
  apply parameter_graph_local_joint_jet_criterion
  · exact fun z hz ↦ (hg.1 z hz).congr_of_eventuallyEq (hnear z hz).symm
  · intro i m hm
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
    have hj := parameter_graph_local_jet_evaluation_continuous e f b hb g
      r m hm U hU hg p hp x hx (fun z ↦ z.2) v hv
    apply hj.congr
    intro z
    change (⟨b (p z),iteratedFDeriv ℝ m (g (p z)) (x z) (v z)⟩ : Sigma F) = _
    rw [(hnear ⟨p z,x z⟩ z.2).iteratedFDeriv ℝ m |>.eq_of_nhds]
    rfl

/-- An actual fibre homeomorphism with invertible derivative has the inverse
of that derivative as the derivative of its inverse. This uses the supplied
homeomorphism's local inverse, with no regularity conclusion assumed. -/
theorem parameter_graph_homeomorph_inverse_hasFDerivAt
    {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] (H : V ≃ₜ W) (y : W)
    (hH : DifferentiableAt ℝ H (H.symm y))
    (hD : (fderiv ℝ H (H.symm y)).IsInvertible) :
    HasFDerivAt H.symm (ContinuousLinearMap.inverse (fderiv ℝ H (H.symm y))) y := by
  obtain ⟨L,hL⟩ := hD
  have hd : HasFDerivAt H (L : V →L[ℝ] W) (H.symm y) := by
    rw [hL]
    exact hH.hasFDerivAt
  have hi := H.toOpenPartialHomeomorph.hasFDerivAt_symm (mem_univ y) hd
  rw [← hL,ContinuousLinearMap.inverse_equiv]
  exact hi

/-- HPS pp.32–36,62: a family of actual fibre homeomorphisms has jointly
C^r inverses on the inverse image of an original open smooth domain, provided
its original derivatives there are invertible and its total inverse is continuous.
Induct on r. Order zero is total continuity. At a successor order, the derivative
of H has the preceding joint order; compose it with the already regular inverse,
then apply joint operator inversion. The local derivative identity and successor
criterion recover the next order, without assuming inverse higher jets. -/
theorem parameter_graph_local_joint_homeomorph_inverse
    {A : Type*} [TopologicalSpace A] {E F : A → Type*}
    [∀p,NormedAddCommGroup (E p)] [∀p,NormedSpace ℝ (E p)]
    [∀p,NormedAddCommGroup (F p)] [∀p,NormedSpace ℝ (F p)]
    [TopologicalSpace (Sigma E)] [TopologicalSpace (Sigma F)]
    (e : FiniteRankNormedAtlas (E := E)) (f : FiniteRankNormedAtlas (E := F))
    (H : ∀p,E p ≃ₜ F p)
    (hi : Continuous (fun z : Sigma F ↦ (⟨z.1,(H z.1).symm z.2⟩ : Sigma E)))
    (r : ℕ) (U : Set (Sigma E)) (hU : IsOpen U)
    (hg : JointFiberContDiffOn e f id r U (fun p ↦ H p))
    (hD : ∀z∈U,(fderiv ℝ (H z.1) z.2).IsInvertible) :
    JointFiberContDiffOn f e id r
      ((fun z : Sigma F ↦ (⟨z.1,(H z.1).symm z.2⟩ : Sigma E)) ⁻¹' U)
      (fun p ↦ (H p).symm) := by
  let W : Set (Sigma F) := (fun z : Sigma F ↦ (⟨z.1,(H z.1).symm z.2⟩ : Sigma E)) ⁻¹' U
  have hW : IsOpen W := hU.preimage hi
  induction r with
  | zero =>
      exact (parameter_graph_local_joint_zero_iff f e id continuous_id (fun p ↦ (H p).symm)
        W hW).mpr hi.continuousOn
  | succ n ih =>
      have hin := ih (hg.of_le (Nat.le_succ n))
      have hdif (z : Sigma F) (hz : z∈W) :
          HasFDerivAt (H z.1).symm
            (ContinuousLinearMap.inverse (fderiv ℝ (H z.1) ((H z.1).symm z.2))) z.2 :=
        parameter_graph_homeomorph_inverse_hasFDerivAt (H z.1) z.2
          ((hg.1 _ hz).differentiableAt (by simp))
          (hD _ hz)
      let := ParameterGraphHomAtlas.topology e f
      let := ParameterGraphHomAtlas.topology f e
      have hdg := parameter_graph_local_joint_derivative e f (fun p ↦ H p) n U hU hg
      have hcomp := parameter_graph_local_joint_comp f e (ParameterGraphHomAtlas.atlas e f)
        id continuous_id id continuous_id (fun p ↦ (H p).symm) (fun p ↦ fderiv ℝ (H p))
        n W U hW hU hin hdg (fun _ hz ↦ hz)
      have hcompinv := parameter_graph_local_joint_comp f (ParameterGraphHomAtlas.atlas e f)
        (ParameterGraphHomAtlas.atlas f e) id continuous_id id continuous_id
        (fun p y ↦ fderiv ℝ (H p) ((H p).symm y))
        (fun p ↦ ContinuousLinearMap.inverse (M := E p) (M₂ := F p)) n W
        {z : Sigma (fun p ↦ E p →L[ℝ] F p) | z.2.IsInvertible}
        hW (ParameterGraphHomAtlas.isOpen_invertible e f) hcomp
        (ParameterGraphHomAtlas.joint_inverse e f n) (fun z hz ↦ hD _ hz)
      have hdi := parameter_graph_local_joint_congr f (ParameterGraphHomAtlas.atlas f e)
        id continuous_id
        (fun p y ↦ ContinuousLinearMap.inverse (fderiv ℝ (H p) ((H p).symm y)))
        (fun p ↦ fderiv ℝ (H p).symm) n W hW hcompinv (fun z hz ↦ (hdif z hz).fderiv.symm)
      exact parameter_graph_local_joint_of_derivative f e (fun p ↦ (H p).symm) n W hW
        hi.continuousOn (fun z hz ↦ (hdif z hz).differentiableAt) hdi

/-- Transport along equality of base points preserves the original fibre norm. -/
def parameter_graph_fibre_cast
    {B : Type*} {F : B → Type*}
    [∀p,NormedAddCommGroup (F p)] [∀p,NormedSpace ℝ (F p)]
    (p q : B) (hpq : p = q) : F p ≃L[ℝ] F q := by
  subst q
  exact ContinuousLinearEquiv.refl ℝ (F p)

lemma parameter_graph_sigma_fibre_cast
    {B : Type*} {F : B → Type*}
    [∀p,NormedAddCommGroup (F p)] [∀p,NormedSpace ℝ (F p)]
    (p q : B) (hpq : p = q) (x : F p) :
    (⟨q,parameter_graph_fibre_cast p q hpq x⟩ : Sigma F) = ⟨p,x⟩ := by
  subst q
  rfl

/-- The local inverse regularity theorem over an arbitrary homeomorphism of
parameter bases. Pull the receiving bundle back along h, apply the same-base
inverse theorem, and precompose by the canonical linear reindexing over h.symm.
The latter is jointly smooth because its original total value is the identity.
The domain is precisely the inverse image of U under the actual total inverse,
equivalently the original total image of U. -/
theorem parameter_graph_local_joint_homeomorph_inverse_over
    {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]
    {E : A → Type*} {F : B → Type*}
    [∀p,NormedAddCommGroup (E p)] [∀p,NormedSpace ℝ (E p)]
    [∀p,NormedAddCommGroup (F p)] [∀p,NormedSpace ℝ (F p)]
    [TopologicalSpace (Sigma E)] [TopologicalSpace (Sigma F)]
    (e : FiniteRankNormedAtlas (E := E)) (f : FiniteRankNormedAtlas (E := F))
    (h : A ≃ₜ B) (H : ∀p,E p ≃ₜ F (h p))
    (hi : Continuous (Equiv.sigmaCongr h.toEquiv (fun p ↦ (H p).toEquiv)).symm)
    (r : ℕ) (U : Set (Sigma E)) (hU : IsOpen U)
    (hg : JointFiberContDiffOn e f h r U (fun p ↦ H p))
    (hD : ∀z∈U,(fderiv ℝ (H z.1) z.2).IsInvertible) :
    JointFiberContDiffOn f e h.symm r
      ((Equiv.sigmaCongr h.toEquiv (fun p ↦ (H p).toEquiv)).symm ⁻¹' U)
      (fun q y ↦ (H (h.symm q)).symm
        (parameter_graph_fibre_cast q (h (h.symm q)) (h.apply_symm_apply q).symm y)) := by
  let := ParameterGraphPullbackAtlas.topology f h h.continuous
  let fp := ParameterGraphPullbackAtlas.atlas f h h.continuous
  let back := (Equiv.sigmaCongr h.toEquiv (fun p ↦ (H p).toEquiv)).symm
  let W := back ⁻¹' U
  let J (q : B) : F q ≃L[ℝ] F (h (h.symm q)) :=
    parameter_graph_fibre_cast q (h (h.symm q)) (h.apply_symm_apply q).symm
  have hJorig : Continuous (fun z : Sigma F ↦ (⟨h (h.symm z.1),J z.1 z.2⟩ : Sigma F)) := by
    apply continuous_id.congr
    intro z
    exact (parameter_graph_sigma_fibre_cast z.1 (h (h.symm z.1))
      (h.apply_symm_apply z.1).symm z.2).symm
  have hJ : Continuous (fun z : Sigma F ↦
      (⟨h.symm z.1,J z.1 z.2⟩ : Sigma (fun p ↦ F (h p)))) :=
    (ParameterGraphPullbackAtlas.continuous_mk_iff f h h.continuous _ _).mpr
      ⟨h.symm.continuous.comp (parameter_graph_atlas_projection_continuous f),hJorig⟩
  have hig : Continuous (fun z : Sigma (fun p ↦ F (h p)) ↦
      (⟨z.1,(H z.1).symm z.2⟩ : Sigma E)) := by
    have ht := hi.comp (ParameterGraphPullbackAtlas.continuous_original f h h.continuous)
    apply ht.congr
    intro z
    change (Equiv.sigmaCongr h.toEquiv (fun p ↦ (H p).toEquiv)).symm
      ((Equiv.sigmaCongrLeft h.toEquiv) z) = _
    change (Equiv.sigmaCongrRight (fun p ↦ (H p).toEquiv)).symm
      ((Equiv.sigmaCongrLeft h.toEquiv).symm ((Equiv.sigmaCongrLeft h.toEquiv) z)) = _
    rw [Equiv.symm_apply_apply]
    rfl
  have hgp : JointFiberContDiffOn e fp id r U (fun p ↦ H p) :=
    (parameter_graph_local_joint_pullback_iff e f h h.continuous r U hU (fun p ↦ H p)).mpr hg
  have hin := parameter_graph_local_joint_homeomorph_inverse e fp H hig r U hU hgp hD
  let V : Set (Sigma (fun p ↦ F (h p))) :=
    (fun z : Sigma (fun p ↦ F (h p)) ↦ (⟨z.1,(H z.1).symm z.2⟩ : Sigma E)) ⁻¹' U
  have hVo : IsOpen V := hU.preimage hig
  have hWo : IsOpen W := hU.preimage hi
  have hJr := parameter_graph_joint_linear f fp h.symm h.symm.continuous
    (fun q ↦ (J q).toContinuousLinearMap) hJ r
  have hJloc : JointFiberContDiffOn f fp h.symm r W (fun q ↦ J q) :=
    (jointFiberContDiffOn_univ_iff.mpr hJr).mono (subset_univ W)
  have hmap : ∀z∈W,(⟨h.symm z.1,J z.1 z.2⟩ : Sigma (fun p ↦ F (h p)))∈V := by
    intro z hz
    have heq : back z = (⟨h.symm z.1,(H (h.symm z.1)).symm (J z.1 z.2)⟩ : Sigma E) := by
      apply (Equiv.sigmaCongr h.toEquiv (fun p ↦ (H p).toEquiv)).injective
      rw [Equiv.apply_symm_apply]
      change z = (⟨h (h.symm z.1),(H (h.symm z.1)) ((H (h.symm z.1)).symm (J z.1 z.2))⟩ : Sigma F)
      rw [(H (h.symm z.1)).apply_symm_apply (J z.1 z.2)]
      exact (parameter_graph_sigma_fibre_cast z.1 (h (h.symm z.1))
        (h.apply_symm_apply z.1).symm z.2).symm
    change back z ∈ U at hz
    change (⟨h.symm z.1,(H (h.symm z.1)).symm (J z.1 z.2)⟩ : Sigma E) ∈ U
    exact heq ▸ hz
  exact parameter_graph_local_joint_comp f fp e h.symm h.symm.continuous id continuous_id
    (fun q ↦ J q) (fun p ↦ (H p).symm) r W V hWo hVo hJloc hin hmap

/-- On whole bundles the local same-base inverse rule yields the global rule. -/
theorem parameter_graph_joint_homeomorph_inverse
    {A : Type*} [TopologicalSpace A] {E F : A → Type*}
    [∀p,NormedAddCommGroup (E p)] [∀p,NormedSpace ℝ (E p)]
    [∀p,NormedAddCommGroup (F p)] [∀p,NormedSpace ℝ (F p)]
    [TopologicalSpace (Sigma E)] [TopologicalSpace (Sigma F)]
    (e : FiniteRankNormedAtlas (E := E)) (f : FiniteRankNormedAtlas (E := F))
    (H : ∀p,E p ≃ₜ F p)
    (hi : Continuous (fun z : Sigma F ↦ (⟨z.1,(H z.1).symm z.2⟩ : Sigma E)))
    (r : ℕ) (hg : JointFiberContDiff e f id r (fun p ↦ H p))
    (hD : ∀p x,(fderiv ℝ (H p) x).IsInvertible) :
    JointFiberContDiff f e id r (fun p ↦ (H p).symm) := by
  apply jointFiberContDiffOn_univ_iff.mp
  simpa only [preimage_univ] using parameter_graph_local_joint_homeomorph_inverse e f H hi r
    univ isOpen_univ (jointFiberContDiffOn_univ_iff.mpr hg) (fun z _ ↦ hD z.1 z.2)

end HolomorphicAnosov
