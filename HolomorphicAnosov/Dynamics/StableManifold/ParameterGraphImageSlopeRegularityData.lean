import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphHorizontalInverse
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphJointComposition
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphJointDerivativeCriterion
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphJointInverse
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphJointJetNorm
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphJointTangentAction
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphGlobalSectionRegularity
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphJointHomeomorphInverse
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphJointDerivativeBlocks
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphJointSlopeAction
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphSlopeSmoothness
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphSlopeTransform
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphDerivativeBlocks
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphImageStep
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphFixedGraphContinuity

noncomputable section
open Set Filter _root_.Topology
open scoped ContDiff
namespace HolomorphicAnosov

/-- The actual rational image action has the uniform closed-unit-ball bounds
of the abstract unit-slope transform. Horizontal invertibility identifies the
abstract transform uniquely with the totalized inverse formula. Thus its norm
and Lipschitz bounds apply to that actual formula, not merely a chosen carrier. -/
theorem parameter_graph_actual_image_slope_bounds
    {X Y U V : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup U] [NormedSpace ℝ U]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (T : X ≃L[ℝ] U)
    (A : X →L[ℝ] U) (B : Y →L[ℝ] U) (C : X →L[ℝ] V) (D : Y →L[ℝ] V)
    (a k ε : NNReal)
    (ha : ‖T.symm.toContinuousLinearMap‖ ≤ a)
    (hA : ‖A-T.toContinuousLinearMap‖ ≤ ε) (hB : ‖B‖ ≤ ε)
    (hC : ‖C‖ ≤ ε) (hD : ‖D‖ ≤ (k:ℝ)+ε)
    (hsmall : 2*(a:ℝ)*ε<1)
    (hjet : (a:ℝ)*(k+2*ε)/(1-2*(a:ℝ)*ε)<1) :
    ∃ q : NNReal, (q:ℝ)=(a:ℝ)*(k+2*ε)/(1-2*(a:ℝ)*ε) ∧ q<1 ∧
      (∀P : X→L[ℝ]Y, ‖P‖≤1 → (A+B.comp P).IsInvertible ∧
        ‖(C+D.comp P).comp (A+B.comp P).inverse‖≤q) ∧
      (∀P Q : X→L[ℝ]Y, ‖P‖≤1 → ‖Q‖≤1 →
        ‖(C+D.comp P).comp (A+B.comp P).inverse-
          (C+D.comp Q).comp (A+B.comp Q).inverse‖≤(q:ℝ)*‖P-Q‖) := by
  obtain ⟨q,hqeq,hq,Φ,_,hΦ,_,hΦeq,_⟩ :=
    parameter_graph_slope_transform T A B C D a k ε ha hA hB hC hD hsmall hjet
  have hInv (P : X→L[ℝ]Y) (hP : ‖P‖≤1) : (A+B.comp P).IsInvertible := by
    obtain ⟨J,hJ,_⟩ := (parameter_graph_horizontal_inverse T A B C a ε ha hsmall hA hB hC).1 P hP
    exact ⟨J,hJ⟩
  have heq (P : ParameterGraphUnitHom X Y) :
      (Φ P).1 = (C+D.comp P.1).comp (A+B.comp P.1).inverse := by
    obtain ⟨J,hJ⟩ := hInv P.1 P.2
    have hh := (hΦeq P).1
    rw [← hJ] at hh ⊢
    rw [ContinuousLinearMap.inverse_equiv]
    ext v
    have hv := DFunLike.congr_fun hh (J.symm v)
    simpa using hv
  refine ⟨q,hqeq,hq,?_,?_⟩
  · intro P hP
    exact ⟨hInv P hP,heq ⟨P,hP⟩ ▸ (hΦeq ⟨P,hP⟩).2⟩
  · intro P Q hP hQ
    have hh := hΦ.dist_le_mul (⟨P,hP⟩ : ParameterGraphUnitHom X Y) ⟨Q,hQ⟩
    change dist (Φ ⟨P,hP⟩).1 (Φ ⟨Q,hQ⟩).1 ≤ (q:ℝ)*dist P Q at hh
    simpa only [heq,dist_eq_norm] using hh

/-- Inside the unit slope ball, the actual slope derivative has the same
strict contraction bound. Smooth inversion gives differentiability, and the
closed-ball Lipschitz estimate bounds its derivative on the interior. -/
theorem parameter_graph_actual_image_slope_derivative_bound
    {X Y U V : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup U] [NormedSpace ℝ U]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (T : X ≃L[ℝ] U)
    (A : X →L[ℝ] U) (B : Y →L[ℝ] U) (C : X →L[ℝ] V) (D : Y →L[ℝ] V)
    (a k ε : NNReal)
    (ha : ‖T.symm.toContinuousLinearMap‖ ≤ a)
    (hA : ‖A-T.toContinuousLinearMap‖ ≤ ε) (hB : ‖B‖ ≤ ε)
    (hC : ‖C‖ ≤ ε) (hD : ‖D‖ ≤ (k:ℝ)+ε)
    (hsmall : 2*(a:ℝ)*ε<1)
    (hjet : (a:ℝ)*(k+2*ε)/(1-2*(a:ℝ)*ε)<1)
    (P : X→L[ℝ]Y) (hP : ‖P‖<1) :
    ‖fderiv ℝ (fun Q : X→L[ℝ]Y ↦ (C+D.comp Q).comp (A+B.comp Q).inverse) P‖≤
      (a:ℝ)*(k+2*ε)/(1-2*(a:ℝ)*ε) := by
  obtain ⟨q,hqeq,_,hb,hl⟩ := parameter_graph_actual_image_slope_bounds
    T A B C D a k ε ha hA hB hC hD hsmall hjet
  have hsmooth := (parameter_graph_slope_contDiffAt 1 P
    (fun _ : X→L[ℝ]Y ↦ A) (fun _ ↦ B) (fun _ ↦ C) (fun _ ↦ D)
    contDiffAt_const contDiffAt_const contDiffAt_const contDiffAt_const).1
    id contDiffAt_id (hb P hP.le).1
  have hd := (hsmooth.differentiableAt (by simp)).hasFDerivAt
  have hL : LipschitzOnWith q
      (fun Q : X→L[ℝ]Y ↦ (C+D.comp Q).comp (A+B.comp Q).inverse)
      (Metric.closedBall 0 1) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro Q hQ R hR
    simpa only [dist_eq_norm] using hl Q R
      (by simpa only [Metric.mem_closedBall,dist_zero_right] using hQ)
      (by simpa only [Metric.mem_closedBall,dist_zero_right] using hR)
  have hball : Metric.closedBall (0 : X →L[ℝ] Y) 1 ∈ 𝓝 P :=
    Metric.closedBall_mem_nhds_of_mem (by simpa only [Metric.mem_ball,dist_zero_right] using hP)
  have hnorm := hd.le_of_lipschitzOn hball hL
  simpa only [id_eq,hqeq] using hnorm

namespace ParameterGraphImageSlopeData
variable {I : Type*} {X Y : I → Type*}
  [∀p,NormedAddCommGroup (X p)] [∀p,NormedSpace ℝ (X p)]
  [∀p,NormedAddCommGroup (Y p)] [∀p,NormedSpace ℝ (Y p)]
  (h : I → I) (G : ∀p,X p×Y p→X (h p)×Y (h p)) (s : ∀p,X p→Y p)

def derivative (p : I) (x : X p) := fderiv ℝ (G p) (x,s p x)
def blockA (p : I) (x : X p) :=
  ((ContinuousLinearMap.fst ℝ (X (h p)) (Y (h p))).comp (derivative h G s p x)).comp
    (ContinuousLinearMap.inl ℝ (X p) (Y p))
def blockB (p : I) (x : X p) :=
  ((ContinuousLinearMap.fst ℝ (X (h p)) (Y (h p))).comp (derivative h G s p x)).comp
    (ContinuousLinearMap.inr ℝ (X p) (Y p))
def blockC (p : I) (x : X p) :=
  ((ContinuousLinearMap.snd ℝ (X (h p)) (Y (h p))).comp (derivative h G s p x)).comp
    (ContinuousLinearMap.inl ℝ (X p) (Y p))
def blockD (p : I) (x : X p) :=
  ((ContinuousLinearMap.snd ℝ (X (h p)) (Y (h p))).comp (derivative h G s p x)).comp
    (ContinuousLinearMap.inr ℝ (X p) (Y p))
def action (p : I) (z : X p × (X p→L[ℝ]Y p)) :=
  (blockC h G s p z.1+(blockD h G s p z.1).comp z.2).comp
    (blockA h G s p z.1+(blockB h G s p z.1).comp z.2).inverse

/-- Actual block bounds along the graph follow directly from the original
Lipschitz nonlinear remainder; the lower block is never inverted. -/
theorem block_bounds (T : ∀p,X p≃L[ℝ]X (h p)) (S : ∀p,Y p→L[ℝ]Y (h p))
    (k ε : NNReal) (hk : ∀p,‖S p‖≤k)
    (hR : ∀p,LipschitzWith ε (fun z ↦ G p z-(T p z.1,S p z.2)))
    (hG : ∀p,Differentiable ℝ (G p)) (p : I) (x : X p) :
    ‖blockA h G s p x-(T p).toContinuousLinearMap‖≤ε ∧
      ‖blockB h G s p x‖≤ε ∧ ‖blockC h G s p x‖≤ε ∧
      ‖blockD h G s p x‖≤(k:ℝ)+ε := by
  obtain ⟨hA,hB,hC,hD⟩ := parameter_graph_derivative_blocks
    (T p).toContinuousLinearMap (S p) (G p) ε (hR p) (x,s p x)
    (derivative h G s p x) (hG p (x,s p x)).hasFDerivAt
  refine ⟨hA,hB,hC,?_⟩
  exact (norm_le_norm_sub_add (blockD h G s p x) (S p)).trans
    ((add_le_add hD (hk p)).trans_eq (add_comm _ _))

/-- Differentiate the first component of the original image graph equation. -/
theorem horizontal_hasFDerivAt (H : ∀p,X p≃ₜX (h p))
    (hfirst : ∀p x,(G p (x,s p x)).1=H p x)
    (hG : ∀p,Differentiable ℝ (G p)) (hs : ∀p,Differentiable ℝ (s p))
    (p : I) (x : X p) : HasFDerivAt (H p)
      (blockA h G s p x+(blockB h G s p x).comp (fderiv ℝ (s p) x)) x := by
  have hh := ((hG p (x,s p x)).hasFDerivAt.comp x
    ((hasFDerivAt_id x).prodMk (hs p x).hasFDerivAt)).fst
  have heq : (fun y ↦ (G p (y,s p y)).1)=(H p) := funext (hfirst p)
  dsimp only [Function.comp_def,id_eq] at hh
  rw [heq] at hh
  convert hh using 1
  ext v
  change (derivative h G s p x (v,0)).1+
    (derivative h G s p x (0,fderiv ℝ (s p) x v)).1 =
    (derivative h G s p x (v,fderiv ℝ (s p) x v)).1
  rw [← Prod.fst_add,← map_add]
  simp

/-- Differentiating exact image invariance gives the actual slope equation. -/
theorem derivative_invariant (H : ∀p,X p≃ₜX (h p))
    (hfirst : ∀p x,(G p (x,s p x)).1=H p x)
    (hsecond : ∀p x,(G p (x,s p x)).2=s (h p) (H p x))
    (hG : ∀p,Differentiable ℝ (G p)) (hs : ∀p,Differentiable ℝ (s p))
    (p : I) (x : X p) :
    (fderiv ℝ (s (h p)) (H p x)).comp
      (blockA h G s p x+(blockB h G s p x).comp (fderiv ℝ (s p) x)) =
      blockC h G s p x+(blockD h G s p x).comp (fderiv ℝ (s p) x) := by
  have hh := ((hG p (x,s p x)).hasFDerivAt.comp x
    ((hasFDerivAt_id x).prodMk (hs p x).hasFDerivAt)).snd
  have hv := (hs (h p) (H p x)).hasFDerivAt.comp x
    (horizontal_hasFDerivAt h G s H hfirst hG hs p x)
  have heq : (fun y ↦ (G p (y,s p y)).2)=(fun y ↦ s (h p) (H p y)) := funext (hsecond p)
  dsimp only [Function.comp_def,id_eq] at hh hv
  rw [heq] at hh
  have hd := hv.unique hh
  rw [hd]
  ext v
  change (derivative h G s p x (v,fderiv ℝ (s p) x v)).2 =
    (derivative h G s p x (v,0)).2+(derivative h G s p x (0,fderiv ℝ (s p) x v)).2
  rw [← Prod.snd_add,← map_add]
  simp

/-- The actual horizontal derivative is invertible and the actual invariant
graph derivative satisfies the rational image action, with strict slope bound.
Use the unit-Lipschitz graph to bound Ds, then invert only A+B Ds. -/
theorem slope_equation_and_bound [∀p,CompleteSpace (X p)]
    (H : ∀p,X p≃ₜX (h p))
    (hfirst : ∀p x,(G p (x,s p x)).1=H p x)
    (hsecond : ∀p x,(G p (x,s p x)).2=s (h p) (H p x))
    (hG : ∀p,Differentiable ℝ (G p)) (hs : ∀p,Differentiable ℝ (s p))
    (hsL : ∀p,LipschitzWith 1 (s p))
    (T : ∀p,X p≃L[ℝ]X (h p)) (S : ∀p,Y p→L[ℝ]Y (h p))
    (a k ε : NNReal) (ha : ∀p,‖(T p).symm.toContinuousLinearMap‖≤a)
    (hk : ∀p,‖S p‖≤k) (hsmall : 2*(a:ℝ)*ε<1)
    (hjet : (a:ℝ)*(k+2*ε)/(1-2*(a:ℝ)*ε)<1)
    (hR : ∀p,LipschitzWith ε (fun z ↦ G p z-(T p z.1,S p z.2)))
    (p : I) (x : X p) :
    (fderiv ℝ (H p) x).IsInvertible ∧
      fderiv ℝ (s (h p)) (H p x)=action h G s p (x,fderiv ℝ (s p) x) ∧
      ‖fderiv ℝ (s (h p)) (H p x)‖≤(a:ℝ)*(k+2*ε)/(1-2*(a:ℝ)*ε) := by
  have hb := block_bounds h G s T S k ε hk hR hG p x
  have hP : ‖fderiv ℝ (s p) x‖≤1 := norm_fderiv_le_of_lipschitz ℝ (hsL p)
  obtain ⟨q,hqeq,_,hq,_⟩ := parameter_graph_actual_image_slope_bounds (T p)
    (blockA h G s p x) (blockB h G s p x) (blockC h G s p x) (blockD h G s p x)
    a k ε (ha p) hb.1 hb.2.1 hb.2.2.1 hb.2.2.2 hsmall hjet
  obtain ⟨J,hJ⟩ := (hq (fderiv ℝ (s p) x) hP).1
  have hder := horizontal_hasFDerivAt h G s H hfirst hG hs p x
  have hinv : (fderiv ℝ (H p) x).IsInvertible := by
    rw [hder.fderiv]
    exact ⟨J,hJ⟩
  have heq : fderiv ℝ (s (h p)) (H p x)=action h G s p (x,fderiv ℝ (s p) x) := by
    have he := derivative_invariant h G s H hfirst hsecond hG hs p x
    rw [← hJ] at he
    dsimp [action]
    rw [← hJ,ContinuousLinearMap.inverse_equiv]
    ext v
    have hv := DFunLike.congr_fun he (J.symm v)
    simpa using hv
  refine ⟨hinv,heq,?_⟩
  rw [heq,← hqeq]
  exact (hq (fderiv ℝ (s p) x) hP).2

/-- Construct the actual horizontal homeomorphism and its jointly regular
inverse from the original image graph, with the exact inverse-return constant.
Joint smoothness of the horizontal map comes from the actual graph embedding
and first projection. Invertibility of its actual derivative follows from the
original derivative blocks and the unit bound for Ds. -/
theorem horizontal_return_data
    [TopologicalSpace I] [TopologicalSpace (Sigma X)] [TopologicalSpace (Sigma Y)]
    [TopologicalSpace (Sigma (fun p ↦ X p×Y p))]
    (e : SplitFiniteRankNormedAtlas (E₁ := X) (E₂ := Y))
    (h : I≃ₜI) (G : ∀p,X p×Y p→X (h p)×Y (h p)) (s : ∀p,X p→Y p)
    (n : ℕ) (hn : 1≤n) (hGj : JointFiberContDiff e.total e.total h (n+1) G)
    (hsj : JointFiberContDiff e.first e.second id n s)
    (hzero : ∀p,G p 0=0) (hs : ∀p,s p 0=0 ∧ LipschitzWith 1 (s p))
    (hgraph : ∀p,G p '' range (fun x ↦ (x,s p x))=range (fun y ↦ (y,s (h p) y)))
    (T : ∀p,X p≃L[ℝ]X (h p)) (S : ∀p,Y p→L[ℝ]Y (h p))
    (a k ε : NNReal) (ha : ∀p,‖(T p).symm.toContinuousLinearMap‖≤a)
    (hk : ∀p,‖S p‖≤k) (hsmall : 2*(a:ℝ)*ε<1)
    (hslope : (a:ℝ)*(k+2*ε)≤1)
    (hR : ∀p,LipschitzWith ε (fun z ↦ G p z-(T p z.1,S p z.2))) :
    ∃ H : ∀p,X p≃ₜX (h p),
      (∀p x,(G p (x,s p x)).1=H p x) ∧
      (∀p x,(G p (x,s p x)).2=s (h p) (H p x)) ∧
      (∀p,H p 0=0 ∧ (H p).symm 0=0) ∧
      (∀p u v,‖(H p).symm u-(H p).symm v‖≤
        ((a:ℝ)/(1-(a:ℝ)*ε))*‖u-v‖) ∧
      JointFiberContDiff e.first e.first h n (fun p ↦ H p) ∧
      Continuous (Equiv.sigmaCongr h.toEquiv (fun p ↦ (H p).toEquiv)).symm ∧
      JointFiberContDiff e.first e.first h.symm n
        (fun q y ↦ (H (h.symm q)).symm
          (parameter_graph_fibre_cast q (h (h.symm q)) (h.apply_symm_apply q).symm y)) := by
  classical
  let : ∀p,FiniteDimensional ℝ (X p) := fun p ↦
    (e.first.coordinates p p (e.first.mem_baseSet p)).symm.toLinearEquiv.finiteDimensional
  let : ∀p,CompleteSpace (X p) := fun p ↦ inferInstance
  have hsmall' : (a:ℝ)*ε<1 := by nlinarith [a.2,ε.2]
  have hHex (p : I) := parameter_graph_image_step (T p) (S p) (G p) (hzero p)
    a k ε (ha p) (hk p) hsmall' hslope (hR p) (s p) (hs p).1 (hs p).2
  choose H s' hHfirst hH0 hHi hs'0 hs'L hHgraph using hHex
  have hfirst : ∀p x,(G p (x,s p x)).1=H p x := fun p x ↦ (hHfirst p x).symm
  have hsecond : ∀p x,(G p (x,s p x)).2=s (h p) (H p x) := by
    intro p x
    have hm : G p (x,s p x)∈range (fun y ↦ (y,s (h p) y)) := by
      rw [← hgraph p]
      exact ⟨(x,s p x),⟨x,rfl⟩,rfl⟩
    obtain ⟨y,hy⟩ := hm
    have hx := congrArg Prod.fst hy
    have hz := congrArg Prod.snd hy
    simpa only [Prod.fst,Prod.snd,hfirst] using hz.symm.trans (congrArg (s (h p)) hx)
  have hpair : JointFiberContDiff e.first e.total id n (fun p x ↦ (x,s p x)) := by
    apply jointFiberContDiffOn_univ_iff.mp
    exact parameter_graph_local_joint_split_pair e.first e n univ isOpen_univ
      (fun _ x ↦ x) s
      (jointFiberContDiffOn_univ_iff.mpr (parameter_graph_joint_id e.first n))
      (jointFiberContDiffOn_univ_iff.mpr hsj)
  have hGn : JointFiberContDiff e.total e.total h n G :=
    jointFiberContDiffOn_univ_iff.mp
      ((jointFiberContDiffOn_univ_iff.mpr hGj).of_le (Nat.le_succ n))
  have hcom := parameter_graph_joint_comp e.first e.total e.total id continuous_id h h.continuous
    (fun p x ↦ (x,s p x)) G n hpair hGn
  have hproj : JointFiberContDiff e.total e.first id n (fun _ z ↦ z.1) :=
    parameter_graph_joint_linear e.total e.first id continuous_id
      (fun p ↦ ContinuousLinearMap.fst ℝ (X p) (Y p))
      (parameter_graph_atlas_split_projections_continuous e).1 n
  have hHj : JointFiberContDiff e.first e.first h n (fun p ↦ H p) := by
    have ht := parameter_graph_joint_comp e.first e.total e.first h h.continuous id continuous_id
      (fun p x ↦ G p (x,s p x)) (fun _ z ↦ z.1) n hcom hproj
    simpa only [Function.comp_def,id_eq,hfirst] using ht
  have hHc : Continuous (fun z : Sigma X ↦ (⟨h z.1,H z.1 z.2⟩ : Sigma X)) :=
    continuousOn_univ.mp (parameter_graph_local_joint_value_continuous e.first e.first h h.continuous
      (fun p ↦ H p) n univ isOpen_univ (jointFiberContDiffOn_univ_iff.mpr hHj))
  have hic := parameter_graph_fibre_homeomorph_inverse_continuous e.first e.first h H
    hHc ((a:ℝ)/(1-(a:ℝ)*ε)) hHi
  have hGd : ∀p,Differentiable ℝ (G p) := fun p ↦ (hGj.1 p).differentiable (by simp)
  have hsd : ∀p,Differentiable ℝ (s p) := fun p ↦ (hsj.1 p).differentiable (by exact_mod_cast (show n≠0 by omega))
  have hHd : ∀p x,(fderiv ℝ (H p) x).IsInvertible := by
    intro p x
    have hb := block_bounds h G s T S k ε hk hR hGd p x
    obtain ⟨J,hJ,_⟩ := (parameter_graph_horizontal_inverse (T p)
      (blockA h G s p x) (blockB h G s p x) (blockC h G s p x)
      a ε (ha p) hsmall hb.1 hb.2.1 hb.2.2.1).1 (fderiv ℝ (s p) x)
      (norm_fderiv_le_of_lipschitz ℝ (hs p).2)
    rw [(horizontal_hasFDerivAt h G s H hfirst hGd hsd p x).fderiv]
    exact ⟨J,hJ⟩
  have hir := parameter_graph_local_joint_homeomorph_inverse_over e.first e.first h H hic n
    univ isOpen_univ (jointFiberContDiffOn_univ_iff.mpr hHj) (fun z _ ↦ hHd z.1 z.2)
  refine ⟨H,hfirst,hsecond,?_,hHi,hHj,hic,?_⟩
  · intro p
    refine ⟨hH0 p,?_⟩
    rw [← hH0 p,(H p).symm_apply_apply]
  · apply jointFiberContDiffOn_univ_iff.mp
    simpa only [preimage_univ] using hir

/-- The actual source-index image action is jointly regular on its open
horizontal-invertibility locus, in the original Hom norms. -/
theorem source_action_joint
    [TopologicalSpace I] [TopologicalSpace (Sigma X)] [TopologicalSpace (Sigma Y)]
    [TopologicalSpace (Sigma (fun p ↦ X p×Y p))]
    (e : SplitFiniteRankNormedAtlas (E₁ := X) (E₂ := Y))
    (h : I≃ₜI) (G : ∀p,X p×Y p→X (h p)×Y (h p)) (s : ∀p,X p→Y p)
    (n : ℕ) (hGj : JointFiberContDiff e.total e.total h (n+1) G)
    (hsj : JointFiberContDiff e.first e.second id n s) :
    letI := ParameterGraphPullbackAtlas.topology e.first h h.continuous
    letI := ParameterGraphPullbackAtlas.topology e.second h h.continuous
    let ex := ParameterGraphPullbackAtlas.atlas e.first h h.continuous
    let ey := ParameterGraphPullbackAtlas.atlas e.second h h.continuous
    letI := ParameterGraphHomAtlas.topology e.first e.second
    letI := ParameterGraphHomAtlas.topology ex ey
    letI := ParameterGraphProductAtlas.topology (E:=X) (F:=fun p ↦ X p→L[ℝ]Y p)
    let Ω := {w : Sigma (fun p ↦ X p×(X p→L[ℝ]Y p)) |
      (blockA h G s w.1 w.2.1+(blockB h G s w.1 w.2.1).comp w.2.2).IsInvertible}
    IsOpen Ω ∧ JointFiberContDiffOn
      (ParameterGraphProductAtlas.atlas e.first (ParameterGraphHomAtlas.atlas e.first e.second))
      (ParameterGraphHomAtlas.atlas ex ey) id n Ω (action h G s) := by
  let := ParameterGraphPullbackAtlas.topology e.first h h.continuous
  let := ParameterGraphPullbackAtlas.topology e.second h h.continuous
  let ex := ParameterGraphPullbackAtlas.atlas e.first h h.continuous
  let ey := ParameterGraphPullbackAtlas.atlas e.second h h.continuous
  have hpair := parameter_graph_local_joint_split_pair e.first e n univ isOpen_univ
    (fun _ x ↦ x) s
    (jointFiberContDiffOn_univ_iff.mpr (parameter_graph_joint_id e.first n))
    (jointFiberContDiffOn_univ_iff.mpr hsj)
  have hb := parameter_graph_local_joint_derivative_blocks e.first e e h h.continuous n
    univ isOpen_univ univ isOpen_univ G (fun p x ↦ (x,s p x))
    (jointFiberContDiffOn_univ_iff.mpr hGj) hpair (fun _ _ ↦ mem_univ _)
  let := ParameterGraphHomAtlas.topology e.first e.second
  let := ParameterGraphHomAtlas.topology ex ey
  let := ParameterGraphProductAtlas.topology (E:=X) (F:=fun p ↦ X p→L[ℝ]Y p)
  convert parameter_graph_joint_image_slope_action e.first e.first e.second ex ey n univ isOpen_univ
      (blockA h G s) (blockB h G s) (blockC h G s) (blockD h G s)
      hb.1 hb.2.1 hb.2.2.1 hb.2.2.2 using 1; simp only [mem_univ,true_and]; rfl

/-- Regard the image action as taking values in the original receiving Hom
bundle, rather than the Hom of two pulled bundles. -/
theorem source_action_joint_over
    [TopologicalSpace I] [TopologicalSpace (Sigma X)] [TopologicalSpace (Sigma Y)]
    [TopologicalSpace (Sigma (fun p ↦ X p×Y p))]
    (e : SplitFiniteRankNormedAtlas (E₁ := X) (E₂ := Y))
    (h : I≃ₜI) (G : ∀p,X p×Y p→X (h p)×Y (h p)) (s : ∀p,X p→Y p)
    (n : ℕ) (hGj : JointFiberContDiff e.total e.total h (n+1) G)
    (hsj : JointFiberContDiff e.first e.second id n s) :
    letI := ParameterGraphHomAtlas.topology e.first e.second
    letI := ParameterGraphProductAtlas.topology (E:=X) (F:=fun p ↦ X p→L[ℝ]Y p)
    let Ω := {w : Sigma (fun p ↦ X p×(X p→L[ℝ]Y p)) |
      (blockA h G s w.1 w.2.1+(blockB h G s w.1 w.2.1).comp w.2.2).IsInvertible}
    IsOpen Ω ∧ JointFiberContDiffOn
      (ParameterGraphProductAtlas.atlas e.first (ParameterGraphHomAtlas.atlas e.first e.second))
      (ParameterGraphHomAtlas.atlas e.first e.second) h n Ω (action h G s) := by
  let := ParameterGraphHomAtlas.topology e.first e.second
  let := ParameterGraphProductAtlas.topology (E:=X) (F:=fun p ↦ X p→L[ℝ]Y p)
  let := ParameterGraphPullbackAtlas.topology e.first h h.continuous
  let := ParameterGraphPullbackAtlas.topology e.second h h.continuous
  let ex := ParameterGraphPullbackAtlas.atlas e.first h h.continuous
  let ey := ParameterGraphPullbackAtlas.atlas e.second h h.continuous
  let := ParameterGraphHomAtlas.topology ex ey
  let f := ParameterGraphHomAtlas.atlas e.first e.second
  let := ParameterGraphPullbackAtlas.topology f h h.continuous
  let ep := ParameterGraphProductAtlas.atlas e.first f
  obtain ⟨ho,hj⟩ := source_action_joint e h G s n hGj hsj
  refine ⟨ho,?_⟩
  apply (parameter_graph_local_joint_pullback_iff ep f h h.continuous n _ ho _).mp
  exact parameter_graph_local_joint_comp ep (ParameterGraphHomAtlas.atlas ex ey)
    (ParameterGraphPullbackAtlas.atlas f h h.continuous) id continuous_id id continuous_id
    (action h G s) (fun _ L ↦ L) n _ univ ho isOpen_univ hj
    (jointFiberContDiffOn_univ_iff.mpr
      (parameter_graph_joint_hom_pullback_symm e.first e.second h h.continuous n))
    (fun _ _ ↦ mem_univ _)

/-- Equality transport of a base map preserves local joint regularity. -/
theorem joint_cast_base
    {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]
    {E : A→Type*} {F : B→Type*}
    [∀p,NormedAddCommGroup (E p)] [∀p,NormedSpace ℝ (E p)]
    [∀p,NormedAddCommGroup (F p)] [∀p,NormedSpace ℝ (F p)]
    [TopologicalSpace (Sigma E)] [TopologicalSpace (Sigma F)]
    (e : FiniteRankNormedAtlas (E:=E)) (f : FiniteRankNormedAtlas (E:=F))
    (b c : A→B) (hbc : b=c) (g : ∀p,E p→F (b p)) (r : ℕ) (U : Set (Sigma E))
    (hg : JointFiberContDiffOn e f b r U g) :
    JointFiberContDiffOn e f c r U
      (fun p x ↦ parameter_graph_fibre_cast (b p) (c p) (congrFun hbc p) (g p x)) := by
  subst c
  simpa only [parameter_graph_fibre_cast,ContinuousLinearEquiv.refl_apply] using hg

/-- The actual return in the receiving fibre. -/
def returnMap [TopologicalSpace I] (h : I≃ₜI) (H : ∀p,X p≃ₜX (h p)) (q : I) (x : X q) : X (h.symm q) :=
  (H (h.symm q)).symm
    (parameter_graph_fibre_cast q (h (h.symm q)) (h.apply_symm_apply q).symm x)

/-- The actual image action in receiving indices. -/
def receivingAction [TopologicalSpace I] (h : I≃ₜI) (G : ∀p,X p×Y p→X (h p)×Y (h p))
    (s : ∀p,X p→Y p) (H : ∀p,X p≃ₜX (h p))
    (q : I) (z : X q×(X (h.symm q)→L[ℝ]Y (h.symm q))) : X q→L[ℝ]Y q :=
  parameter_graph_fibre_cast (F:=fun p ↦ X p→L[ℝ]Y p)
    (h (h.symm q)) q (h.apply_symm_apply q)
    (action h G s (h.symm q) (returnMap h H q z.1,z.2))

/-- Reindexing the source action by the actual regular return gives the
regular receiving action on an open neighborhood of its invertible domain. -/
theorem receiving_action_joint
    [TopologicalSpace I] [TopologicalSpace (Sigma X)] [TopologicalSpace (Sigma Y)]
    [TopologicalSpace (Sigma (fun p ↦ X p×Y p))]
    (e : SplitFiniteRankNormedAtlas (E₁ := X) (E₂ := Y))
    (h : I≃ₜI) (G : ∀p,X p×Y p→X (h p)×Y (h p)) (s : ∀p,X p→Y p)
    (H : ∀p,X p≃ₜX (h p)) (n : ℕ)
    (hGj : JointFiberContDiff e.total e.total h (n+1) G)
    (hsj : JointFiberContDiff e.first e.second id n s)
    (hR : JointFiberContDiff e.first e.first h.symm n (returnMap h H)) :
    letI := ParameterGraphHomAtlas.topology e.first e.second
    let f := ParameterGraphHomAtlas.atlas e.first e.second
    letI := ParameterGraphPullbackAtlas.topology f h.symm h.symm.continuous
    letI := ParameterGraphProductAtlas.topology (E:=X) (F:=fun p ↦ X (h.symm p)→L[ℝ]Y (h.symm p))
    let W := {z : Sigma (fun p ↦ X p×(X (h.symm p)→L[ℝ]Y (h.symm p))) |
      (blockA h G s (h.symm z.1) (returnMap h H z.1 z.2.1)+
        (blockB h G s (h.symm z.1) (returnMap h H z.1 z.2.1)).comp z.2.2).IsInvertible}
    IsOpen W ∧ JointFiberContDiffOn
      (ParameterGraphProductAtlas.atlas e.first (ParameterGraphPullbackAtlas.atlas f h.symm h.symm.continuous))
      f id n W (receivingAction h G s H) := by
  let := ParameterGraphHomAtlas.topology e.first e.second
  let f := ParameterGraphHomAtlas.atlas e.first e.second
  let := ParameterGraphPullbackAtlas.topology f h.symm h.symm.continuous
  let fp := ParameterGraphPullbackAtlas.atlas f h.symm h.symm.continuous
  let := ParameterGraphProductAtlas.topology (E:=X) (F:=fun p ↦ X (h.symm p)→L[ℝ]Y (h.symm p))
  let er := ParameterGraphProductAtlas.atlas e.first fp
  let := ParameterGraphProductAtlas.topology (E:=X) (F:=fun p ↦ X p→L[ℝ]Y p)
  let es := ParameterGraphProductAtlas.atlas e.first f
  have hr := parameter_graph_joint_comp er e.first e.first id continuous_id h.symm h.symm.continuous
    (fun _ z ↦ z.1) (returnMap h H) n (parameter_graph_joint_native_fst e.first fp n) hR
  have hp : JointFiberContDiffOn er f h.symm n univ (fun _ z ↦ z.2) :=
    (parameter_graph_local_joint_pullback_iff er f h.symm h.symm.continuous n univ isOpen_univ
      (fun _ z ↦ z.2)).mp
      (jointFiberContDiffOn_univ_iff.mpr (parameter_graph_joint_native_snd e.first fp n))
  let K (p : I) (z : X p×(X (h.symm p)→L[ℝ]Y (h.symm p))) := (returnMap h H p z.1,z.2)
  have hK : JointFiberContDiff er es h.symm n K := jointFiberContDiffOn_univ_iff.mp
    (parameter_graph_local_joint_pair er e.first f h.symm h.symm.continuous n univ isOpen_univ
      (fun p z ↦ returnMap h H p z.1) (fun _ z ↦ z.2)
      (jointFiberContDiffOn_univ_iff.mpr hr) hp)
  have hKc := continuousOn_univ.mp (parameter_graph_local_joint_value_continuous er es h.symm
    h.symm.continuous K n univ isOpen_univ (jointFiberContDiffOn_univ_iff.mpr hK))
  obtain ⟨ho,hA⟩ := source_action_joint_over e h G s n hGj hsj
  let W := {z : Sigma (fun p ↦ X p×(X (h.symm p)→L[ℝ]Y (h.symm p))) |
    (blockA h G s (h.symm z.1) (returnMap h H z.1 z.2.1)+
      (blockB h G s (h.symm z.1) (returnMap h H z.1 z.2.1)).comp z.2.2).IsInvertible}
  have hW : IsOpen W := ho.preimage hKc
  have hcomp := parameter_graph_local_joint_comp er es f h.symm h.symm.continuous h h.continuous
    K (action h G s) n W _ hW ho
    ((jointFiberContDiffOn_univ_iff.mpr hK).mono (subset_univ W)) hA (fun _ hz ↦ hz)
  refine ⟨hW,?_⟩
  exact joint_cast_base er f (h ∘ h.symm) id (funext h.apply_symm_apply)
    (fun p z ↦ action h G s (h.symm p) (K p z)) n W hcomp

lemma cast_norm {A : Type*} {E : A→Type*}
    [∀p,NormedAddCommGroup (E p)] [∀p,NormedSpace ℝ (E p)]
    (p q : A) (hpq : p=q) (x : E p) :
    ‖parameter_graph_fibre_cast p q hpq x‖=‖x‖ := by
  subst q
  rfl

lemma cast_cancel {A : Type*} {E : A→Type*}
    [∀p,NormedAddCommGroup (E p)] [∀p,NormedSpace ℝ (E p)]
    (p q : A) (hpq : p=q) (x : E p) :
    parameter_graph_fibre_cast q p hpq.symm (parameter_graph_fibre_cast p q hpq x)=x := by
  subst q
  rfl

lemma cast_fderiv (p q : I) (hpq : p=q) (x : X p) :
    parameter_graph_fibre_cast (F:=fun p ↦ X p→L[ℝ]Y p) p q hpq (fderiv ℝ (s p) x)=
      fderiv ℝ (s q) (parameter_graph_fibre_cast p q hpq x) := by
  subst q
  rfl

/-- One full image regularity step in the original moving fibres. The
continuous actual graph derivative is the invariant section of the receiving
rational action. Its strict slope bound places it inside the unit strip;
the contracting return and vertical action give joint order n, hence s has
joint order n+1 by the derivative criterion. HPS pp.33–36,62. -/
theorem regularity_step
    [TopologicalSpace I] [CompactSpace I]
    [TopologicalSpace (Sigma X)] [TopologicalSpace (Sigma Y)]
    [TopologicalSpace (Sigma (fun p ↦ X p×Y p))]
    (e : SplitFiniteRankNormedAtlas (E₁ := X) (E₂ := Y))
    (h : I≃ₜI) (G : ∀p,X p×Y p→X (h p)×Y (h p)) (s : ∀p,X p→Y p)
    (n : ℕ) (hn : 1≤n) (hGj : JointFiberContDiff e.total e.total h (n+1) G)
    (hsj : JointFiberContDiff e.first e.second id n s)
    (hzero : ∀p,G p 0=0) (hs : ∀p,s p 0=0 ∧ LipschitzWith 1 (s p))
    (hgraph : ∀p,G p '' range (fun x ↦ (x,s p x))=range (fun y ↦ (y,s (h p) y)))
    (T : ∀p,X p≃L[ℝ]X (h p)) (S : ∀p,Y p→L[ℝ]Y (h p))
    (a k ε : NNReal) (ha : ∀p,‖(T p).symm.toContinuousLinearMap‖≤a)
    (hk : ∀p,‖S p‖≤k) (hsmall : 2*(a:ℝ)*ε<1)
    (hslope : (a:ℝ)*(k+2*ε)≤1)
    (hjet : (a:ℝ)*(k+2*ε)/(1-2*(a:ℝ)*ε)<1)
    (hstrong : (a:ℝ)/(1-(a:ℝ)*ε)<1)
    (hpert : ∀p,LipschitzWith ε (fun z ↦ G p z-(T p z.1,S p z.2))) :
    JointFiberContDiff e.first e.second id (n+1) s := by
  classical
  let : ∀p,FiniteDimensional ℝ (X p) := fun p ↦
    (e.first.coordinates p p (e.first.mem_baseSet p)).symm.toLinearEquiv.finiteDimensional
  let : ∀p,FiniteDimensional ℝ (Y p) := fun p ↦
    (e.second.coordinates p p (e.second.mem_baseSet p)).symm.toLinearEquiv.finiteDimensional
  let : ∀p,CompleteSpace (X p) := fun p ↦ inferInstance
  let : ∀p,CompleteSpace (Y p) := fun p ↦ inferInstance
  have hd : 0<1-2*(a:ℝ)*ε := sub_pos.mpr hsmall
  have hd' : 0<1-(a:ℝ)*ε := by nlinarith [a.2,ε.2]
  let q : NNReal := ⟨(a:ℝ)*(k+2*ε)/(1-2*(a:ℝ)*ε),by positivity⟩
  let c : NNReal := ⟨(a:ℝ)/(1-(a:ℝ)*ε),by positivity⟩
  obtain ⟨H,hfirst,hsecond,hH0,hHi,hHj,hHc,hir⟩ := horizontal_return_data e h G s n hn
    hGj hsj hzero hs hgraph T S a k ε ha hk hsmall hslope hpert
  have hGd : ∀p,Differentiable ℝ (G p) := fun p ↦ (hGj.1 p).differentiable (by simp)
  have hsd : ∀p,Differentiable ℝ (s p) := fun p ↦
    (hsj.1 p).differentiable (by exact_mod_cast (show n≠0 by omega))
  have heq := slope_equation_and_bound h G s H hfirst hsecond hGd hsd (fun p ↦ (hs p).2)
    T S a k ε ha hk hsmall hjet hpert
  have hrat (p : I) (x : X p) :
      (∀P : X p→L[ℝ]Y p,‖P‖≤1 →
        (blockA h G s p x+(blockB h G s p x).comp P).IsInvertible ∧
        ‖action h G s p (x,P)‖≤q) ∧
      (∀P Q : X p→L[ℝ]Y p,‖P‖≤1 → ‖Q‖≤1 →
        ‖action h G s p (x,P)-action h G s p (x,Q)‖≤(q:ℝ)*‖P-Q‖) := by
    have hb := block_bounds h G s T S k ε hk hpert hGd p x
    obtain ⟨q',hq',_,hbound,hLip⟩ := parameter_graph_actual_image_slope_bounds (T p)
      (blockA h G s p x) (blockB h G s p x) (blockC h G s p x) (blockD h G s p x)
      a k ε (ha p) hb.1 hb.2.1 hb.2.2.1 hb.2.2.2 hsmall hjet
    have hqq : q'=q := NNReal.coe_injective hq'
    subst q'
    exact ⟨hbound,hLip⟩
  have hRL : ∀p,LipschitzWith c (returnMap h H p) := by
    intro p
    apply LipschitzWith.of_dist_le_mul
    intro u v
    have hi := hHi (h.symm p)
      (parameter_graph_fibre_cast p (h (h.symm p)) (h.apply_symm_apply p).symm u)
      (parameter_graph_fibre_cast p (h (h.symm p)) (h.apply_symm_apply p).symm v)
    rw [← (parameter_graph_fibre_cast p (h (h.symm p)) (h.apply_symm_apply p).symm).map_sub u v,cast_norm] at hi
    simp only [dist_eq_norm]
    exact hi
  have hR0 : ∀p,returnMap h H p 0=0 := by
    intro p
    change (H (h.symm p)).symm (parameter_graph_fibre_cast p (h (h.symm p)) _ 0)=0
    rw [map_zero]
    exact (hH0 (h.symm p)).2
  have hcast (p : I) (x : X p) :
      parameter_graph_fibre_cast (F:=fun p ↦ X p→L[ℝ]Y p)
        (h (h.symm p)) p (h.apply_symm_apply p)
        (fderiv ℝ (s (h (h.symm p))) (H (h.symm p) (returnMap h H p x)))=
      fderiv ℝ (s p) x := by
    rw [cast_fderiv]
    simp only [returnMap,(H (h.symm p)).apply_symm_apply]
    exact congrArg (fderiv ℝ (s p)) (cast_cancel p (h (h.symm p)) (h.apply_symm_apply p).symm x)
  have hP : ∀p x,‖fderiv ℝ (s p) x‖≤(q:ℝ) := by
    intro p x
    rw [← hcast p x,cast_norm]
    exact (heq (h.symm p) (returnMap h H p x)).2.2
  have hinv : ∀p x,fderiv ℝ (s p) x=
      receivingAction h G s H p (x,fderiv ℝ (s (h.symm p)) (returnMap h H p x)) := by
    intro p x
    rw [← hcast p x]
    exact congrArg (parameter_graph_fibre_cast (F:=fun p ↦ X p→L[ℝ]Y p)
      (h (h.symm p)) p (h.apply_symm_apply p))
      (heq (h.symm p) (returnMap h H p x)).2.1
  have hvert : ∀p x,LipschitzOnWith q (fun v ↦ receivingAction h G s H p (x,v))
      (Metric.closedBall 0 1) := by
    intro p x
    apply LipschitzOnWith.of_dist_le_mul
    intro P hP Q hQ
    have hP' : ‖P‖≤1 := by simpa only [Metric.mem_closedBall,dist_zero_right] using hP
    have hQ' : ‖Q‖≤1 := by simpa only [Metric.mem_closedBall,dist_zero_right] using hQ
    simp only [dist_eq_norm]
    unfold receivingAction
    rw [← map_sub,cast_norm]
    exact (hrat (h.symm p) (returnMap h H p x)).2 P Q hP' hQ'
  let := ParameterGraphHomAtlas.topology e.first e.second
  let f := ParameterGraphHomAtlas.atlas e.first e.second
  have hs1 := (jointFiberContDiffOn_univ_iff.mpr hsj).of_le hn
  have hPc : Continuous (fun z : Sigma X ↦
      (⟨z.1,fderiv ℝ (s z.1) z.2⟩ : Sigma (fun p ↦ X p→L[ℝ]Y p))) :=
    continuousOn_univ.mp (parameter_graph_local_joint_value_continuous e.first f id continuous_id
      (fun p ↦ fderiv ℝ (s p)) 0 univ isOpen_univ
      (parameter_graph_local_joint_derivative e.first e.second s 0 univ isOpen_univ hs1))
  obtain ⟨hW,hF⟩ := receiving_action_joint e h G s H n hGj hsj hir
  have hstrip : ∀p (x:X p) (v:X (h.symm p)→L[ℝ]Y (h.symm p)),‖v‖≤1 →
      (blockA h G s (h.symm p) (returnMap h H p x)+
        (blockB h G s (h.symm p) (returnMap h H p x)).comp v).IsInvertible :=
    fun p x v hv ↦ ((hrat (h.symm p) (returnMap h H p x)).1 v hv).1
  have hPreg := parameter_graph_global_section_regularity e.first f h.symm h.symm.continuous
    (returnMap h H) (receivingAction h G s H) (fun p ↦ fderiv ℝ (s p)) n
    c q hstrong hjet hRL hR0 hir hPc q 1 hjet hP hinv hvert _ hW hF hstrip
  apply parameter_graph_joint_of_derivative e.first e.second s n _ hsd hPreg
  exact continuousOn_univ.mp (parameter_graph_local_joint_value_continuous e.first e.second id
    continuous_id s n univ isOpen_univ (jointFiberContDiffOn_univ_iff.mpr hsj))

end ParameterGraphImageSlopeData
end HolomorphicAnosov
