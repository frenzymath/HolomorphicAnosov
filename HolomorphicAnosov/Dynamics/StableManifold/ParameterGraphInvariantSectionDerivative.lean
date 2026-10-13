import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphJetIdentification
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphTaylorJetTransport
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphBoundedSectionFixedPoint
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Operations

noncomputable section
open Filter Asymptotics
open scoped Topology
namespace HolomorphicAnosov
open BoundedLipschitzJets

/-- The Taylor defect for a nonlinear invariant section is the vertical
linearized action on its receiving defect, modulo little-o. Expand the smooth
map along the Lipschitz displacement `(v,T(R(x+v))-T(Rx))`. Subtract the
linearized invariance equation. The remaining error is the ambient Taylor
remainder plus the bounded linear image of the Taylor remainder of R. No
derivative of either section P or T is assumed. This is the local calculation
in HPS, Invariant Manifolds, pp.32–35, for differentiating an invariant section. -/
theorem parameter_graph_section_taylor_defect
    {X Y U V : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup U] [NormedSpace ℝ U]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (R : X → U) (F : X × V → Y) (P : X → Y) (T : U → V)
    (L c : NNReal) (hR : LipschitzWith c R) (hT : LipschitzWith L T)
    (hinv : ∀ x, P x = F (x, T (R x))) (x : X)
    (dR : X →L[ℝ] U) (hdR : HasFDerivAt R dR x)
    (dF : X × V →L[ℝ] Y) (hdF : HasFDerivAt F dF (x,T (R x)))
    (D : X →L[ℝ] Y) (Dnext : U →L[ℝ] V)
    (hlin : ∀ v, D v = dF (v, Dnext (dR v))) :
    (fun v ↦ (P (x+v) - P x - D v) -
      dF (0, T (R (x+v)) - T (R x) - Dnext (R (x+v)-R x)))
      =o[𝓝 (0 : X)] (fun v ↦ v) := by
  let u : X → X × V := fun v ↦ (v,T (R (x+v))-T (R x))
  have hu0 : u 0 = 0 := by simp [u]
  have hu : LipschitzWith (max 1 (L*c)) u := by
    apply LipschitzWith.of_dist_le_mul
    intro v w
    simp only [u, Prod.dist_eq, NNReal.coe_max, NNReal.coe_one, NNReal.coe_mul,
      dist_sub_right]
    apply max_le
    · exact le_mul_of_one_le_left (dist_nonneg) (le_max_left _ _)
    · calc
        dist (T (R (x+v))) (T (R (x+w))) ≤ (L*c : NNReal) * dist (x+v) (x+w) :=
          (hT.comp hR).dist_le_mul _ _
        _ ≤ max 1 ((L : ℝ)*c) * dist v w := by
          simpa only [dist_add_left, NNReal.coe_mul] using
            mul_le_mul_of_nonneg_right (le_max_right (1 : ℝ) ((L : ℝ)*c)) (show 0 ≤ dist (x+v) (x+w) from dist_nonneg)
  let remF : X → Y := fun v ↦ F ((x,T (R x))+u v) - F (x,T (R x)) - dF (u v)
  have hremF : remF =o[𝓝 (0 : X)] (fun v ↦ v) :=
    parameter_graph_lipschitz_taylor F dF (x,T (R x)) hdF u hu0 _ hu
  let remR : X → U := fun v ↦ R (x+v)-R x-dR v
  have hremR : remR =o[𝓝 (0 : X)] (fun v ↦ v) :=
    hasFDerivAt_iff_isLittleO_nhds_zero.mp hdR
  let B : V →L[ℝ] Y := dF.comp (ContinuousLinearMap.inr ℝ X V)
  let K : U →L[ℝ] Y := B.comp Dnext
  have hKrem : (fun v ↦ K (remR v)) =o[𝓝 (0 : X)] (fun v ↦ v) :=
    (K.isBigO_comp remR (𝓝 0)).trans_isLittleO hremR
  have huval (v : X) : dF (u v) = D v + B (T (R (x+v))-T (R x)-Dnext (dR v)) := by
    rw [hlin v]
    change dF (u v) = dF (v,Dnext (dR v)) + dF (0,T (R (x+v))-T (R x)-Dnext (dR v))
    rw [← map_add]
    congr 1
    ext <;> simp [u]
  have heq (v : X) :
      (P (x+v) - P x - D v) -
        dF (0,T (R (x+v))-T (R x)-Dnext (R (x+v)-R x)) = remF v + K (remR v) := by
    have hpoint : (x,T (R x))+u v = (x+v,T (R (x+v))) := by
      ext <;> simp [u]
    change (P (x+v) - P x - D v) -
      B (T (R (x+v))-T (R x)-Dnext (R (x+v)-R x)) = remF v + B (Dnext (remR v))
    simp only [remF, hpoint, ← hinv, huval, remR, map_sub]
    abel
  exact (hremF.add hKrem).congr_left (fun v ↦ (heq v).symm)

/-- Local form of the section Taylor-defect calculation, using an eventual
graph equation and an eventual bound on the receiving displacement. Taylor
remainders pull back along the centered continuous displacement, whose local
linear bound preserves little-o. Source: HPS pp.32–35. -/
theorem parameter_graph_section_taylor_defect_local
    {X Y U V : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup U] [NormedSpace ℝ U]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (R : X → U) (F : X × V → Y) (P : X → Y) (T : U → V)
    (C : NNReal) (x : X) (hT : ContinuousAt T (R x))
    (hbound : ∀ᶠ v in 𝓝 (0 : X), ‖T (R (x+v))-T (R x)‖ ≤ (C : ℝ)*‖v‖)
    (hinv : ∀ᶠ z in 𝓝 x, P z = F (z,T (R z)))
    (dR : X →L[ℝ] U) (hdR : HasFDerivAt R dR x)
    (dF : X × V →L[ℝ] Y) (hdF : HasFDerivAt F dF (x,T (R x)))
    (D : X →L[ℝ] Y) (Dnext : U →L[ℝ] V)
    (hlin : ∀ v, D v = dF (v, Dnext (dR v))) :
    (fun v ↦ (P (x+v) - P x - D v) -
      dF (0, T (R (x+v)) - T (R x) - Dnext (R (x+v)-R x)))
      =o[𝓝 (0 : X)] (fun v ↦ v) := by
  let u : X → X × V := fun v ↦ (v,T (R (x+v))-T (R x))
  have hu0 : u 0 = 0 := by simp [u]
  have hvzero : Tendsto (fun v : X ↦ x+v) (𝓝 0) (𝓝 x) := by
    simpa only [ContinuousAt, add_zero] using
      (show Continuous (fun v : X ↦ x+v) from continuous_const.add continuous_id).continuousAt (x := 0)
  have hucont : ContinuousAt u 0 := by
    have hRc := hdR.continuousAt.tendsto.comp hvzero
    have hTc := hT.tendsto.comp hRc
    have hTc' : ContinuousAt (fun v : X ↦ T (R (x+v))) 0 := by
      simpa only [ContinuousAt, add_zero, Function.comp_def] using hTc
    exact continuousAt_id.prodMk (hTc'.sub continuousAt_const)
  have hubig : u =O[𝓝 (0 : X)] (fun v ↦ v) := by
    apply IsBigO.of_bound (max 1 (C : ℝ))
    filter_upwards [hbound] with v hv
    change max ‖v‖ ‖T (R (x+v))-T (R x)‖ ≤ max 1 (C : ℝ)*‖v‖
    exact max_le (le_mul_of_one_le_left (norm_nonneg _) (le_max_left _ _))
      (hv.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _)))
  let remF : X → Y := fun v ↦ F ((x,T (R x))+u v) - F (x,T (R x)) - dF (u v)
  have hremF : remF =o[𝓝 (0 : X)] (fun v ↦ v) :=
    ((hasFDerivAt_iff_isLittleO_nhds_zero.mp hdF).comp_tendsto
      (hu0 ▸ hucont)).trans_isBigO hubig
  let remR : X → U := fun v ↦ R (x+v)-R x-dR v
  have hremR : remR =o[𝓝 (0 : X)] (fun v ↦ v) :=
    hasFDerivAt_iff_isLittleO_nhds_zero.mp hdR
  let B : V →L[ℝ] Y := dF.comp (ContinuousLinearMap.inr ℝ X V)
  let K : U →L[ℝ] Y := B.comp Dnext
  have hKrem : (fun v ↦ K (remR v)) =o[𝓝 (0 : X)] (fun v ↦ v) :=
    (K.isBigO_comp remR (𝓝 0)).trans_isLittleO hremR
  have huval (v : X) : dF (u v) = D v + B (T (R (x+v))-T (R x)-Dnext (dR v)) := by
    rw [hlin v]
    change dF (u v) = dF (v,Dnext (dR v)) + dF (0,T (R (x+v))-T (R x)-Dnext (dR v))
    rw [← map_add]
    congr 1
    ext <;> simp [u]
  have hz : P x = F (x,T (R x)) := hinv.self_of_nhds
  have heq : ∀ᶠ v in 𝓝 (0 : X),
      (P (x+v) - P x - D v) -
        dF (0,T (R (x+v))-T (R x)-Dnext (R (x+v)-R x)) = remF v + K (remR v) := by
    filter_upwards [hvzero.eventually hinv] with v hv
    have hpoint : (x,T (R x))+u v = (x+v,T (R (x+v))) := by
      ext <;> simp [u]
    change (P (x+v) - P x - D v) -
      B (T (R (x+v))-T (R x)-Dnext (R (x+v)-R x)) = remF v + B (Dnext (remR v))
    simp only [remF, hpoint, ← hv, ← hz, huval, remR, map_sub]
    abel
  exact (hremF.add hKrem).congr' (Filter.EventuallyEq.symm heq) Filter.EventuallyEq.rfl

/-- A uniformly bounded invariant candidate derivative is the actual derivative
of a uniformly Lipschitz nonlinear invariant section, whenever the vertical
linearized bound b times the spatial return bound c is less than one.

Index all spatial anchors by Sigma X. At each anchor the translated section
is a bounded jet representative; its defect from the candidate derivative has
norm at most L+M. The preceding Taylor calculation and jet transport bound the
defect by b*c times the defect at the returned anchor. Iteration gives
(L+M)*(b*c)^n for every n. Geometric decay makes the defects zero, and the
bounded-jet derivative criterion identifies the candidate with the actual
Frechet derivative. The return may be noninvertible; neither section
smoothness nor convergence of derivatives is assumed. This is the derivative
identification step in HPS pp.32–35. -/
theorem parameter_graph_invariant_section_derivative
    {A : Type*} (X Y : A → Type*)
    [∀ p, NormedAddCommGroup (X p)] [∀ p, NormedSpace ℝ (X p)]
    [∀ p, NormedAddCommGroup (Y p)] [∀ p, NormedSpace ℝ (Y p)]
    (h : A → A) (R : ∀ p, X p → X (h p))
    (F : ∀ p, X p × Y (h p) → Y p) (P : ∀ p, X p → Y p)
    (L M b c : NNReal)
    (hP : ∀ p, LipschitzWith L (P p))
    (hR : ∀ p, LipschitzWith c (R p))
    (hinv : ∀ p x, P p x = F p (x,P (h p) (R p x)))
    (dR : ∀ p, X p → X p →L[ℝ] X (h p))
    (hdR : ∀ p x, HasFDerivAt (R p) (dR p x) x)
    (dF : ∀ p, X p → X p × Y (h p) →L[ℝ] Y p)
    (hdF : ∀ p x, HasFDerivAt (F p) (dF p x) (x,P (h p) (R p x)))
    (hvert : ∀ p x, ‖(dF p x).comp (ContinuousLinearMap.inr ℝ (X p) (Y (h p)))‖ ≤ b)
    (hq : (b : ℝ) * c < 1)
    (D : ∀ p, X p → X p →L[ℝ] Y p)
    (hD : ∀ p x, ‖D p x‖ ≤ M)
    (hlin : ∀ p x v, D p x v = dF p x (v,D (h p) (R p x) (dR p x v))) :
    ∀ p x, HasFDerivAt (P p) (D p x) x := by
  let T : Sigma X → Sigma X := fun i ↦ ⟨h i.1, R i.1 i.2⟩
  let r : ∀ i : Sigma X, X i.1 → X (T i).1 := fun i v ↦
    R i.1 (i.2+v) - R i.1 i.2
  have hr (i : Sigma X) : LipschitzWith c (r i) := by
    apply LipschitzWith.of_dist_le_mul
    intro v w
    simpa only [r, dist_sub_right, dist_add_left] using
      (hR i.1).dist_le_mul (i.2+v) (i.2+w)
  have hsbound (i : Sigma X) (v : X i.1) :
      ‖P i.1 (i.2+v)-P i.1 i.2‖ ≤ (L : ℝ)*‖v‖ := by
    simpa only [add_sub_cancel_left] using (hP i.1).norm_sub_le (i.2+v) i.2
  let Q : ∀ i : Sigma X, BoundedRepresentative (X i.1) (Y i.1) := fun i ↦
    ⟨fun v ↦ P i.1 (i.2+v)-P i.1 i.2, by
      refine ⟨by simp, L, L.2, ?_⟩
      exact Eventually.of_forall (fun v ↦ hsbound i v)⟩
  let E : ∀ i : Sigma X, BoundedRepresentative (X i.1) (Y i.1) := fun i ↦
    Q i - linearRepresentative (X i.1) (Y i.1) (D i.1 i.2)
  have hE (i : Sigma X) : ‖jetClass (X i.1) (Y i.1) (E i)‖ ≤ (L : ℝ)+M := by
    change sInf (slopeBounds (X i.1) (Y i.1) (E i)) ≤ (L : ℝ)+M
    apply csInf_le ⟨0, fun _ h ↦ h.1⟩
    refine ⟨add_nonneg L.2 M.2, Eventually.of_forall (fun v ↦ ?_)⟩
    change ‖P i.1 (i.2+v)-P i.1 i.2-D i.1 i.2 v‖ ≤ ((L : ℝ)+M)*‖v‖
    calc
      _ ≤ ‖P i.1 (i.2+v)-P i.1 i.2‖+‖D i.1 i.2 v‖ := norm_sub_le _ _
      _ ≤ (L : ℝ)*‖v‖+(M : ℝ)*‖v‖ := add_le_add (hsbound i v)
        (((D i.1 i.2).le_opNorm v).trans
          (mul_le_mul_of_nonneg_right (hD i.1 i.2) (norm_nonneg _)))
      _ = _ := (add_mul _ _ _).symm
  have hident := parameter_graph_jet_identification
    (fun i : Sigma X ↦ X i.1) (fun i : Sigma X ↦ Y i.1) T
    (fun i ↦ P i.1) (fun i ↦ i.2) (fun i ↦ D i.1 i.2) Q
    (fun _ _ ↦ rfl) (b*c) (by simpa using hq) ((L : ℝ)+M) hE
  apply fun p x ↦ hident ?_ ⟨p,x⟩
  intro i
  change ‖jetClass (X i.1) (Y i.1) (E i)‖ ≤
    ((b*c : NNReal) : ℝ) * ‖jetClass (X (T i).1) (Y (T i).1) (E (T i))‖
  apply (parameter_graph_taylor_jet_transport (E i) (E (T i)) (r i)
    (hr i).continuous.continuousAt (by simp [r])
    ((dF i.1 i.2).comp (ContinuousLinearMap.inr ℝ (X i.1) (Y (h i.1))))
    b c (hvert i.1 i.2)
    (Eventually.of_forall (fun v ↦ by
      simpa only [r, add_zero, sub_self, sub_zero] using (hr i).norm_sub_le v 0)) ?_).trans_eq
    (by simp only [NNReal.coe_mul])
  have he := parameter_graph_section_taylor_defect (R i.1) (F i.1) (P i.1) (P (h i.1))
    L c (hR i.1) (hP (h i.1)) (hinv i.1) i.2 (dR i.1 i.2) (hdR i.1 i.2)
    (dF i.1 i.2) (hdF i.1 i.2) (D i.1 i.2) (D (h i.1) (R i.1 i.2)) (hlin i.1 i.2)
  change (fun v ↦ (P i.1 (i.2+v)-P i.1 i.2-D i.1 i.2 v) -
    dF i.1 i.2 (0,P (h i.1) (R i.1 i.2 + (R i.1 (i.2+v)-R i.1 i.2)) -
      P (h i.1) (R i.1 i.2) - D (h i.1) (R i.1 i.2) (R i.1 (i.2+v)-R i.1 i.2)))
      =o[𝓝 (0 : X i.1)] (fun v ↦ v)
  simpa only [add_sub_cancel] using he


/-- The local-anchor version of invariant derivative identification. Only an
eventual radial bound on each centered section germ is used; a common local
Lipschitz bound on inward discs supplies it. Each centered return is continuous
at zero and eventually bounded by c times the displacement norm. The given
Taylor-defect identity and bounded candidate derivative make every defect jet
at most L+M, and contract its norm by b*c<1 along the arbitrary anchor return.
Jet identification proves the derivative without any extension of the germs
or global Lipschitz condition on the section maps. Source: HPS pp.32–35. -/
theorem parameter_graph_invariant_taylor_derivative_local
    {I : Type*} (X Y : I → Type*)
    [∀ i, NormedAddCommGroup (X i)] [∀ i, NormedSpace ℝ (X i)]
    [∀ i, NormedAddCommGroup (Y i)] [∀ i, NormedSpace ℝ (Y i)]
    (R : I → I) (s : ∀ i, X i → Y i) (x : ∀ i, X i)
    (L M : NNReal)
    (hs : ∀ i, ∀ᶠ v in 𝓝 (0 : X i),
      ‖s i (x i+v)-s i (x i)‖ ≤ (L : ℝ)*‖v‖)
    (P : ∀ i, X i →L[ℝ] Y i) (hP : ∀ i, ‖P i‖ ≤ M)
    (r : ∀ i, X i → X (R i))
    (hr : ∀ i, ContinuousAt (r i) 0) (hr0 : ∀ i, r i 0 = 0)
    (B : ∀ i, Y (R i) →L[ℝ] Y i) (b c : NNReal)
    (hB : ∀ i, ‖B i‖ ≤ b) (hq : (b : ℝ)*c < 1)
    (hbound : ∀ i, ∀ᶠ v in 𝓝 (0 : X i), ‖r i v‖ ≤ (c : ℝ)*‖v‖)
    (herror : ∀ i,
      (fun v ↦ (s i (x i+v)-s i (x i)-P i v) -
        B i (s (R i) (x (R i)+r i v)-s (R i) (x (R i))-P (R i) (r i v)))
        =o[𝓝 (0 : X i)] (fun v ↦ v)) :
    ∀ i, HasFDerivAt (s i) (P i) (x i) := by
  let Q : ∀ i, BoundedRepresentative (X i) (Y i) := fun i ↦
    ⟨fun v ↦ s i (x i+v)-s i (x i), by
      refine ⟨by simp, L, L.2, ?_⟩
      exact (hs i).filter_mono nhdsWithin_le_nhds⟩
  let E : ∀ i, BoundedRepresentative (X i) (Y i) := fun i ↦
    Q i - linearRepresentative (X i) (Y i) (P i)
  have hE (i : I) : ‖jetClass (X i) (Y i) (E i)‖ ≤ (L : ℝ)+M := by
    change sInf (slopeBounds (X i) (Y i) (E i)) ≤ (L : ℝ)+M
    apply csInf_le ⟨0, fun _ h ↦ h.1⟩
    refine ⟨add_nonneg L.2 M.2, ?_⟩
    filter_upwards [(hs i).filter_mono nhdsWithin_le_nhds] with v hv
    change ‖s i (x i+v)-s i (x i)-P i v‖ ≤ ((L : ℝ)+M)*‖v‖
    calc
      _ ≤ ‖s i (x i+v)-s i (x i)‖+‖P i v‖ := norm_sub_le _ _
      _ ≤ (L : ℝ)*‖v‖+(M : ℝ)*‖v‖ := add_le_add hv
        (((P i).le_opNorm v).trans
          (mul_le_mul_of_nonneg_right (hP i) (norm_nonneg _)))
      _ = _ := (add_mul _ _ _).symm
  apply parameter_graph_jet_identification X Y R s x P Q (fun _ _ ↦ rfl)
    (b*c) (by simpa using hq) ((L : ℝ)+M) hE
  intro i
  change ‖jetClass (X i) (Y i) (E i)‖ ≤
    ((b*c : NNReal) : ℝ)*‖jetClass (X (R i)) (Y (R i)) (E (R i))‖
  simpa only [NNReal.coe_mul] using
    parameter_graph_taylor_jet_transport (E i) (E (R i)) (r i) (hr i) (hr0 i)
      (B i) b c (hB i) (hbound i) (herror i)

/-- HPS pp.32–35: differentiability of an invariant Lipschitz section from a
contracting affine derivative action. On the anchor set Sigma X, the action on
linear maps is H + V ∘ Dnext ∘ dR. Its contraction factor is b*c and its forcing
is bounded by B. The bounded-section theorem constructs a candidate derivative
of norm at most B/(1-b*c). Taylor defect identification proves that it is the
actual derivative. Completeness is required only for the target fibres. -/
theorem parameter_graph_invariant_section_differentiable
    {A : Type*} (X Y : A → Type*)
    [∀ p, NormedAddCommGroup (X p)] [∀ p, NormedSpace ℝ (X p)]
    [∀ p, NormedAddCommGroup (Y p)] [∀ p, NormedSpace ℝ (Y p)]
    [∀ p, CompleteSpace (Y p)]
    (h : A → A) (R : ∀ p, X p → X (h p))
    (F : ∀ p, X p × Y (h p) → Y p) (P : ∀ p, X p → Y p)
    (L B b c : NNReal)
    (hP : ∀ p, LipschitzWith L (P p))
    (hR : ∀ p, LipschitzWith c (R p))
    (hinv : ∀ p x, P p x = F p (x,P (h p) (R p x)))
    (dR : ∀ p, X p → X p →L[ℝ] X (h p))
    (hdR : ∀ p x, HasFDerivAt (R p) (dR p x) x)
    (dF : ∀ p, X p → X p × Y (h p) →L[ℝ] Y p)
    (hdF : ∀ p x, HasFDerivAt (F p) (dF p x) (x,P (h p) (R p x)))
    (hvert : ∀ p x, ‖(dF p x).comp (ContinuousLinearMap.inr ℝ (X p) (Y (h p)))‖ ≤ b)
    (hhor : ∀ p x, ‖(dF p x).comp (ContinuousLinearMap.inl ℝ (X p) (Y (h p)))‖ ≤ B)
    (hq : (b : ℝ)*c < 1) :
    (∀ p, Differentiable ℝ (P p)) ∧
      ∀ p x, ‖fderiv ℝ (P p) x‖ ≤ (B : ℝ)/(1-(b : ℝ)*c) := by
  let T : Sigma X → Sigma X := fun i ↦ ⟨h i.1,R i.1 i.2⟩
  let E : Sigma X → Type _ := fun i ↦ X i.1 →L[ℝ] Y i.1
  let V (i : Sigma X) := (dF i.1 i.2).comp
    (ContinuousLinearMap.inr ℝ (X i.1) (Y (h i.1)))
  let H (i : Sigma X) := (dF i.1 i.2).comp
    (ContinuousLinearMap.inl ℝ (X i.1) (Y (h i.1)))
  let Φ : ∀ i, E (T i) → E i := fun i D ↦ H i + (V i).comp (D.comp (dR i.1 i.2))
  have hPhi (i : Sigma X) : LipschitzWith (b*c) (Φ i) := by
    apply LipschitzWith.of_dist_le_mul
    intro D D'
    rw [dist_eq_norm, dist_eq_norm]
    have heq : Φ i D-Φ i D' = (V i).comp ((D-D').comp (dR i.1 i.2)) := by
      ext v
      simp [Φ, map_sub]
    rw [heq]
    calc
      _ ≤ ‖V i‖ * ‖(D-D').comp (dR i.1 i.2)‖ := (V i).opNorm_comp_le _
      _ ≤ (b : ℝ) * (‖D-D'‖ * (c : ℝ)) := mul_le_mul (hvert i.1 i.2)
        (((D-D').opNorm_comp_le _).trans (mul_le_mul_of_nonneg_left
          ((hdR i.1 i.2).le_of_lipschitz (hR i.1)) (norm_nonneg _)))
        (norm_nonneg _) b.2
      _ = _ := by simp only [NNReal.coe_mul]; ring
  have hzero (i : Sigma X) : ‖Φ i 0‖ ≤ B := by
    simpa [Φ] using hhor i.1 i.2
  obtain ⟨D,hDinv,hDbound,-,-⟩ := parameter_graph_bounded_section_fixed_point
    E T Φ (b*c) B (by exact_mod_cast hq) hPhi hzero
  let M : NNReal := ⟨(B : ℝ)/(1-(b : ℝ)*c), div_nonneg B.2 (sub_pos.mpr hq).le⟩
  have hD (p : A) (x : X p) : ‖D ⟨p,x⟩‖ ≤ M := by
    exact hDbound ⟨p,x⟩
  have hlin (p : A) (x : X p) (v : X p) :
      D ⟨p,x⟩ v = dF p x (v,D ⟨h p,R p x⟩ (dR p x v)) := by
    have he := congrArg (fun Q : E ⟨p,x⟩ ↦ Q v) (hDinv ⟨p,x⟩)
    change dF p x (v,0)+dF p x (0,D ⟨h p,R p x⟩ (dR p x v)) = D ⟨p,x⟩ v at he
    rw [← map_add] at he
    simpa only [Prod.mk_add_mk, add_zero, zero_add] using he.symm
  have hd := parameter_graph_invariant_section_derivative X Y h R F P L M b c hP hR hinv
    dR hdR dF hdF hvert hq (fun p x ↦ D ⟨p,x⟩) hD hlin
  refine ⟨fun p x ↦ (hd p x).differentiableAt, fun p x ↦ ?_⟩
  rw [(hd p x).fderiv]
  exact hD p x

/-- Local-domain form of invariant section differentiability. Index the affine
derivative construction only by anchors in open invariant domains. Their local
Lipschitz estimates and graph equations supply the eventual Taylor identity,
and local defect identification gives the derivative and its uniform bound.
This applies to inward open discs without any extension. Source: HPS pp.32–35. -/
theorem parameter_graph_invariant_section_differentiable_on
    {A : Type*} (X Y : A → Type*)
    [∀ p, NormedAddCommGroup (X p)] [∀ p, NormedSpace ℝ (X p)]
    [∀ p, NormedAddCommGroup (Y p)] [∀ p, NormedSpace ℝ (Y p)]
    [∀ p, CompleteSpace (Y p)]
    (h : A → A) (R : ∀ p, X p → X (h p))
    (F : ∀ p, X p × Y (h p) → Y p) (P : ∀ p, X p → Y p)
    (U : ∀ p, Set (X p)) (hU : ∀ p, IsOpen (U p))
    (hRU : ∀ p, Set.MapsTo (R p) (U p) (U (h p)))
    (L B b c : NNReal)
    (hP : ∀ p, LipschitzOnWith L (P p) (U p))
    (hR : ∀ p, LipschitzOnWith c (R p) (U p))
    (hinv : ∀ p x, x ∈ U p → P p x = F p (x,P (h p) (R p x)))
    (dR : ∀ p, X p → X p →L[ℝ] X (h p))
    (hdR : ∀ p x, x ∈ U p → HasFDerivAt (R p) (dR p x) x)
    (dF : ∀ p, X p → X p × Y (h p) →L[ℝ] Y p)
    (hdF : ∀ p x, x ∈ U p → HasFDerivAt (F p) (dF p x) (x,P (h p) (R p x)))
    (hvert : ∀ p x, x ∈ U p → ‖(dF p x).comp (ContinuousLinearMap.inr ℝ (X p) (Y (h p)))‖ ≤ b)
    (hhor : ∀ p x, x ∈ U p → ‖(dF p x).comp (ContinuousLinearMap.inl ℝ (X p) (Y (h p)))‖ ≤ B)
    (hq : (b : ℝ)*c < 1) :
    (∀ p x, x ∈ U p → DifferentiableAt ℝ (P p) x) ∧
      ∀ p x, x ∈ U p → ‖fderiv ℝ (P p) x‖ ≤ (B : ℝ)/(1-(b : ℝ)*c) := by
  let I := Σ p, {x : X p // x ∈ U p}
  let T : I → I := fun i ↦ ⟨h i.1,⟨R i.1 i.2.1,hRU i.1 i.2.2⟩⟩
  let E : I → Type _ := fun i ↦ X i.1 →L[ℝ] Y i.1
  let V (i : I) := (dF i.1 i.2.1).comp
    (ContinuousLinearMap.inr ℝ (X i.1) (Y (h i.1)))
  let H (i : I) := (dF i.1 i.2.1).comp
    (ContinuousLinearMap.inl ℝ (X i.1) (Y (h i.1)))
  let Φ : ∀ i, E (T i) → E i := fun i D ↦ H i + (V i).comp (D.comp (dR i.1 i.2.1))
  have hPhi (i : I) : LipschitzWith (b*c) (Φ i) := by
    apply LipschitzWith.of_dist_le_mul
    intro D D'
    rw [dist_eq_norm, dist_eq_norm]
    have heq : Φ i D-Φ i D' = (V i).comp ((D-D').comp (dR i.1 i.2.1)) := by
      ext v
      simp [Φ, map_sub]
    rw [heq]
    calc
      _ ≤ ‖V i‖ * ‖(D-D').comp (dR i.1 i.2.1)‖ := (V i).opNorm_comp_le _
      _ ≤ (b : ℝ) * (‖D-D'‖ * (c : ℝ)) := mul_le_mul (hvert i.1 i.2.1 i.2.2)
        (((D-D').opNorm_comp_le _).trans (mul_le_mul_of_nonneg_left
          ((hdR i.1 i.2.1 i.2.2).le_of_lipschitzOn ((hU i.1).mem_nhds i.2.2) (hR i.1)) (norm_nonneg _)))
        (norm_nonneg _) b.2
      _ = _ := by simp only [NNReal.coe_mul]; ring
  have hzero (i : I) : ‖Φ i 0‖ ≤ B := by
    simpa [Φ] using hhor i.1 i.2.1 i.2.2
  obtain ⟨D,hDinv,hDbound,-,-⟩ := parameter_graph_bounded_section_fixed_point
    E T Φ (b*c) B (by exact_mod_cast hq) hPhi hzero
  let M : NNReal := ⟨(B : ℝ)/(1-(b : ℝ)*c), div_nonneg B.2 (sub_pos.mpr hq).le⟩
  have hD (i : I) : ‖D i‖ ≤ M := hDbound i
  have hlin (i : I) (v : X i.1) :
      D i v = dF i.1 i.2.1 (v,D (T i) (dR i.1 i.2.1 v)) := by
    have he := congrArg (fun Q : E i ↦ Q v) (hDinv i)
    change dF i.1 i.2.1 (v,0)+dF i.1 i.2.1 (0,D (T i) (dR i.1 i.2.1 v)) = D i v at he
    rw [← map_add] at he
    simpa only [Prod.mk_add_mk, add_zero, zero_add] using he.symm
  let r : ∀ i : I, X i.1 → X (T i).1 := fun i v ↦
    R i.1 (i.2.1+v)-R i.1 i.2.1
  have hvzero (i : I) : Tendsto (fun v : X i.1 ↦ i.2.1+v) (𝓝 0) (𝓝 i.2.1) := by
    simpa only [ContinuousAt, add_zero] using
      (show Continuous (fun v : X i.1 ↦ i.2.1+v) from continuous_const.add continuous_id).continuousAt (x := 0)
  have hnear (i : I) : ∀ᶠ v in 𝓝 (0 : X i.1), i.2.1+v ∈ U i.1 :=
    (hvzero i).eventually ((hU i.1).mem_nhds i.2.2)
  have hr (i : I) : ContinuousAt (r i) 0 := by
    have hc := (hdR i.1 i.2.1 i.2.2).continuousAt.tendsto.comp (hvzero i)
    have hc' : ContinuousAt (fun v : X i.1 ↦ R i.1 (i.2.1+v)) 0 := by
      simpa only [ContinuousAt, Function.comp_def, add_zero] using hc
    exact hc'.sub continuousAt_const
  have hrbound (i : I) : ∀ᶠ v in 𝓝 (0 : X i.1), ‖r i v‖ ≤ (c : ℝ)*‖v‖ := by
    filter_upwards [hnear i] with v hv
    simpa only [r, add_sub_cancel_left] using (hR i.1).norm_sub_le hv i.2.2
  have hsbound (i : I) : ∀ᶠ v in 𝓝 (0 : X i.1),
      ‖P i.1 (i.2.1+v)-P i.1 i.2.1‖ ≤ (L : ℝ)*‖v‖ := by
    filter_upwards [hnear i] with v hv
    simpa only [add_sub_cancel_left] using (hP i.1).norm_sub_le hv i.2.2
  have hd : ∀ i : I, HasFDerivAt (P i.1) (D i) i.2.1 := by
    apply parameter_graph_invariant_taylor_derivative_local
      (fun i : I ↦ X i.1) (fun i : I ↦ Y i.1) T
      (fun i ↦ P i.1) (fun i ↦ i.2.1) L M hsbound D hD r hr
      (fun i ↦ by simp [r]) V b c (fun i ↦ hvert i.1 i.2.1 i.2.2) hq hrbound
    intro i
    have hTcont : ContinuousAt (P (h i.1)) (R i.1 i.2.1) :=
      (hP (h i.1)).continuousOn.continuousAt
        ((hU (h i.1)).mem_nhds (hRU i.1 i.2.2))
    have hrecv : ∀ᶠ v in 𝓝 (0 : X i.1),
        ‖P (h i.1) (R i.1 (i.2.1+v))-P (h i.1) (R i.1 i.2.1)‖ ≤
          ((L*c : NNReal) : ℝ)*‖v‖ := by
      filter_upwards [hnear i] with v hv
      calc
        _ ≤ (L : ℝ)*‖R i.1 (i.2.1+v)-R i.1 i.2.1‖ :=
          (hP (h i.1)).norm_sub_le (hRU i.1 hv) (hRU i.1 i.2.2)
        _ ≤ (L : ℝ)*((c : ℝ)*‖v‖) := mul_le_mul_of_nonneg_left
          (by simpa only [add_sub_cancel_left] using (hR i.1).norm_sub_le hv i.2.2) L.2
        _ = _ := by simp only [NNReal.coe_mul, mul_assoc]
    have heq : ∀ᶠ z in 𝓝 i.2.1, P i.1 z = F i.1 (z,P (h i.1) (R i.1 z)) :=
      Filter.Eventually.mono ((hU i.1).mem_nhds i.2.2) (fun z hz ↦ hinv i.1 z hz)
    have he := parameter_graph_section_taylor_defect_local (R i.1) (F i.1)
      (P i.1) (P (h i.1)) (L*c) i.2.1 hTcont hrecv heq
      (dR i.1 i.2.1) (hdR i.1 i.2.1 i.2.2) (dF i.1 i.2.1) (hdF i.1 i.2.1 i.2.2)
      (D i) (D (T i)) (hlin i)
    change (fun v ↦ (P i.1 (i.2.1+v)-P i.1 i.2.1-D i v) -
      dF i.1 i.2.1 (0,P (h i.1) (R i.1 i.2.1+(R i.1 (i.2.1+v)-R i.1 i.2.1)) -
        P (h i.1) (R i.1 i.2.1)-D (T i) (R i.1 (i.2.1+v)-R i.1 i.2.1)))
        =o[𝓝 (0 : X i.1)] (fun v ↦ v)
    simpa only [add_sub_cancel] using he
  refine ⟨fun p x hx ↦ (hd ⟨p,⟨x,hx⟩⟩).differentiableAt, fun p x hx ↦ ?_⟩
  rw [(hd ⟨p,⟨x,hx⟩⟩).fderiv]
  exact hD ⟨p,⟨x,hx⟩⟩

/-- HPS pp.32–35: the tangent affine action has one less order of smoothness
than the ambient map and return, using only the already known regularity of
the section itself. Derivatives of F and R lose one order. Compose them with
the graph point and spatial projection, then use the smooth bilinear operation
of continuous-linear-map composition and the linear product operation. No
spatial derivative of P occurs in the action or its assumptions. -/
theorem parameter_graph_tangent_action_contDiffAt
    {X Y U V : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup U] [NormedSpace ℝ U]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (n : ℕ) (F : X × V → Y) (R : X → U) (P : U → V)
    (x : X) (Q : U →L[ℝ] V)
    (hF : ContDiffAt ℝ (↑n+1) F (x,P (R x)))
    (hR : ContDiffAt ℝ (↑n+1) R x)
    (hP : ContDiffAt ℝ (↑n) P (R x)) :
    ContDiffAt ℝ (↑n)
      (fun z : X × (U →L[ℝ] V) ↦
        (fderiv ℝ F (z.1,P (R z.1))).comp
          ((ContinuousLinearMap.id ℝ X).prod (z.2.comp (fderiv ℝ R z.1)))) (x,Q) := by
  have hRn : ContDiffAt ℝ (↑n) R x := hR.of_le (by exact le_add_of_nonneg_right zero_le_one)
  have hg : ContDiffAt ℝ (↑n) (fun z : X × (U →L[ℝ] V) ↦ (z.1,P (R z.1))) (x,Q) :=
    contDiffAt_fst.prodMk (hP.comp (x,Q) (hRn.comp (x,Q) contDiffAt_fst))
  have hDf : ContDiffAt ℝ (↑n)
      (fun z : X × (U →L[ℝ] V) ↦ fderiv ℝ F (z.1,P (R z.1))) (x,Q) :=
    hF.fderiv_right_succ.comp (x,Q) hg
  have hDr : ContDiffAt ℝ (↑n)
      (fun z : X × (U →L[ℝ] V) ↦ fderiv ℝ R z.1) (x,Q) :=
    hR.fderiv_right_succ.comp (x,Q) contDiffAt_fst
  have hnext := contDiffAt_snd.clm_comp hDr
  have hprod : ContDiffAt ℝ (↑n)
      (fun z : X × (U →L[ℝ] V) ↦
        (ContinuousLinearMap.id ℝ X).prod (z.2.comp (fderiv ℝ R z.1))) (x,Q) := by
    have hsum : ContDiffAt ℝ (↑n)
        (fun z : X × (U →L[ℝ] V) ↦ ContinuousLinearMap.inl ℝ X V +
          (ContinuousLinearMap.inr ℝ X V).comp (z.2.comp (fderiv ℝ R z.1))) (x,Q) :=
      ContDiffAt.add contDiffAt_const (ContDiffAt.clm_comp contDiffAt_const hnext)
    convert hsum using 1
    ext z v <;> simp
  exact hDf.clm_comp hprod

/-- A fibre contraction on the closed unit ball bounds the actual vertical
partial derivative at every point of the open unit ball. Fix the base variable
and apply the chain rule to the vertical affine inclusion. The closed unit
ball is a neighborhood of the interior point, so the local Lipschitz derivative
bound applies, including contraction constant zero. This is the vertical
coefficient estimate in HPS pp.32–35. -/
theorem parameter_graph_vertical_derivative_bound
    {Z V W : Type*}
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (Φ : Z × V → W) (z : Z) (p : V) (q : NNReal)
    (hΦ : DifferentiableAt ℝ Φ (z,p)) (hp : ‖p‖ < 1)
    (hlip : ∀ v w, ‖v‖ ≤ 1 → ‖w‖ ≤ 1 →
      ‖Φ (z,v)-Φ (z,w)‖ ≤ (q : ℝ)*‖v-w‖) :
    ‖(fderiv ℝ Φ (z,p)).comp (ContinuousLinearMap.inr ℝ Z V)‖ ≤ q := by
  have hd := hΦ.hasFDerivAt.comp p (hasFDerivAt_prodMk_right z p)
  apply hd.le_of_lipschitzOn (s := Metric.closedBall (0 : V) 1)
    (Metric.closedBall_mem_nhds_of_mem (by simpa [Metric.mem_ball, dist_zero_right] using hp))
  apply LipschitzOnWith.of_dist_le_mul
  intro v hv w hw
  simpa only [Function.comp_def, dist_eq_norm] using
    hlip v w (by simpa [Metric.mem_closedBall, dist_zero_right] using hv)
      (by simpa [Metric.mem_closedBall, dist_zero_right] using hw)






end HolomorphicAnosov
