import HolomorphicAnosov.Analysis.Calculus.BoundedLipschitzJetsSupport.BoundedRepresentativeStructure
import HolomorphicAnosov.Analysis.Calculus.BoundedLipschitzJetsSupport.LittleORepresentativeStructure
import HolomorphicAnosov.Analysis.Calculus.BoundedLipschitzJetsSupport.NormCore
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphJetTransport
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphJetIdentification
import Mathlib.Analysis.Normed.Operator.Asymptotics

noncomputable section
open Filter Asymptotics
open scoped Topology

namespace HolomorphicAnosov
open BoundedLipschitzJets

/-- A first-order Taylor error does not change the graph-jet contraction estimate (HPS, pp.33–34, 55–58). -/
theorem parameter_graph_taylor_jet_transport
    {X Y U V : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup U] [NormedSpace ℝ U]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (Q : BoundedRepresentative X Y) (P : BoundedRepresentative U V)
    (R : X → U) (hR : ContinuousAt R 0) (hR0 : R 0 = 0)
    (L : V →L[ℝ] Y) (b c : NNReal) (hL : ‖L‖ ≤ b)
    (hbound : ∀ᶠ x in 𝓝 (0 : X), ‖R x‖ ≤ (c : ℝ) * ‖x‖)
    (herror : (fun x ↦ (Q : X → Y) x - L ((P : U → V) (R x)))
      =o[𝓝 (0 : X)] (fun x ↦ x)) :
    ‖jetClass X Y Q‖ ≤ (b : ℝ) * c * ‖jetClass U V P‖ := by
  obtain ⟨C, hC, hPC⟩ := P.property.2
  have hPC' : ∀ᶠ u in 𝓝 (0 : U), ‖(P : U → V) u‖ ≤ C * ‖u‖ := by
    rw [← nhdsNE_sup_pure (0 : U), Filter.eventually_sup]
    refine ⟨hPC, ?_⟩
    simp only [Filter.eventually_pure, P.property.1, norm_zero, mul_zero, le_refl]
  have hR' : Tendsto R (𝓝 0) (𝓝 0) := by simpa only [hR0] using hR.tendsto
  have hnorm (v : V) : ‖L v‖ ≤ (b : ℝ) * ‖v‖ :=
    (L.le_opNorm v).trans (mul_le_mul_of_nonneg_right hL (norm_nonneg _))
  let J : BoundedRepresentative X Y := ⟨fun x ↦ L ((P : U → V) (R x)), by
    refine ⟨by simp only [hR0, P.property.1, map_zero], (b : ℝ) * C * c,
      by positivity, ?_⟩
    filter_upwards [hR'.eventually hPC' |>.filter_mono nhdsWithin_le_nhds,
      hbound.filter_mono nhdsWithin_le_nhds] with x hx hxR
    calc
      ‖L ((P : U → V) (R x))‖ ≤ (b : ℝ) * ‖(P : U → V) (R x)‖ := hnorm _
      _ ≤ (b : ℝ) * (C * ‖R x‖) := mul_le_mul_of_nonneg_left hx b.2
      _ ≤ (b : ℝ) * (C * ((c : ℝ) * ‖x‖)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hxR hC) b.2
      _ = ((b : ℝ) * C * c) * ‖x‖ := by ring⟩
  have heq : jetClass X Y Q = jetClass X Y J := by
    apply (jetClass_eq_iff X Y Q J).mpr
    intro ε hε
    exact (herror.def hε).filter_mono nhdsWithin_le_nhds
  rw [heq]
  exact parameter_graph_jet_transport J P R hR hR0 b c hbound
    (Eventually.of_forall (fun x ↦ hnorm _))


/-- A bounded invariant linear field equals the derivative of the corresponding Lipschitz graphs (HPS, pp.33–34). -/
theorem parameter_graph_invariant_taylor_derivative
    {I : Type*} (X Y : I → Type*)
    [∀ i, NormedAddCommGroup (X i)] [∀ i, NormedSpace ℝ (X i)]
    [∀ i, NormedAddCommGroup (Y i)] [∀ i, NormedSpace ℝ (Y i)]
    (R : I → I) (s : ∀ i, X i → Y i) (x : ∀ i, X i)
    (hs : ∀ i, LipschitzWith 1 (s i))
    (P : ∀ i, X i →L[ℝ] Y i) (hP : ∀ i, ‖P i‖ ≤ 1)
    (r : ∀ i, X i → X (R i))
    (hr : ∀ i, ContinuousAt (r i) 0) (hr0 : ∀ i, r i 0 = 0)
    (L : ∀ i, Y (R i) →L[ℝ] Y i) (b c : NNReal)
    (hL : ∀ i, ‖L i‖ ≤ b) (hq : (b : ℝ) * c < 1)
    (hbound : ∀ i, ∀ᶠ v in 𝓝 (0 : X i), ‖r i v‖ ≤ (c : ℝ) * ‖v‖)
    (herror : ∀ i,
      (fun v ↦ (s i (x i + v) - s i (x i) - P i v) -
        L i (s (R i) (x (R i) + r i v) - s (R i) (x (R i)) - P (R i) (r i v)))
        =o[𝓝 (0 : X i)] (fun v ↦ v)) :
    ∀ i, HasFDerivAt (s i) (P i) (x i) := by
  have hsbound (i : I) (v : X i) : ‖s i (x i + v) - s i (x i)‖ ≤ ‖v‖ := by
    simpa only [NNReal.coe_one, one_mul, add_sub_cancel_left] using
      (hs i).norm_sub_le (x i + v) (x i)
  let Q : ∀ i, BoundedRepresentative (X i) (Y i) := fun i ↦
    ⟨fun v ↦ s i (x i + v) - s i (x i), by
      refine ⟨by simp, 1, zero_le_one, ?_⟩
      exact Eventually.of_forall (fun v ↦ by simpa using hsbound i v)⟩
  let D : ∀ i, BoundedRepresentative (X i) (Y i) := fun i ↦
    Q i - linearRepresentative (X i) (Y i) (P i)
  have hD (i : I) : ‖jetClass (X i) (Y i) (D i)‖ ≤ 2 := by
    change sInf (slopeBounds (X i) (Y i) (D i)) ≤ 2
    apply csInf_le ⟨0, fun _ h ↦ h.1⟩
    refine ⟨by norm_num, Eventually.of_forall (fun v ↦ ?_)⟩
    change ‖s i (x i + v) - s i (x i) - P i v‖ ≤ 2 * ‖v‖
    calc
      _ ≤ ‖s i (x i + v) - s i (x i)‖ + ‖P i v‖ := norm_sub_le _ _
      _ ≤ ‖v‖ + 1 * ‖v‖ := add_le_add (hsbound i v)
        (((P i).le_opNorm v).trans (mul_le_mul_of_nonneg_right (hP i) (norm_nonneg _)))
      _ = _ := by ring
  apply parameter_graph_jet_identification X Y R s x P Q (fun _ _ ↦ rfl)
    (b * c) (by simpa using hq) 2 hD
  intro i
  change ‖jetClass (X i) (Y i) (D i)‖ ≤
    ((b * c : NNReal) : ℝ) * ‖jetClass (X (R i)) (Y (R i)) (D (R i))‖
  simpa only [NNReal.coe_mul] using
    parameter_graph_taylor_jet_transport (D i) (D (R i)) (r i) (hr i) (hr0 i)
      (L i) b c (hL i) (hbound i) (herror i)


/-- Taylor's first-order remainder pulled back along a centered Lipschitz displacement. -/
lemma parameter_graph_lipschitz_taylor
    {X Y V : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (G : X → Y) (F : X →L[ℝ] Y) (z : X) (hF : HasFDerivAt G F z)
    (u : V → X) (hu0 : u 0 = 0) (c : NNReal) (hu : LipschitzWith c u) :
    (fun v ↦ G (z + u v) - G z - F (u v)) =o[𝓝 (0 : V)] (fun v ↦ v) := by
  have ht : Tendsto u (𝓝 0) (𝓝 0) := by
    simpa only [hu0] using hu.continuous.tendsto 0
  have hb : u =O[𝓝 (0 : V)] (fun v ↦ v) := by
    apply IsBigO.of_bound c
    exact Eventually.of_forall (fun v ↦ by simpa only [hu0, sub_zero] using hu.norm_sub_le v 0)
  exact ((hasFDerivAt_iff_isLittleO_nhds_zero.mp hF).comp_tendsto ht).trans_isBigO hb

/-- The derivative defect of a full-preimage graph satisfies the corresponding Taylor equation (HPS, pp.57–58). -/
theorem parameter_graph_preimage_taylor_defect
    {X Y U V : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup U] [NormedSpace ℝ U]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (G : X × Y → U × V) (s : Y → X) (t : V → U)
    (hs : LipschitzWith 1 s)
    (hgraph : ∀ y, (G (s y, y)).1 = t (G (s y, y)).2)
    (y : Y) (F : X × Y →L[ℝ] U × V) (hF : HasFDerivAt G F (s y,y))
    (P : Y →L[ℝ] X) (Q : V →L[ℝ] U) (J : X ≃L[ℝ] U)
    (hJ : ∀ x, J x = (F (x,0)).1 - Q (F (x,0)).2)
    (hP : ∀ v, J (P v) = Q (F (0,v)).2 - (F (0,v)).1) :
    (fun v ↦ (s (y+v) - s y - P v) -
      J.symm (t (G (s (y+v),y+v)).2 - t (G (s y,y)).2 -
        Q ((G (s (y+v),y+v)).2 - (G (s y,y)).2)))
      =o[𝓝 (0 : Y)] (fun v ↦ v) := by
  let u : Y → X × Y := fun v ↦ (s (y+v)-s y,v)
  have hu0 : u 0 = 0 := by simp [u]
  have hu : LipschitzWith 1 u := by
    apply LipschitzWith.of_dist_le_mul
    intro v w
    simp only [u, Prod.dist_eq, NNReal.coe_one, one_mul]
    apply max_le
    · simpa only [dist_sub_right, dist_add_left, NNReal.coe_one, one_mul] using
        hs.dist_le_mul (y+v) (y+w)
    · exact le_rfl
  let rem : Y → U × V := fun v ↦ G ((s y,y) + u v) - G (s y,y) - F (u v)
  have hrem : rem =o[𝓝 (0 : Y)] (fun v ↦ v) :=
    parameter_graph_lipschitz_taylor G F (s y,y) hF u hu0 1 hu
  let K : U × V →L[ℝ] X := J.symm.toContinuousLinearMap.comp
    (Q.comp (ContinuousLinearMap.snd ℝ U V) - ContinuousLinearMap.fst ℝ U V)
  have he : ∀ v,
      (s (y+v) - s y - P v) -
      J.symm (t (G (s (y+v),y+v)).2 - t (G (s y,y)).2 -
        Q ((G (s (y+v),y+v)).2 - (G (s y,y)).2)) = K (rem v) := by
    intro v
    apply J.injective
    rw [map_sub, J.apply_symm_apply]
    change J (s (y+v) - s y - P v) -
      (t (G (s (y+v),y+v)).2 - t (G (s y,y)).2 -
        Q ((G (s (y+v),y+v)).2 - (G (s y,y)).2)) =
      J (J.symm (Q (rem v).2 - (rem v).1))
    rw [J.apply_symm_apply, map_sub, hJ, hP]
    have hsplit : F (s (y+v)-s y,v) = F (s (y+v)-s y,0) + F (0,v) := by
      rw [← F.map_add]
      congr 1
      simp
    have hpoint : (s y,y) + u v = (s (y+v),y+v) := by
      ext <;> simp [u]
    simp only [rem, hpoint, u, Prod.fst_sub, Prod.snd_sub, hsplit,
      Prod.fst_add, Prod.snd_add, map_sub, map_add, ← hgraph]
    abel
  exact ((K.isBigO_comp rem (𝓝 0)).trans_isLittleO hrem).congr_left (fun v ↦ (he v).symm)


/-- The derivative defect of an image graph satisfies the corresponding Taylor equation (HPS, pp.55–56). -/
theorem parameter_graph_image_taylor_defect
    {X Y U V : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup U] [NormedSpace ℝ U]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (G : X × Y → U × V) (s : X → Y) (t : U → V)
    (hs : LipschitzWith 1 s) (H : U → X) (c : NNReal) (hH : LipschitzWith c H)
    (hfirst : ∀ u, (G (H u,s (H u))).1 = u)
    (hsecond : ∀ u, (G (H u,s (H u))).2 = t u)
    (u : U) (F : X × Y →L[ℝ] U × V)
    (hF : HasFDerivAt G F (H u,s (H u)))
    (P : X →L[ℝ] Y) (Q : U →L[ℝ] V)
    (hPQ : ∀ x, Q (F (x,P x)).1 = (F (x,P x)).2) :
    (fun v ↦ (t (u+v) - t u - Q v) -
      ((F (0,s (H (u+v)) - s (H u) - P (H (u+v)-H u))).2 -
        Q (F (0,s (H (u+v)) - s (H u) - P (H (u+v)-H u))).1))
      =o[𝓝 (0 : U)] (fun v ↦ v) := by
  let d : U → X × Y := fun v ↦ (H (u+v)-H u, s (H (u+v))-s (H u))
  have hd0 : d 0 = 0 := by simp [d]
  have hd : LipschitzWith c d := by
    apply LipschitzWith.of_dist_le_mul
    intro v w
    simp only [d, Prod.dist_eq, dist_sub_right]
    apply max_le
    · simpa only [dist_add_left] using hH.dist_le_mul (u+v) (u+w)
    · have h := (hs.dist_le_mul (H (u+v)) (H (u+w))).trans
        (by simpa only [NNReal.coe_one, one_mul, dist_add_left] using
          hH.dist_le_mul (u+v) (u+w))
      simpa only [NNReal.coe_one, one_mul] using h
  let rem : U → U × V := fun v ↦
    G ((H u,s (H u)) + d v) - G (H u,s (H u)) - F (d v)
  have hrem : rem =o[𝓝 (0 : U)] (fun v ↦ v) :=
    parameter_graph_lipschitz_taylor G F (H u,s (H u)) hF d hd0 c hd
  let K : U × V →L[ℝ] V :=
    ContinuousLinearMap.snd ℝ U V - Q.comp (ContinuousLinearMap.fst ℝ U V)
  have he : ∀ v,
      (t (u+v) - t u - Q v) -
      ((F (0,s (H (u+v)) - s (H u) - P (H (u+v)-H u))).2 -
        Q (F (0,s (H (u+v)) - s (H u) - P (H (u+v)-H u))).1) = K (rem v) := by
    intro v
    have hpoint : (H u,s (H u)) + d v = (H (u+v),s (H (u+v))) := by
      ext <;> simp [d]
    have hsplit : F (d v) =
        F (H (u+v)-H u, P (H (u+v)-H u)) +
        F (0,s (H (u+v)) - s (H u) - P (H (u+v)-H u)) := by
      rw [← F.map_add]
      congr 1
      ext <;> simp [d]
    change _ = (rem v).2 - Q (rem v).1
    have hpq := hPQ (H (u+v)-H u)
    simp only [map_sub] at hpq
    simp only [rem, hpoint, Prod.fst_sub, Prod.snd_sub, hfirst, hsecond,
      hsplit, Prod.fst_add, Prod.snd_add, map_sub, map_add]
    rw [hpq]
    abel
  exact ((K.isBigO_comp rem (𝓝 0)).trans_isLittleO hrem).congr_left (fun v ↦ (he v).symm)


/-- An invariant bounded slope field on a full-preimage graph is its actual fibre derivative (HPS, pp.33–34, 57–58). -/
theorem parameter_graph_preimage_hasFDerivAt_of_invariant_slope
    {A : Type*} (X Y : A → Type*)
    [∀ p, NormedAddCommGroup (X p)] [∀ p, NormedSpace ℝ (X p)]
    [∀ p, NormedAddCommGroup (Y p)] [∀ p, NormedSpace ℝ (Y p)]
    (h : A → A) (G : ∀ p, X p × Y p → X (h p) × Y (h p))
    (s : ∀ p, Y p → X p) (hs : ∀ p, LipschitzWith 1 (s p))
    (hgraph : ∀ p y, (G p (s p y,y)).1 = s (h p) (G p (s p y,y)).2)
    (F : ∀ p, Y p → (X p × Y p →L[ℝ] X (h p) × Y (h p)))
    (hF : ∀ p y, HasFDerivAt (G p) (F p y) (s p y,y))
    (P : ∀ p, Y p → (Y p →L[ℝ] X p)) (hP : ∀ p y, ‖P p y‖ ≤ 1)
    (J : ∀ p, Y p → (X p ≃L[ℝ] X (h p)))
    (b c : NNReal) (hJnorm : ∀ p y, ‖(J p y).symm.toContinuousLinearMap‖ ≤ b)
    (hq : (b : ℝ) * c < 1)
    (hK : ∀ p, LipschitzWith c (fun y ↦ (G p (s p y,y)).2))
    (hJ : ∀ p y x, J p y x = (F p y (x,0)).1 -
      P (h p) (G p (s p y,y)).2 (F p y (x,0)).2)
    (hinv : ∀ p y v, J p y (P p y v) =
      P (h p) (G p (s p y,y)).2 (F p y (0,v)).2 - (F p y (0,v)).1) :
    ∀ p y, HasFDerivAt (s p) (P p y) y := by
  let R : Sigma Y → Sigma Y := fun i ↦ ⟨h i.1, (G i.1 (s i.1 i.2,i.2)).2⟩
  let r : ∀ i : Sigma Y, Y i.1 → Y (R i).1 := fun i v ↦
    (G i.1 (s i.1 (i.2+v),i.2+v)).2 - (G i.1 (s i.1 i.2,i.2)).2
  have hr (i : Sigma Y) : LipschitzWith c (r i) := by
    apply LipschitzWith.of_dist_le_mul
    intro v w
    simpa only [r, dist_sub_right, dist_add_left] using
      (hK i.1).dist_le_mul (i.2+v) (i.2+w)
  have h := parameter_graph_invariant_taylor_derivative
    (fun i : Sigma Y ↦ Y i.1) (fun i : Sigma Y ↦ X i.1) R
    (fun i ↦ s i.1) (fun i ↦ i.2) (fun i ↦ hs i.1)
    (fun i ↦ P i.1 i.2) (fun i ↦ hP i.1 i.2) r
    (fun i ↦ (hr i).continuous.continuousAt) (by intro i; simp [r])
    (fun i ↦ (J i.1 i.2).symm.toContinuousLinearMap) b c
    (fun i ↦ hJnorm i.1 i.2) hq
    (fun i ↦ Eventually.of_forall (fun v ↦ by
      simpa only [r, add_zero, sub_self, sub_zero] using (hr i).norm_sub_le v 0))
    (by
      intro i
      have ht := parameter_graph_preimage_taylor_defect (G i.1) (s i.1) (s (h i.1))
        (hs i.1) (hgraph i.1) i.2 (F i.1 i.2) (hF i.1 i.2)
        (P i.1 i.2) (P (h i.1) (G i.1 (s i.1 i.2,i.2)).2)
        (J i.1 i.2) (hJ i.1 i.2) (hinv i.1 i.2)
      simpa only [R, r, add_sub_cancel, ContinuousLinearEquiv.coe_coe] using ht)
  exact fun p y ↦ h ⟨p,y⟩


/-- An invariant bounded slope field on an image graph is its actual fibre derivative (HPS, pp.33–34, 55–56). -/
theorem parameter_graph_image_hasFDerivAt_of_invariant_slope
    {A : Type*} (X Y : A → Type*)
    [∀ p, NormedAddCommGroup (X p)] [∀ p, NormedSpace ℝ (X p)]
    [∀ p, NormedAddCommGroup (Y p)] [∀ p, NormedSpace ℝ (Y p)]
    (h : A ≃ A) (G : ∀ p, X p × Y p → X (h p) × Y (h p))
    (s : ∀ p, X p → Y p) (hs : ∀ p, LipschitzWith 1 (s p))
    (H : ∀ p, X p ≃ₜ X (h p))
    (hfirst : ∀ p x, (G p (x,s p x)).1 = H p x)
    (hsecond : ∀ p x, (G p (x,s p x)).2 = s (h p) (H p x))
    (F : ∀ p, X p → (X p × Y p →L[ℝ] X (h p) × Y (h p)))
    (hF : ∀ p x, HasFDerivAt (G p) (F p x) (x,s p x))
    (P : ∀ p, X p → (X p →L[ℝ] Y p)) (hP : ∀ p x, ‖P p x‖ ≤ 1)
    (b c : NNReal) (hq : (b : ℝ) * c < 1)
    (hH : ∀ p, LipschitzWith c ((H p).symm : X (h p) → X p))
    (hinv : ∀ p x v, P (h p) (H p x) (F p x (v,P p x v)).1 =
      (F p x (v,P p x v)).2)
    (hL : ∀ p x,
      ‖((ContinuousLinearMap.snd ℝ (X (h p)) (Y (h p))).comp (F p x) -
        (P (h p) (H p x)).comp
          ((ContinuousLinearMap.fst ℝ (X (h p)) (Y (h p))).comp (F p x))).comp
        (ContinuousLinearMap.inr ℝ (X p) (Y p))‖ ≤ b) :
    ∀ p x, HasFDerivAt (s p) (P p x) x := by
  let T : Sigma X ≃ Sigma X := Equiv.sigmaCongr h (fun p ↦ (H p).toEquiv)
  have hsbound (i : Sigma X) (v : X i.1) :
      ‖s i.1 (i.2+v) - s i.1 i.2‖ ≤ ‖v‖ := by
    simpa only [NNReal.coe_one, one_mul, add_sub_cancel_left] using
      (hs i.1).norm_sub_le (i.2+v) i.2
  let Q : ∀ i : Sigma X, BoundedRepresentative (X i.1) (Y i.1) := fun i ↦
    ⟨fun v ↦ s i.1 (i.2+v) - s i.1 i.2, by
      refine ⟨by simp, 1, zero_le_one, ?_⟩
      exact Eventually.of_forall (fun v ↦ by simpa using hsbound i v)⟩
  let D : ∀ i : Sigma X, BoundedRepresentative (X i.1) (Y i.1) := fun i ↦
    Q i - linearRepresentative (X i.1) (Y i.1) (P i.1 i.2)
  have hD (i : Sigma X) : ‖jetClass (X i.1) (Y i.1) (D i)‖ ≤ 2 := by
    change sInf (slopeBounds (X i.1) (Y i.1) (D i)) ≤ 2
    apply csInf_le ⟨0, fun _ h ↦ h.1⟩
    refine ⟨by norm_num, Eventually.of_forall (fun v ↦ ?_)⟩
    change ‖s i.1 (i.2+v) - s i.1 i.2 - P i.1 i.2 v‖ ≤ 2 * ‖v‖
    calc
      _ ≤ ‖s i.1 (i.2+v) - s i.1 i.2‖ + ‖P i.1 i.2 v‖ := norm_sub_le _ _
      _ ≤ ‖v‖ + 1 * ‖v‖ := add_le_add (hsbound i v)
        (((P i.1 i.2).le_opNorm v).trans
          (mul_le_mul_of_nonneg_right (hP i.1 i.2) (norm_nonneg _)))
      _ = _ := by ring
  have hstep (i : Sigma X) : ‖jetClass (X i.1) (Y i.1) (D i)‖ ≤
      ((b * c : NNReal) : ℝ) *
        ‖jetClass (X (T.symm i).1) (Y (T.symm i).1) (D (T.symm i))‖ := by
    obtain ⟨⟨p,x⟩,rfl⟩ := T.surjective i
    rw [T.symm_apply_apply]
    let r : X (h p) → X p := fun v ↦ (H p).symm (H p x + v) - x
    have hr0 : r 0 = 0 := by simp [r]
    have hr : LipschitzWith c r := by
      apply LipschitzWith.of_dist_le_mul
      intro v w
      simpa only [r, dist_sub_right, dist_add_left] using
        (hH p).dist_le_mul (H p x+v) (H p x+w)
    let L : Y p →L[ℝ] Y (h p) :=
      ((ContinuousLinearMap.snd ℝ (X (h p)) (Y (h p))).comp (F p x) -
        (P (h p) (H p x)).comp
          ((ContinuousLinearMap.fst ℝ (X (h p)) (Y (h p))).comp (F p x))).comp
        (ContinuousLinearMap.inr ℝ (X p) (Y p))
    have herr :
        (fun v ↦ (D ⟨h p,H p x⟩ : X (h p) → Y (h p)) v -
          L ((D ⟨p,x⟩ : X p → Y p) (r v))) =o[𝓝 0] (fun v ↦ v) := by
      have ht := parameter_graph_image_taylor_defect (G p) (s p) (s (h p)) (hs p)
        (H p).symm c (hH p)
        (fun u ↦ by rw [hfirst, (H p).apply_symm_apply])
        (fun u ↦ by rw [hsecond, (H p).apply_symm_apply])
        (H p x) (F p x) (by simpa only [(H p).symm_apply_apply] using hF p x)
        (P p x) (P (h p) (H p x)) (hinv p x)
      simpa [D, Q, linearRepresentative, r, L] using ht
    have ht := parameter_graph_taylor_jet_transport (D ⟨h p,H p x⟩) (D ⟨p,x⟩)
      r hr.continuous.continuousAt hr0 L b c (hL p x)
      (Eventually.of_forall (fun v ↦ by simpa [hr0] using hr.norm_sub_le v 0)) herr
    change ‖jetClass (X (h p)) (Y (h p)) (D ⟨h p,H p x⟩)‖ ≤
      ((b*c : NNReal) : ℝ) * ‖jetClass (X p) (Y p) (D ⟨p,x⟩)‖
    simpa only [NNReal.coe_mul] using ht
  have hd := parameter_graph_jet_identification
    (fun i : Sigma X ↦ X i.1) (fun i : Sigma X ↦ Y i.1) T.symm
    (fun i ↦ s i.1) (fun i ↦ i.2) (fun i ↦ P i.1 i.2) Q (fun _ _ ↦ rfl)
    (b*c) (by simpa using hq) 2 hD hstep
  exact fun p x ↦ hd ⟨p,x⟩

end HolomorphicAnosov
