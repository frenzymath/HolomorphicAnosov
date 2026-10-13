import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphHorizontalInverse
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphTaylorJetTransport
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphSlopeTransform
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphUnitSectionFixedPoint
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphDerivativeBlocks
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphVerticalEstimate

noncomputable section
namespace HolomorphicAnosov

/-- HPS pp.33–34 and 57–58: differentiability of every invariant full-preimage
unit-Lipschitz graph. The ambient derivative supplies the four block families.
The small-perturbation bound makes the rational slope action a strict
contraction on unit operator sections over all spatial anchors. Its invariant
section solves the linearized graph equation. Taylor-defect contraction
identifies that section with the actual derivative, without requiring any
continuity or invertibility of the vertical graph return. -/
theorem parameter_graph_preimage_differentiable
    {A : Type*} (X Y : A → Type*)
    [∀ p, NormedAddCommGroup (X p)] [∀ p, NormedSpace ℝ (X p)]
    [∀ p, CompleteSpace (X p)]
    [∀ p, NormedAddCommGroup (Y p)] [∀ p, NormedSpace ℝ (Y p)]
    (h : A → A) (T : ∀ p, X p ≃L[ℝ] X (h p))
    (S : ∀ p, Y p →L[ℝ] Y (h p))
    (G : ∀ p, X p × Y p → X (h p) × Y (h p))
    (hG : ∀ p, Differentiable ℝ (G p))
    (a k ε : NNReal) (ha : ∀ p, ‖(T p).symm.toContinuousLinearMap‖ ≤ a)
    (hk : ∀ p, ‖S p‖ ≤ k)
    (hsmall : 2 * (a : ℝ) * ε < 1)
    (hjet : (a : ℝ) * (k + 2 * ε) / (1 - 2 * (a : ℝ) * ε) < 1)
    (hR : ∀ p, LipschitzWith ε (fun z ↦ G p z - (T p z.1,S p z.2)))
    (s : ∀ p, Y p → X p) (hs : ∀ p, LipschitzWith 1 (s p))
    (hgraph : ∀ p y, (G p (s p y,y)).1 = s (h p) (G p (s p y,y)).2) :
    ∀ p, Differentiable ℝ (s p) := by
  classical
  let F := fun p y ↦ fderiv ℝ (G p) (s p y,y)
  let A₀ := fun p y ↦ ((ContinuousLinearMap.fst ℝ (X (h p)) (Y (h p))).comp
    (F p y)).comp (ContinuousLinearMap.inl ℝ (X p) (Y p))
  let B₀ := fun p y ↦ ((ContinuousLinearMap.fst ℝ (X (h p)) (Y (h p))).comp
    (F p y)).comp (ContinuousLinearMap.inr ℝ (X p) (Y p))
  let C₀ := fun p y ↦ ((ContinuousLinearMap.snd ℝ (X (h p)) (Y (h p))).comp
    (F p y)).comp (ContinuousLinearMap.inl ℝ (X p) (Y p))
  let D₀ := fun p y ↦ ((ContinuousLinearMap.snd ℝ (X (h p)) (Y (h p))).comp
    (F p y)).comp (ContinuousLinearMap.inr ℝ (X p) (Y p))
  have hblocks (p : A) (y : Y p) :
      ‖A₀ p y - (T p).toContinuousLinearMap‖ ≤ ε ∧ ‖B₀ p y‖ ≤ ε ∧
      ‖C₀ p y‖ ≤ ε ∧ ‖D₀ p y‖ ≤ (k : ℝ) + ε := by
    obtain ⟨hA,hB,hC,hD⟩ := parameter_graph_derivative_blocks
      (T p).toContinuousLinearMap (S p) (G p) ε (hR p) (s p y,y)
      (F p y) ((hG p (s p y,y)).hasFDerivAt)
    refine ⟨hA,hB,hC,?_⟩
    calc
      ‖D₀ p y‖ ≤ ‖D₀ p y - S p‖ + ‖S p‖ := norm_le_norm_sub_add _ _
      _ ≤ (ε : ℝ) + k := add_le_add hD (hk p)
      _ = _ := add_comm _ _
  have hden : 0 < 1 - 2 * (a : ℝ) * ε := sub_pos.mpr hsmall
  let b : NNReal := ⟨(a : ℝ) / (1 - 2 * (a : ℝ) * ε), div_nonneg a.2 hden.le⟩
  let q : NNReal := b * (k+2*ε)
  have hqeq : (q : ℝ) = (a : ℝ) * (k+2*ε) / (1-2*(a : ℝ)*ε) := by
    change (a : ℝ) / (1-2*(a : ℝ)*ε) * ((k : ℝ)+2*ε) = _
    ring
  have hq : q < 1 := by exact_mod_cast hqeq ▸ hjet
  have hΦexists (i : Sigma Y) :
      ∃ Φ : ParameterGraphUnitHom (Y (h i.1)) (X (h i.1)) →
          ParameterGraphUnitHom (Y i.1) (X i.1),
        LipschitzWith q Φ ∧ ∀ P,
          (A₀ i.1 i.2 - P.1.comp (C₀ i.1 i.2)).comp (Φ P).1 =
            P.1.comp (D₀ i.1 i.2) - B₀ i.1 i.2 := by
    obtain ⟨hA,hB,hC,hD⟩ := hblocks i.1 i.2
    obtain ⟨q',hq',_,Φs,Φt,_,hΦt,_,heq⟩ := parameter_graph_slope_transform
      (T i.1) (A₀ i.1 i.2) (B₀ i.1 i.2) (C₀ i.1 i.2) (D₀ i.1 i.2)
      a k ε (ha i.1) hA hB hC hD hsmall hjet
    have hqq : q' = q := NNReal.coe_injective (hq'.trans hqeq.symm)
    exact ⟨Φt,hqq ▸ hΦt,fun P ↦ (heq P).1⟩
  choose Φ hΦ hΦeq using hΦexists
  let R : Sigma Y → Sigma Y := fun i ↦ ⟨h i.1,(G i.1 (s i.1 i.2,i.2)).2⟩
  obtain ⟨P,hPfix,_,_⟩ := parameter_graph_unit_section_fixed_point
    (fun i : Sigma Y ↦ Y i.1 →L[ℝ] X i.1) R Φ q hq hΦ
  have hJexists (p : A) (y : Y p) : ∃ J : X p ≃L[ℝ] X (h p),
      J.toContinuousLinearMap = A₀ p y - (P (R ⟨p,y⟩)).1.comp (C₀ p y) ∧
        ‖J.symm.toContinuousLinearMap‖ ≤ b := by
    obtain ⟨hA,hB,hC,_⟩ := hblocks p y
    exact (parameter_graph_horizontal_inverse (T p) (A₀ p y) (B₀ p y) (C₀ p y)
      a ε (ha p) hsmall hA hB hC).2 (P (R ⟨p,y⟩)).1 (P (R ⟨p,y⟩)).2
  choose J hJeq hJnorm using hJexists
  have hK (p : A) : LipschitzWith (k+ε) (fun y ↦ (G p (s p y,y)).2) := by
    apply lipschitzWith_iff_norm_sub_le.mpr
    intro y z
    have hsz : ‖s p y-s p z‖ ≤ ‖y-z‖ := by simpa using (hs p).norm_sub_le y z
    have hv := parameter_graph_vertical_estimate (T p).toContinuousLinearMap
      (S p) (G p) k ε (hk p) (hR p) (s p y) (s p z) y z
    simpa only [max_eq_right hsz, NNReal.coe_add, add_mul] using hv
  have hbc : (b : ℝ) * (k+ε : NNReal) < 1 := by
    apply lt_of_le_of_lt _ (show (q : ℝ) < 1 from hq)
    dsimp [q]
    gcongr
    nlinarith [ε.2]
  have hderiv := parameter_graph_preimage_hasFDerivAt_of_invariant_slope X Y h G s hs hgraph
    F (fun p y ↦ (hG p (s p y,y)).hasFDerivAt)
    (fun p y ↦ (P ⟨p,y⟩).1) (fun p y ↦ (P ⟨p,y⟩).2) J b (k+ε)
    hJnorm hbc hK
    (by
      intro p y x
      have he := DFunLike.congr_fun (hJeq p y) x
      simpa [A₀,C₀,R] using he)
    (by
      intro p y v
      have he := hΦeq ⟨p,y⟩ (P (R ⟨p,y⟩))
      rw [hPfix ⟨p,y⟩, ← hJeq p y] at he
      have hv := DFunLike.congr_fun he v
      simpa [B₀,D₀,R] using hv)
  exact fun p y ↦ (hderiv p y).differentiableAt


/-- HPS pp.33–34 and 55–56: differentiability of an invariant image graph.
The derivative blocks define a contracting image slope action. Construct its
invariant unit section over the actual horizontal graph homeomorphism, then
use the inverse-return Taylor-defect estimate to identify it as the derivative.
Only the horizontal map is inverted; the vertical block may be singular. -/
theorem parameter_graph_image_differentiable
    {A : Type*} (X Y : A → Type*)
    [∀ p, NormedAddCommGroup (X p)] [∀ p, NormedSpace ℝ (X p)]
    [∀ p, CompleteSpace (X p)]
    [∀ p, NormedAddCommGroup (Y p)] [∀ p, NormedSpace ℝ (Y p)]
    [∀ p, CompleteSpace (Y p)]
    (h : A ≃ A) (T : ∀ p, X p ≃L[ℝ] X (h p))
    (S : ∀ p, Y p →L[ℝ] Y (h p))
    (G : ∀ p, X p × Y p → X (h p) × Y (h p))
    (hG : ∀ p, Differentiable ℝ (G p))
    (a k ε c : NNReal) (ha : ∀ p, ‖(T p).symm.toContinuousLinearMap‖ ≤ a)
    (hk : ∀ p, ‖S p‖ ≤ k)
    (hsmall : 2 * (a : ℝ) * ε < 1)
    (hjet : (a : ℝ) * (k + 2 * ε) / (1 - 2 * (a : ℝ) * ε) < 1)
    (hreturn : ((k : ℝ) + 2 * ε) * c < 1)
    (hR : ∀ p, LipschitzWith ε (fun z ↦ G p z - (T p z.1,S p z.2)))
    (s : ∀ p, X p → Y p) (hs : ∀ p, LipschitzWith 1 (s p))
    (H : ∀ p, X p ≃ₜ X (h p))
    (hfirst : ∀ p x, (G p (x,s p x)).1 = H p x)
    (hsecond : ∀ p x, (G p (x,s p x)).2 = s (h p) (H p x))
    (hH : ∀ p, LipschitzWith c ((H p).symm : X (h p) → X p)) :
    ∀ p, Differentiable ℝ (s p) := by
  classical
  let F := fun p x ↦ fderiv ℝ (G p) (x,s p x)
  let A₀ := fun p x ↦ ((ContinuousLinearMap.fst ℝ (X (h p)) (Y (h p))).comp
    (F p x)).comp (ContinuousLinearMap.inl ℝ (X p) (Y p))
  let B₀ := fun p x ↦ ((ContinuousLinearMap.fst ℝ (X (h p)) (Y (h p))).comp
    (F p x)).comp (ContinuousLinearMap.inr ℝ (X p) (Y p))
  let C₀ := fun p x ↦ ((ContinuousLinearMap.snd ℝ (X (h p)) (Y (h p))).comp
    (F p x)).comp (ContinuousLinearMap.inl ℝ (X p) (Y p))
  let D₀ := fun p x ↦ ((ContinuousLinearMap.snd ℝ (X (h p)) (Y (h p))).comp
    (F p x)).comp (ContinuousLinearMap.inr ℝ (X p) (Y p))
  have hblocks (p : A) (x : X p) :
      ‖A₀ p x - (T p).toContinuousLinearMap‖ ≤ ε ∧ ‖B₀ p x‖ ≤ ε ∧
      ‖C₀ p x‖ ≤ ε ∧ ‖D₀ p x‖ ≤ (k : ℝ) + ε := by
    obtain ⟨hA,hB,hC,hD⟩ := parameter_graph_derivative_blocks
      (T p).toContinuousLinearMap (S p) (G p) ε (hR p) (x,s p x)
      (F p x) ((hG p (x,s p x)).hasFDerivAt)
    refine ⟨hA,hB,hC,?_⟩
    calc
      ‖D₀ p x‖ ≤ ‖D₀ p x - S p‖ + ‖S p‖ := norm_le_norm_sub_add _ _
      _ ≤ (ε : ℝ) + k := add_le_add hD (hk p)
      _ = _ := add_comm _ _
  have hden : 0 < 1 - 2 * (a : ℝ) * ε := sub_pos.mpr hsmall
  let b : NNReal := ⟨(a : ℝ) / (1 - 2 * (a : ℝ) * ε), div_nonneg a.2 hden.le⟩
  let q : NNReal := b * (k+2*ε)
  have hqeq : (q : ℝ) = (a : ℝ) * (k+2*ε) / (1-2*(a : ℝ)*ε) := by
    change (a : ℝ) / (1-2*(a : ℝ)*ε) * ((k : ℝ)+2*ε) = _
    ring
  have hq : q < 1 := by exact_mod_cast hqeq ▸ hjet
  have hΦexists (i : Sigma X) :
      ∃ Φ : ParameterGraphUnitHom (X i.1) (Y i.1) →
          ParameterGraphUnitHom (X (h i.1)) (Y (h i.1)),
        LipschitzWith q Φ ∧ ∀ P,
          (Φ P).1.comp (A₀ i.1 i.2 + (B₀ i.1 i.2).comp P.1) =
            C₀ i.1 i.2 + (D₀ i.1 i.2).comp P.1 := by
    obtain ⟨hA,hB,hC,hD⟩ := hblocks i.1 i.2
    obtain ⟨q',hq',_,Φs,Φt,hΦs,_,heq,_⟩ := parameter_graph_slope_transform
      (T i.1) (A₀ i.1 i.2) (B₀ i.1 i.2) (C₀ i.1 i.2) (D₀ i.1 i.2)
      a k ε (ha i.1) hA hB hC hD hsmall hjet
    have hqq : q' = q := NNReal.coe_injective (hq'.trans hqeq.symm)
    exact ⟨Φs,hqq ▸ hΦs,fun P ↦ (heq P).1⟩
  choose Φ hΦ hΦeq using hΦexists
  let R : Sigma X ≃ Sigma X := Equiv.sigmaCongr h (fun p ↦ (H p).toEquiv)
  obtain ⟨P,hPfix,_⟩ := parameter_graph_unit_section_fixed_point_forward
    (fun i : Sigma X ↦ X i.1 →L[ℝ] Y i.1) R Φ q hq hΦ
  have hderiv := parameter_graph_image_hasFDerivAt_of_invariant_slope X Y h G s hs H
    hfirst hsecond F (fun p x ↦ (hG p (x,s p x)).hasFDerivAt)
    (fun p x ↦ (P ⟨p,x⟩).1) (fun p x ↦ (P ⟨p,x⟩).2) (k+2*ε) c
    (by simpa using hreturn) hH
    (by
      intro p x v
      have he := hΦeq ⟨p,x⟩ (P ⟨p,x⟩)
      rw [hPfix ⟨p,x⟩] at he
      have hv := DFunLike.congr_fun he v
      change (P ⟨h p,H p x⟩).1 ((A₀ p x + (B₀ p x).comp (P ⟨p,x⟩).1) v) =
        (C₀ p x + (D₀ p x).comp (P ⟨p,x⟩).1) v at hv
      have hsplit : F p x (v,(P ⟨p,x⟩).1 v) =
          F p x (v,0) + F p x (0,(P ⟨p,x⟩).1 v) := by
        rw [← map_add]; congr 1; simp
      simpa [A₀,B₀,C₀,D₀,R,hsplit] using hv)
    (by
      intro p x
      have hB := (hblocks p x).2.1
      have hD := (hblocks p x).2.2.2
      have he : ((ContinuousLinearMap.snd ℝ (X (h p)) (Y (h p))).comp (F p x) -
          (P ⟨h p,H p x⟩).1.comp
            ((ContinuousLinearMap.fst ℝ (X (h p)) (Y (h p))).comp (F p x))).comp
          (ContinuousLinearMap.inr ℝ (X p) (Y p)) =
          D₀ p x - (P ⟨h p,H p x⟩).1.comp (B₀ p x) := by ext v; rfl
      rw [he]
      calc
        _ ≤ ‖D₀ p x‖ + ‖(P ⟨h p,H p x⟩).1.comp (B₀ p x)‖ := norm_sub_le _ _
        _ ≤ ((k : ℝ)+ε) + ‖(P ⟨h p,H p x⟩).1‖ * ‖B₀ p x‖ :=
          add_le_add hD ((P ⟨h p,H p x⟩).1.opNorm_comp_le _)
        _ ≤ (k+2*ε : NNReal) := by
          have hp := (P ⟨h p,H p x⟩).2
          change _ ≤ (k : ℝ)+2*ε
          nlinarith [norm_nonneg (P ⟨h p,H p x⟩).1, norm_nonneg (B₀ p x)])
  exact fun p x ↦ (hderiv p x).differentiableAt

end HolomorphicAnosov
