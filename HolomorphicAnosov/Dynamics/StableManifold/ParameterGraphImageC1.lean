import HolomorphicAnosov.Dynamics.StableManifold.FiniteRankSplitBundleFibreRegularity
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphAtlasOperations
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphHorizontalInverse
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphSlopeEvaluation
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphTaylorJetTransport
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphSlopeTransform
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphDerivativeBlocks
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphPreimageSlopeContinuity
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphJointDerivativeEvaluation
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphC1OfEvaluation

noncomputable section
open Set Topology
namespace HolomorphicAnosov

/-- HPS pp.33–35,55–56 and 62: a continuous invariant image graph is jointly
fibre C¹ under the original graph-transform contraction bounds. The ambient
derivative evaluated along its continuous graph gives continuous block
evaluations. The rational image slope action preserves their continuity,
using the continuous inverse anchor return. Its contracting Picard iterates
yield a continuous invariant unit slope field. The inverse-return Taylor
defect estimate identifies that field as the actual derivative. The tangent
evaluation criterion then gives joint fibre C¹ regularity in the original
atlases. Only horizontal operators are inverted; the lower block may be singular. -/
theorem parameter_graph_image_c1
    {A : Type*} (X Y : A → Type*)
    [∀ p, NormedAddCommGroup (X p)] [∀ p, NormedSpace ℝ (X p)]
    [∀ p, CompleteSpace (X p)]
    [∀ p, NormedAddCommGroup (Y p)] [∀ p, NormedSpace ℝ (Y p)]
    [∀ p, CompleteSpace (Y p)]
    [TopologicalSpace A]
    [TopologicalSpace (Sigma X)] [TopologicalSpace (Sigma Y)]
    [TopologicalSpace (Sigma (fun p ↦ X p × Y p))]
    (e : SplitFiniteRankNormedAtlas (E₁ := X) (E₂ := Y))
    (r : ℕ) (hr : 1 ≤ r)
    (h : A ≃ₜ A) (T : ∀ p, X p ≃L[ℝ] X (h p))
    (S : ∀ p, Y p →L[ℝ] Y (h p))
    (G : ∀ p, X p × Y p → X (h p) × Y (h p))
    (hGj : JointFiberContDiff e.total e.total h r G)
    (a k ε c : NNReal) (ha : ∀ p, ‖(T p).symm.toContinuousLinearMap‖ ≤ a)
    (hk : ∀ p, ‖S p‖ ≤ k)
    (hsmall : 2 * (a : ℝ) * ε < 1)
    (hjet : (a : ℝ) * (k + 2 * ε) / (1 - 2 * (a : ℝ) * ε) < 1)
    (hreturn : ((k : ℝ) + 2 * ε) * c < 1)
    (hR : ∀ p, LipschitzWith ε (fun z ↦ G p z - (T p z.1,S p z.2)))
    (s : ∀ p, X p → Y p) (hs : ∀ p, LipschitzWith 1 (s p))
    (hsc : Continuous (fun z : Sigma X ↦ (⟨z.1,s z.1 z.2⟩ : Sigma Y)))
    (H : ∀ p, X p ≃ₜ X (h p))
    (hfirst : ∀ p x, (G p (x,s p x)).1 = H p x)
    (hsecond : ∀ p x, (G p (x,s p x)).2 = s (h p) (H p x))
    (hH : ∀ p, LipschitzWith c ((H p).symm : X (h p) → X p))
    (hHinv : Continuous
      (Equiv.sigmaCongr h.toEquiv (fun p ↦ (H p).toEquiv)).symm) :
    JointFiberContDiff e.first e.second id 1 s := by
  classical
  have hG : ∀p,Differentiable ℝ (G p) := fun p ↦
    (hGj.1 p).differentiable (by exact_mod_cast (show r ≠ 0 by omega))
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
  have hproj := parameter_graph_atlas_projection_continuous e.first
  have hcomponents := parameter_graph_atlas_split_projections_continuous e
  have hAxCx : Continuous (fun z : ParameterGraphTangentPoint X ↦
      (⟨h z.base,F z.base z.point (z.vector,0)⟩ : Sigma (fun p ↦ X p × Y p))) := by
    let Z := ParameterGraphTangentPoint X
    have hb : Continuous (fun z : Z ↦ z.base) :=
      hproj.comp ParameterGraphTangentPoint.continuous_point
    apply parameter_graph_joint_derivative_evaluation e.total e.total h h.continuous G r hr hGj
      (fun z : Z ↦ z.base) hb
      (fun z ↦ (z.point,s z.base z.point)) (fun z ↦ (z.vector,0))
    · exact parameter_graph_atlas_pair_continuous e _ _ _
        ParameterGraphTangentPoint.continuous_point (hsc.comp ParameterGraphTangentPoint.continuous_point)
    · exact parameter_graph_atlas_pair_continuous e _ _ _ ParameterGraphTangentPoint.continuous_vector
        (parameter_graph_atlas_zero_continuous e.second _ hb)
  have hBvDv : Continuous (fun z : ParameterGraphMixedPoint X Y ↦
      (⟨h z.base,F z.base z.point (0,z.vector)⟩ : Sigma (fun p ↦ X p × Y p))) := by
    let Z := ParameterGraphMixedPoint X Y
    have hb : Continuous (fun z : Z ↦ z.base) :=
      hproj.comp ParameterGraphMixedPoint.continuous_point
    apply parameter_graph_joint_derivative_evaluation e.total e.total h h.continuous G r hr hGj
      (fun z : Z ↦ z.base) hb
      (fun z ↦ (z.point,s z.base z.point)) (fun z ↦ (0,z.vector))
    · exact parameter_graph_atlas_pair_continuous e _ _ _
        ParameterGraphMixedPoint.continuous_point (hsc.comp ParameterGraphMixedPoint.continuous_point)
    · exact parameter_graph_atlas_pair_continuous e _ _ _
        (parameter_graph_atlas_zero_continuous e.first _ hb) ParameterGraphMixedPoint.continuous_vector
  have hAc := hcomponents.1.comp hAxCx
  have hCc := hcomponents.2.comp hAxCx
  have hBc := hcomponents.1.comp hBvDv
  have hDc := hcomponents.2.comp hBvDv
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
  let R : Sigma X ≃ Sigma X := Equiv.sigmaCongr h.toEquiv (fun p ↦ (H p).toEquiv)
  have hpreserve (P Q : ∀i : Sigma X,ParameterGraphUnitHom (X i.1) (Y i.1))
      (hPQ : ∀i,Φ i (P i)=Q (R i))
      (hPc : Continuous (fun z : ParameterGraphTangentPoint X ↦
        (⟨z.base,(P ⟨z.base,z.point⟩).1 z.vector⟩ : Sigma Y))) :
      Continuous (fun z : ParameterGraphTangentPoint X ↦
        (⟨z.base,(Q ⟨z.base,z.point⟩).1 z.vector⟩ : Sigma Y)) := by
    have hJexists (p : A) (x : X p) : ∃ J : X p ≃L[ℝ] X (h p),
        J.toContinuousLinearMap = A₀ p x + (B₀ p x).comp (P ⟨p,x⟩).1 ∧
          ‖J.symm.toContinuousLinearMap‖ ≤ b := by
      obtain ⟨hA,hB,hC,_⟩ := hblocks p x
      exact (parameter_graph_horizontal_inverse (T p) (A₀ p x) (B₀ p x) (C₀ p x)
        a ε (ha p) hsmall hA hB hC).1 (P ⟨p,x⟩).1 (P ⟨p,x⟩).2
    choose J hJeq hJnorm using hJexists
    apply parameter_graph_receiving_evaluation_continuous e.first h H hHinv
      (fun p x ↦ (Q ⟨p,x⟩).1)
    intro p hp x hx v hv
    have hc := parameter_graph_image_slope_evaluation_continuous e.first e.second h h.continuous
      A₀ B₀ C₀ D₀ hAc hBc hCc hDc (fun p x ↦ (P ⟨p,x⟩).1) hPc
      J hJeq (b : ℝ) hJnorm p hp x hx v hv
    apply hc.congr
    intro z
    apply Sigma.ext
    · rfl
    · apply heq_of_eq
      have he := hΦeq ⟨p z,x z⟩ (P ⟨p z,x z⟩)
      rw [hPQ ⟨p z,x z⟩, ← hJeq (p z) (x z)] at he
      have hv' := DFunLike.congr_fun he ((J (p z) (x z)).symm (v z))
      change (Q ⟨h (p z),H (p z) (x z)⟩).1
        (J (p z) (x z) ((J (p z) (x z)).symm (v z))) = _ at hv'
      simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
        ContinuousLinearEquiv.apply_symm_apply, add_apply] using hv'.symm
  obtain ⟨P,hPfix,hPc⟩ := parameter_graph_continuous_invariant_slope_forward e.first e.second
    R Φ q hq hΦ hpreserve
  have hderiv := parameter_graph_image_hasFDerivAt_of_invariant_slope X Y h.toEquiv G s hs H
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
      simp only [Homeomorph.coe_toEquiv]
      rw [he]
      calc
        _ ≤ ‖D₀ p x‖ + ‖(P ⟨h p,H p x⟩).1.comp (B₀ p x)‖ := norm_sub_le _ _
        _ ≤ ((k : ℝ)+ε) + ‖(P ⟨h p,H p x⟩).1‖ * ‖B₀ p x‖ :=
          add_le_add hD ((P ⟨h p,H p x⟩).1.opNorm_comp_le _)
        _ ≤ (k+2*ε : NNReal) := by
          have hp := (P ⟨h p,H p x⟩).2
          change _ ≤ (k : ℝ)+2*ε
          nlinarith [norm_nonneg (P ⟨h p,H p x⟩).1, norm_nonneg (B₀ p x)])
  exact parameter_graph_c1_of_tangent_evaluation e.first e.second id s hsc
    (fun p x ↦ (P ⟨p,x⟩).1) hderiv hPc

end HolomorphicAnosov
