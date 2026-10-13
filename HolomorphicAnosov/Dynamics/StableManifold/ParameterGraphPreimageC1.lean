import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphSlopeEvaluation
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphSlopeTransform
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphTaylorJetTransport
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphFixedGraphDifferentiability
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphPreimageSlopeContinuity
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphJointDerivativeEvaluation
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphC1OfEvaluation

noncomputable section
open Set Topology
namespace HolomorphicAnosov

/-- HPS pp.33–35,57–58,62: the invariant preimage graph is jointly fibre C¹.
The original derivative blocks preserve continuous slope evaluation. Contracting
zero slope iterates converge uniformly in the original operator norms; evaluation
is a weighted atlas limit. Taylor defect identification makes the continuous
slope section the actual derivative, and the chart C¹ criterion concludes. -/
theorem parameter_graph_preimage_c1
    {A : Type*} [TopologicalSpace A] (X Y : A → Type*)
    [∀ p, NormedAddCommGroup (X p)] [∀ p, NormedSpace ℝ (X p)]
    [∀ p, CompleteSpace (X p)]
    [∀ p, NormedAddCommGroup (Y p)] [∀ p, NormedSpace ℝ (Y p)]
    [TopologicalSpace (Sigma X)] [TopologicalSpace (Sigma Y)]
    [TopologicalSpace (Sigma (fun p ↦ X p × Y p))]
    (e : SplitFiniteRankNormedAtlas (E₁ := X) (E₂ := Y))
    (r : ℕ) (hr : 1 ≤ r)
    (h : A → A) (hh : Continuous h) (T : ∀ p, X p ≃L[ℝ] X (h p))
    (S : ∀ p, Y p →L[ℝ] Y (h p))
    (G : ∀ p, X p × Y p → X (h p) × Y (h p))
    (hGj : JointFiberContDiff e.total e.total h r G)
    (a k ε : NNReal) (ha : ∀ p, ‖(T p).symm.toContinuousLinearMap‖ ≤ a)
    (hk : ∀ p, ‖S p‖ ≤ k)
    (hsmall : 2 * (a : ℝ) * ε < 1)
    (hjet : (a : ℝ) * (k + 2 * ε) / (1 - 2 * (a : ℝ) * ε) < 1)
    (hR : ∀ p, LipschitzWith ε (fun z ↦ G p z - (T p z.1,S p z.2)))
    (s : ∀ p, Y p → X p) (hs : ∀ p, LipschitzWith 1 (s p))
    (hsc : Continuous (fun z : Sigma Y ↦ (⟨z.1,s z.1 z.2⟩ : Sigma X)))
    (hgraph : ∀ p y, (G p (s p y,y)).1 = s (h p) (G p (s p y,y)).2) :
    JointFiberContDiff e.second e.first id 1 s := by
  classical
  have hG : ∀p,Differentiable ℝ (G p) := fun p ↦
    (hGj.1 p).differentiable (by exact_mod_cast (show r ≠ 0 by omega))
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
  have hproj := parameter_graph_atlas_projection_continuous e.second
  have hcomponents := parameter_graph_atlas_split_projections_continuous e
  have hGtotal := parameter_graph_joint_value_continuous e.total e.total h hh G r hGj
  let K := fun p y ↦ (G p (s p y,y)).2
  have hKcont : Continuous (fun z : Sigma Y ↦ (⟨h z.1,K z.1 z.2⟩ : Sigma Y)) :=
    hcomponents.2.comp (hGtotal.comp
      (parameter_graph_atlas_pair_continuous e Sigma.fst (fun z ↦ s z.1 z.2)
        Sigma.snd hsc continuous_id))
  have hAxCx : Continuous (fun z : ParameterGraphMixedPoint Y X ↦
      (⟨h z.base,F z.base z.point (z.vector,0)⟩ : Sigma (fun p ↦ X p × Y p))) := by
    let Z := ParameterGraphMixedPoint Y X
    have hb : Continuous (fun z : Z ↦ z.base) :=
      hproj.comp ParameterGraphMixedPoint.continuous_point
    apply parameter_graph_joint_derivative_evaluation e.total e.total h hh G r hr hGj
      (fun z : Z ↦ z.base) hb
      (fun z ↦ (s z.base z.point,z.point)) (fun z ↦ (z.vector,0))
    · exact parameter_graph_atlas_pair_continuous e _ _ _
        (hsc.comp ParameterGraphMixedPoint.continuous_point) ParameterGraphMixedPoint.continuous_point
    · exact parameter_graph_atlas_pair_continuous e _ _ _ ParameterGraphMixedPoint.continuous_vector
        (parameter_graph_atlas_zero_continuous e.second _ hb)
  have hBvDv : Continuous (fun z : ParameterGraphTangentPoint Y ↦
      (⟨h z.base,F z.base z.point (0,z.vector)⟩ : Sigma (fun p ↦ X p × Y p))) := by
    let Z := ParameterGraphTangentPoint Y
    have hb : Continuous (fun z : Z ↦ z.base) :=
      hproj.comp ParameterGraphTangentPoint.continuous_point
    apply parameter_graph_joint_derivative_evaluation e.total e.total h hh G r hr hGj
      (fun z : Z ↦ z.base) hb
      (fun z ↦ (s z.base z.point,z.point)) (fun z ↦ (0,z.vector))
    · exact parameter_graph_atlas_pair_continuous e _ _ _
        (hsc.comp ParameterGraphTangentPoint.continuous_point) ParameterGraphTangentPoint.continuous_point
    · exact parameter_graph_atlas_pair_continuous e _ _ _
        (parameter_graph_atlas_zero_continuous e.first _ hb) ParameterGraphTangentPoint.continuous_vector
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
  have hpreserve (P : ∀i : Sigma Y,ParameterGraphUnitHom (Y i.1) (X i.1))
      (hPc : Continuous (fun z : ParameterGraphTangentPoint Y ↦
        (⟨z.base,(P ⟨z.base,z.point⟩).1 z.vector⟩ : Sigma X))) :
      Continuous (fun z : ParameterGraphTangentPoint Y ↦
        (⟨z.base,(Φ ⟨z.base,z.point⟩ (P (R ⟨z.base,z.point⟩))).1 z.vector⟩ : Sigma X)) := by
    have hJexists (p : A) (y : Y p) : ∃ J : X p ≃L[ℝ] X (h p),
        J.toContinuousLinearMap = A₀ p y - (P (R ⟨p,y⟩)).1.comp (C₀ p y) ∧
          ‖J.symm.toContinuousLinearMap‖ ≤ b := by
      obtain ⟨hA,hB,hC,_⟩ := hblocks p y
      exact (parameter_graph_horizontal_inverse (T p) (A₀ p y) (B₀ p y) (C₀ p y)
        a ε (ha p) hsmall hA hB hC).2 (P (R ⟨p,y⟩)).1 (P (R ⟨p,y⟩)).2
    choose J hJeq hJnorm using hJexists
    have hc := parameter_graph_preimage_slope_evaluation_continuous e.first e.second h hh K
      hKcont A₀ B₀ C₀ D₀ hAc hBc hCc hDc
      (fun p y ↦ (P ⟨p,y⟩).1) hPc J hJeq (b : ℝ) hJnorm
    apply hc.congr
    intro z
    apply Sigma.ext
    · rfl
    · apply heq_of_eq
      apply (J z.base z.point).injective
      rw [(J z.base z.point).apply_symm_apply]
      have he := hΦeq ⟨z.base,z.point⟩ (P (R ⟨z.base,z.point⟩))
      rw [← hJeq z.base z.point] at he
      exact (DFunLike.congr_fun he z.vector).symm
  obtain ⟨P,hPfix,hPc⟩ := parameter_graph_continuous_invariant_slope e.second e.first
    R Φ q hq hΦ hpreserve
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
  exact parameter_graph_c1_of_tangent_evaluation e.second e.first id s hsc
    (fun p y ↦ (P ⟨p,y⟩).1) hderiv hPc


end HolomorphicAnosov
