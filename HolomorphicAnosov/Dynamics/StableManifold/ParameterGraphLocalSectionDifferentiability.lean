import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphLocalFiberRegularity
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphCompactForcing
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphFibreBoundedForcing

noncomputable section
open Set
open scoped _root_.Topology ContDiff
namespace HolomorphicAnosov

/-- The quantitative C¹ step for the local invariant-section induction.
A bounded invariant section in the interior of a receiving-value ball becomes
Lipschitz by bounded-forcing iteration. Compact original rectangular discs
bound the known horizontal derivative of the action. The bounded affine
section contraction constructs its candidate derivative, and Taylor transport
identifies it with the actual derivative. Thus no regularity of the unknown
section is assumed. Source: HPS, Invariant Manifolds, pp.32–36,62. -/
theorem parameter_graph_local_section_differentiable
    {A : Type*} [TopologicalSpace A] [CompactSpace A]
    {X Y : A → Type*}
    [∀p,NormedAddCommGroup (X p)] [∀p,NormedSpace ℝ (X p)]
    [∀p,NormedAddCommGroup (Y p)] [∀p,NormedSpace ℝ (Y p)] [∀p,CompleteSpace (Y p)]
    [TopologicalSpace (Sigma X)] [TopologicalSpace (Sigma Y)]
    (h : A→A) [TopologicalSpace (Sigma (fun p ↦ Y (h p)))]
    (e : FiniteRankNormedAtlas (E := X)) (f : FiniteRankNormedAtlas (E := Y))
    (fh : FiniteRankNormedAtlas (E := fun p ↦ Y (h p)))
    (R : ∀p,X p→X (h p)) (F : ∀p,X p×Y (h p)→Y p) (P : ∀p,X p→Y p)
    (d M M₀ : ℝ) (q c : NNReal) (hM : M<M₀)
    (hq : (q:ℝ)<1) (hqc : (q:ℝ)*c<1)
    (hP : ∀p x,‖x‖<d → ‖P p x‖≤M)
    (hRU : ∀p,MapsTo (R p) (Metric.ball 0 d) (Metric.ball 0 d))
    (hR : ∀p,LipschitzOnWith c (R p) (Metric.ball 0 d))
    (hRd : ∀p x,‖x‖<d → DifferentiableAt ℝ (R p) x)
    (hinv : ∀p x,‖x‖<d → P p x=F p (x,P (h p) (R p x)))
    (hvertical : ∀p x,‖x‖≤d →
      LipschitzOnWith q (fun v ↦ F p (x,v)) (Metric.closedBall 0 M₀))
    (W : Set (Sigma (fun p ↦ X p×Y (h p))))
    (hW : @IsOpen _ (ParameterGraphProductAtlas.topology (E := X) (F := fun p ↦ Y (h p))) W)
    (hF : letI := ParameterGraphProductAtlas.topology (E := X) (F := fun p ↦ Y (h p))
      JointFiberContDiffOn (ParameterGraphProductAtlas.atlas e fh) f id 1 W F)
    (hrect : ∀p (x:X p) (v:Y (h p)), ‖x‖≤d → ‖v‖≤M₀ →
      (⟨p,(x,v)⟩ : Sigma (fun p ↦ X p×Y (h p)))∈W) :
    ∃ B : NNReal,
      (∀p x,‖x‖<d → DifferentiableAt ℝ (P p) x) ∧
      (∀p x,‖x‖<d → ‖fderiv ℝ (P p) x‖≤(B:ℝ)/(1-(q:ℝ)*c)) := by
  let := ParameterGraphProductAtlas.topology (E := X) (F := fun p ↦ Y (h p))
  obtain ⟨B,hB,hFL⟩ := parameter_graph_compact_rectangular_forcing
    e fh f id continuous_id F 1 (le_refl 1) W d M₀ hW hF hrect
  have hRP (p:A) (x:X p) (hx:‖x‖<d) : ‖P (h p) (R p x)‖≤M :=
    hP (h p) (R p x) (by simpa only [Metric.mem_ball,dist_zero_right] using
      (hRU p (by simpa only [Metric.mem_ball,dist_zero_right] using hx)))
  have hFd (p:A) (x:X p) (hx:‖x‖<d) :
      DifferentiableAt ℝ (F p) (x,P (h p) (R p x)) :=
    (hF.1 ⟨p,(x,P (h p) (R p x))⟩
      (hrect p x _ hx.le ((hRP p x hx).trans hM.le))).differentiableAt (by simp)
  have hstep (p:A) (x:X p) (hx:x∈Metric.ball 0 d) (y:X p) (hy:y∈Metric.ball 0 d) :
      dist (P p x) (P p y) ≤
        (q:ℝ)*dist (P (h p) (R p x)) (P (h p) (R p y))+(B:ℝ)*dist x y := by
    have hx' : ‖x‖<d := by simpa using hx
    have hy' : ‖y‖<d := by simpa using hy
    rw [hinv p x hx',hinv p y hy']
    simpa only [dist_eq_norm] using parameter_graph_rectangular_comparison
      (F p) B q d M₀ (hFL p) (hvertical p) x y
      (P (h p) (R p x)) (P (h p) (R p y)) hx'.le hy'.le
      ((hRP p x hx').trans hM.le) ((hRP p y hy').trans hM.le)
  have hc := parameter_graph_bounded_invariant_section_differentiable_on X Y h R F P
    (fun p ↦ Metric.ball 0 d) (fun p ↦ Metric.isOpen_ball) hRU B q c B M hq hqc
    (fun p x hx ↦ hP p x (by simpa using hx)) hR hstep
    (fun p x hx ↦ hinv p x (by simpa using hx))
    (fun p x ↦ fderiv ℝ (R p) x)
    (fun p x hx ↦ (hRd p x (by simpa using hx)).hasFDerivAt)
    (fun p x ↦ fderiv ℝ (F p) (x,P (h p) (R p x)))
    (fun p x hx ↦ (hFd p x (by simpa using hx)).hasFDerivAt) ?_ ?_
  · exact ⟨B,fun p x hx ↦ hc.1 p x (by simpa using hx),
      fun p x hx ↦ hc.2 p x (by simpa using hx)⟩
  · intro p x hx
    have hx' : ‖x‖<d := by simpa using hx
    exact parameter_graph_vertical_derivative_bound_on_ball (F p) x
      (P (h p) (R p x)) M₀ q (hFd p x hx') ((hRP p x hx').trans_lt hM)
      (hvertical p x hx'.le)
  · intro p x hx
    have hx' : ‖x‖<d := by simpa using hx
    apply ContinuousLinearMap.opNorm_le_bound _ B.2
    intro v
    calc
      ‖(fderiv ℝ (F p) (x,P (h p) (R p x))) (v,0)‖ ≤
          ‖fderiv ℝ (F p) (x,P (h p) (R p x))‖ * ‖(v,(0:Y (h p)))‖ :=
        ContinuousLinearMap.le_opNorm _ _
      _ ≤ (B:ℝ)*‖v‖ := by
        simpa only [Prod.norm_mk,norm_zero,max_eq_left (norm_nonneg _)] using
          mul_le_mul_of_nonneg_right
            (hB p (x,P (h p) (R p x)) hx'.le ((hRP p x hx').trans hM.le))
            (norm_nonneg (v,(0:Y (h p))))

/-- The top-order homogeneous part of the tangent action contracts by the
product of the vertical contraction and the spatial return derivative bound. -/
theorem parameter_graph_tangent_action_lipschitz
    {X Y X' Y' : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup X'] [NormedSpace ℝ X']
    [NormedAddCommGroup Y'] [NormedSpace ℝ Y']
    (D : X×Y'→L[ℝ]Y) (R : X→L[ℝ]X') (q c : NNReal)
    (hD : ‖D.comp (ContinuousLinearMap.inr ℝ X Y')‖≤q) (hR : ‖R‖≤c) :
    LipschitzWith (q*c) (fun Q:X'→L[ℝ]Y' ↦
      D.comp ((ContinuousLinearMap.id ℝ X).prod (Q.comp R))) := by
  apply LipschitzWith.of_dist_le_mul
  intro Q Q'
  let B := D.comp (ContinuousLinearMap.inr ℝ X Y')
  have heq : D.comp ((ContinuousLinearMap.id ℝ X).prod (Q.comp R)) -
      D.comp ((ContinuousLinearMap.id ℝ X).prod (Q'.comp R)) =
      B.comp ((Q-Q').comp R) := by
    ext v
    change D (v,Q (R v))-D (v,Q' (R v))=D (0,(Q-Q') (R v))
    rw [← map_sub]
    simp
  rw [dist_eq_norm,heq,dist_eq_norm,NNReal.coe_mul]
  calc
    ‖B.comp ((Q-Q').comp R)‖ ≤ ‖B‖*(‖Q-Q'‖*‖R‖) :=
      (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
    _ ≤ (q:ℝ)*(‖Q-Q'‖*c) :=
      mul_le_mul hD (mul_le_mul_of_nonneg_left hR (norm_nonneg _))
        (mul_nonneg (norm_nonneg _) (norm_nonneg _)) q.2
    _ = (q:ℝ)*c*‖Q-Q'‖ := by ring

/-- A centered return that contracts on a source ball preserves every smaller
concentric ball. This lets the finite-order induction shrink domains without
changing the original return or introducing an extension. -/
theorem parameter_graph_return_smaller_ball
    {X Y : Type*} [NormedAddCommGroup X] [NormedAddCommGroup Y]
    (R : X→Y) (c : NNReal) (d δ : ℝ) (hd : 0<d) (hδ : δ≤d)
    (hc : (c:ℝ)≤1) (hR : LipschitzOnWith c R (Metric.ball 0 d)) (hzero : R 0=0) :
    MapsTo R (Metric.ball 0 δ) (Metric.ball 0 δ) ∧
      LipschitzOnWith c R (Metric.ball 0 δ) := by
  have hsub : Metric.ball (0:X) δ ⊆ Metric.ball 0 d := Metric.ball_subset_ball hδ
  refine ⟨?_,hR.mono hsub⟩
  intro x hx
  have hn := hR.dist_le_mul x (hsub hx) 0 (Metric.mem_ball_self hd)
  rw [hzero,dist_zero_right,dist_zero_right] at hn
  have hx' : ‖x‖<δ := by simpa only [Metric.mem_ball,dist_zero_right] using hx
  have he : ‖R x‖<δ := hn.trans_lt ((mul_le_of_le_one_left (norm_nonneg x) hc).trans_lt hx')
  simpa only [Metric.mem_ball,dist_zero_right] using he

end HolomorphicAnosov
