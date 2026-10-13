import HolomorphicAnosov.Analysis.FrameOperatorNormContinuity
import HolomorphicAnosov.Dynamics.StableManifold.FiniteRankAtlasFrameContinuity

open Set Topology _root_.Topology Filter

namespace HolomorphicAnosov
noncomputable section

/-- Solutions of a family with a uniform inverse estimate depend continuously on the
parameter in finite dimensional moving frames. This is the parameter contraction
argument of HPS, Invariant Manifolds, p.62. At a fixed parameter, hold its solution's
frame coordinates constant. Its residual tends to zero. The inverse estimate bounds
the original norm of the solution difference by this residual; continuity of the
inverse frame's operator norm transfers the estimate to model coordinates. Squeezing
proves continuity. Compactness of the model unit sphere gives frame norm continuity,
including the zero dimensional case; no invertibility of a lower block is used. -/
theorem parameter_graph_inverse_solution_coordinates_continuous
    {X V : Type*} [TopologicalSpace X]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    {E F : X → Type*}
    [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℝ (E x)]
    [∀ x, NormedAddCommGroup (F x)]
    (j : ∀ x, V ≃L[ℝ] E x)
    (hframe : Continuous (fun z : X × V ↦ ‖j z.1 z.2‖))
    (H : ∀ x, E x → F x) (target : ∀ x, F x) (s : ∀ x, E x)
    (K : ℝ)
    (hinv : ∀ x u v, ‖u - v‖ ≤ K * ‖H x u - H x v‖)
    (hsol : ∀ x, H x (s x) = target x)
    (hres : ∀ v : V, Continuous (fun x ↦ ‖H x (j x v) - target x‖)) :
    Continuous (fun x ↦ (j x).symm (s x)) := by
  have hc : Continuous (fun x ↦ ‖(j x).symm.toContinuousLinearMap‖) := by
    apply continuous_norm_of_frame j (fun x ↦ (j x).symm.toContinuousLinearMap) hframe
    simpa using (continuous_snd.norm : Continuous (fun z : X × V ↦ ‖z.2‖))
  apply continuous_iff_continuousAt.mpr
  intro x₀
  let v₀ := (j x₀).symm (s x₀)
  have hzero : ‖H x₀ (j x₀ v₀) - target x₀‖ = 0 := by simp [v₀, hsol]
  have hlim : Tendsto
      (fun x ↦ ‖(j x).symm.toContinuousLinearMap‖ * K *
        ‖H x (j x v₀) - target x‖) (𝓝 x₀) (𝓝 0) := by
    have h := (((hc.mul_const K).mul (hres v₀)).continuousAt (x := x₀)).tendsto
    convert h using 1; simp [hzero]
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun x ↦ norm_nonneg _) _ hlim
  intro x
  calc
    ‖(j x).symm (s x) - (j x₀).symm (s x₀)‖ =
        ‖(j x).symm (s x - j x v₀)‖ := by simp [map_sub, v₀]
    _ ≤ ‖(j x).symm.toContinuousLinearMap‖ * ‖s x - j x v₀‖ :=
      (j x).symm.toContinuousLinearMap.le_opNorm _
    _ ≤ ‖(j x).symm.toContinuousLinearMap‖ *
        (K * ‖H x (j x v₀) - target x‖) := by
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      simpa [hsol, norm_sub_rev] using hinv x (s x) (j x v₀)
    _ = _ := by ring

/-- Parameter dependent inverse solutions form a continuous section of the original
finite rank normed bundle. The receiving fibres may vary over any base map. On the
preimage of a source chart, its inverse coordinates form a continuous frame and the
original Finsler norm makes the frame norm jointly continuous. Apply the preceding
inverse estimate theorem on that open parameter set, then compose its coordinate
solution with the continuous original frame. These open sets cover all parameters.
This implements the original bundle parameter argument in HPS, Invariant Manifolds,
pp.8 and 62, without imposing uniform bounds on all bundle charts. -/
theorem parameter_graph_inverse_solution_continuous
    {X A B : Type*} [TopologicalSpace X] [TopologicalSpace A]
    {E : A → Type*} {F : B → Type*}
    [∀ p, NormedAddCommGroup (E p)] [∀ p, NormedSpace ℝ (E p)]
    [∀ q, NormedAddCommGroup (F q)] [TopologicalSpace (Sigma E)]
    (e : FiniteRankNormedAtlas (E := E))
    (a : X → A) (b : X → B) (ha : Continuous a)
    (H : ∀ x, E (a x) → F (b x)) (target : ∀ x, F (b x))
    (s : ∀ x, E (a x)) (K : ℝ)
    (hinv : ∀ x u v, ‖u - v‖ ≤ K * ‖H x u - H x v‖)
    (hsol : ∀ x, H x (s x) = target x)
    (hres : ∀ i (v : FiniteFiberModel (e.rank i)),
      Continuous (fun x : {x : X // a x ∈ (e.chart i).baseSet} ↦
        ‖H x.val ((e.coordinates i (a x.val) x.property).symm v) - target x.val‖)) :
    Continuous (fun x ↦ (⟨a x, s x⟩ : Sigma E)) := by
  apply continuous_iff_continuousAt.mpr
  intro x₀
  let i := a x₀
  let U := {x : X | a x ∈ (e.chart i).baseSet}
  let j : ∀ x : U, FiniteFiberModel (e.rank i) ≃L[ℝ] E (a x.val) :=
    fun x ↦ (e.coordinates i (a x.val) x.property).symm
  have hbase : Continuous (fun x : U ↦ (⟨a x.val, x.property⟩ : (e.chart i).baseSet)) :=
    (ha.comp continuous_subtype_val).subtype_mk _
  have hframe : Continuous (fun z : U × FiniteFiberModel (e.rank i) ↦
      (⟨a z.1.val, j z.1 z.2⟩ : Sigma E)) :=
    (atlas_frame_continuous e i).comp ((hbase.comp continuous_fst).prodMk continuous_snd)
  have hcoords : Continuous (fun x : U ↦ (j x).symm (s x.val)) :=
    parameter_graph_inverse_solution_coordinates_continuous j
      (e.continuous_norm.comp hframe) (fun x ↦ H x.val) (fun x ↦ target x.val)
      (fun x ↦ s x.val) K (fun x ↦ hinv x.val) (fun x ↦ hsol x.val) (hres i)
  have hsection : Continuous (fun x : U ↦ (⟨a x.val, s x.val⟩ : Sigma E)) := by
    have hc' := hframe.comp (continuous_id.prodMk hcoords)
    convert hc' using 1
    funext x
    apply Sigma.ext
    · rfl
    · simp only [Function.comp_apply, id_eq]
      exact HEq.symm (heq_of_eq ((j x).apply_symm_apply (s x.val)))
  have hon : ContinuousOn (fun x ↦ (⟨a x, s x⟩ : Sigma E)) U :=
    continuousOn_iff_continuous_domRestrict.mpr hsection
  exact hon.continuousAt (((e.chart i).open_baseSet.preimage ha).mem_nhds
    (e.mem_baseSet i))

end
end HolomorphicAnosov
