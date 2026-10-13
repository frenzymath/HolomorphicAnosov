import Mathlib.Analysis.Calculus.MeanValue

/-!
# Ordered factorization of a transition preserving both plaque directions

This file factors a differentiable transition map whose cross-direction derivatives vanish on an open product (Lee, Prop. 19.12).
-/

open Set

namespace HolomorphicAnosov.Ghys

/-- If the cross-direction derivatives of a differentiable map vanish on an open connected product, each output coordinate depends only on its corresponding input coordinate, with the stated anchors (Lee, Prop. 19.12). -/
theorem surface_product_transition_factors
    {E F G H : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    {U : Set E} {V : Set F} (hU : IsOpen U) (hV : IsOpen V)
    (hcU : IsPreconnected U) (hcV : IsPreconnected V)
    (T : E × F → G × H) (hT : DifferentiableOn ℝ T (U ×ˢ V))
    (hvertical : ∀ s ∈ U, ∀ u ∈ V, ∀ v : F,
      (fderiv ℝ T (s, u) (0, v)).1 = 0)
    (hhorizontal : ∀ s ∈ U, ∀ u ∈ V, ∀ v : E,
      (fderiv ℝ T (s, u) (v, 0)).2 = 0)
    (s₀ : E) (u₀ : F) (hs₀ : s₀ ∈ U) (hu₀ : u₀ ∈ V) :
    ∀ s ∈ U, ∀ u ∈ V, T (s, u) = ((T (s, u₀)).1, (T (s₀, u)).2) := by
  have hTd (s : E) (hs : s ∈ U) (u : F) (hu : u ∈ V) :=
    (hT (s, u) ⟨hs, hu⟩).differentiableAt ((hU.prod hV).mem_nhds ⟨hs, hu⟩)
  intro s hs u hu
  apply Prod.ext
  · have hd (v : F) (hv : v ∈ V) :=
      ((hTd s hs v hv).hasFDerivAt.comp v (hasFDerivAt_prodMk_right s v)).fst
    apply hV.is_const_of_fderiv_eq_zero hcV
      (fun v hv ↦ (hd v hv).differentiableAt.differentiableWithinAt) ?_ hu hu₀
    intro v hv
    rw [(hd v hv).fderiv]
    ext w
    exact hvertical s hs v hv w
  · have hd (v : E) (hv : v ∈ U) :=
      ((hTd v hv u hu).hasFDerivAt.comp v
        (hasFDerivAt_prodMk_left (𝕜 := ℝ) v u)).snd
    apply hU.is_const_of_fderiv_eq_zero hcU
      (fun v hv ↦ (hd v hv).differentiableAt.differentiableWithinAt) ?_ hs hs₀
    intro v hv
    rw [(hd v hv).fderiv]
    ext w
    exact hhorizontal v hv u hu w


end HolomorphicAnosov.Ghys
