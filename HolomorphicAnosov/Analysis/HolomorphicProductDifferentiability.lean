/-
The mean-value splitting proof is adapted from Mathlib's FDeriv/Partial.lean.
Copyright (c) 2025 A Tucker. Released under Apache 2.0 license.
-/
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.Analysis.Calculus.FDeriv.OfCompLeft
import Mathlib.Analysis.Normed.Module.FiniteDimension
import HolomorphicAnosov.Analysis.HolomorphicSliceFrameContinuity

/-! # First-order regularity of a holomorphic product chart

Source: Demailly I §3.B, pp.22–23; the mean-value splitting argument of
Mathlib.Analysis.Calculus.FDeriv.Partial, lines 31–50.
DAG nodes: `analysis.continuous_first_partial_differentiability_g13` and
`analysis.holomorphic_product_differentiability_g13`.
-/

namespace HolomorphicAnosov.Analysis
open Filter Asymptotics
open scoped Topology _root_.Topology Convex

/-- Differentiability from one jointly continuous partial derivative and the
other derivative on the central axis. Source: the mean-value estimate proved
in Mathlib `FDeriv/Partial.lean`, `isLittleO_sub_sub_fderiv`. This is the
first-order decomposition used in the native paired-product scalar proof.

Proof: split the increment from `(a,b)` to `(x,y)` into the first-variable
increment from `(a,y)` to `(x,y)` and the central-axis increment from `(a,b)`
to `(a,y)`. The first remainder is little-o of `x-a` by the mean-value
estimate and joint continuity of the first partial derivative. The second
is little-o of `y-b` by the given axis derivative. Each coordinate increment
has norm at most the norm of the full increment, so adding the remainders
gives the asserted derivative. The second partial derivative away from the
central axis is not assumed. Zero-dimensional models are included. -/
theorem hasFDerivAt_of_continuous_first_partial
    {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (H : E × F → G) (D : E × F → E →L[ℝ] G)
    (a : E) (b : F) (B : F →L[ℝ] G)
    (hD : ContinuousAt D (a,b))
    (hd : ∀ᶠ p in 𝓝 (a,b), HasFDerivAt (fun x ↦ H (x,p.2)) (D p) p.1)
    (hb : HasFDerivAt (fun y ↦ H (a,y)) B b) :
    HasFDerivAt H ((D (a,b)).coprod B) (a,b) := by
  have ht : Tendsto (fun z : (E × F) × E ↦ (z.2,z.1.2))
      (𝓝 (a,b) ×ˢ 𝓝 a) (𝓝 (a,b)) :=
    tendsto_snd.prodMk_nhds (continuous_snd.continuousAt.tendsto.comp tendsto_fst)
  have hfirst : (fun p : E × F ↦ H (p.1,p.2) - H (a,p.2) - D (a,b) (p.1-a))
      =o[𝓝 (a,b)] (fun p ↦ p.1-a) := by
    rw [isLittleO_iff]
    intro ε hε
    have hder : ∀ᶠ p in 𝓝 (a,b), ∀ z ∈ [a -[ℝ] p.1],
        HasFDerivAt (fun x ↦ H (x,p.2)) (D (z,p.2)) z :=
      (ht.eventually hd).segment_of_prod_nhds tendsto_const_nhds
        continuous_fst.continuousAt.tendsto
    have hsmall : ∀ᶠ p in 𝓝 (a,b), ∀ z ∈ [a -[ℝ] p.1],
        ‖D (z,p.2) - D (a,b)‖ < ε := by
      have hh := hD.tendsto.comp ht
      rw [Metric.tendsto_nhds] at hh
      have he := hh ε hε
      simp only [dist_eq_norm_sub] at he
      exact he.segment_of_prod_nhds tendsto_const_nhds continuous_fst.continuousAt.tendsto
    filter_upwards [hder, hsmall] with p hp hεp
    exact Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le'
      (fun z hz ↦ (hp z hz).hasFDerivWithinAt) (fun z hz ↦ (hεp z hz).le)
      (convex_segment ..) (left_mem_segment ..) (right_mem_segment ..)
  have hsecond : (fun p : E × F ↦ H (a,p.2) - H (a,b) - B (p.2-b))
      =o[𝓝 (a,b)] (fun p ↦ p.2-b) :=
    (hasFDerivAt_iff_isLittleO.mp hb).comp_tendsto continuous_snd.continuousAt.tendsto
  have hfst : (fun p : E × F ↦ p.1-a) =O[𝓝 (a,b)] (fun p ↦ p-(a,b)) :=
    isBigO_of_le _ (fun p ↦ norm_fst_le (p-(a,b)))
  have hsnd : (fun p : E × F ↦ p.2-b) =O[𝓝 (a,b)] (fun p ↦ p-(a,b)) :=
    isBigO_of_le _ (fun p ↦ norm_snd_le (p-(a,b)))
  rw [hasFDerivAt_iff_isLittleO]
  convert (hfirst.trans_isBigO hfst).add (hsecond.trans_isBigO hsnd) using 1
  funext p
  simp only [ContinuousLinearMap.coprod_apply, Prod.fst_sub, Prod.snd_sub]
  abel

/-- A continuous product chart with holomorphic first-variable slices has a
real derivative at every point where its central transverse axis has a
real derivative. Source: the preceding first-partial estimate and Demailly
I §3.B. The Cauchy integral formula makes the holomorphic partial derivative
jointly continuous, which is the sole transverse regularity needed. -/
theorem hasFDerivAt_holomorphic_product
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {d : ℕ}
    (H : ℂ × F → Fin d → ℂ) (Ω : Set (ℂ × F)) (hΩ : IsOpen Ω)
    (hH : ContinuousOn H Ω)
    (hhol : ∀ t, DifferentiableOn ℂ (fun z ↦ H (z,t)) {z | (z,t) ∈ Ω})
    (a : ℂ) (b : F) (hab : (a,b) ∈ Ω) (B : F →L[ℝ] (Fin d → ℂ))
    (hb : HasFDerivAt (fun y ↦ H (a,y)) B b) :
    HasFDerivAt H
      (((fderiv ℂ (fun z ↦ H (z,b)) a).restrictScalars ℝ).coprod B) (a,b) := by
  let D (p : ℂ × F) : ℂ →L[ℝ] (Fin d → ℂ) :=
    (ContinuousLinearMap.toSpanSingleton ℂ (deriv (fun z ↦ H (z,p.2)) p.1)).restrictScalars ℝ
  have hdc := holomorphic_slice_vector_derivative_continuousOn Ω hΩ H hH hhol
  have hD : ContinuousAt D (a,b) :=
    (ContinuousLinearMap.continuous_restrictScalars ℝ).continuousAt.comp
      ((ContinuousLinearMap.toSpanSingletonLIE ℂ (Fin d → ℂ)).continuous.continuousAt.comp
        (hdc.continuousAt (hΩ.mem_nhds hab)))
  have hd : ∀ᶠ p in 𝓝 (a,b), HasFDerivAt (fun z ↦ H (z,p.2)) (D p) p.1 := by
    filter_upwards [hΩ.mem_nhds hab] with p hp
    exact ((hhol p.2).differentiableAt
      ((hΩ.preimage (continuous_id.prodMk continuous_const)).mem_nhds hp)).hasDerivAt.hasFDerivAt.restrictScalars ℝ
  have hder := hasFDerivAt_of_continuous_first_partial H D a b B hD hd hb
  have hf := ((hhol b).differentiableAt
    ((hΩ.preimage (continuous_id.prodMk continuous_const)).mem_nhds hab)).hasDerivAt.hasFDerivAt.fderiv
  simpa only [D, ← hf] using hder

/-- Differentiability transports through a pre-existing product homeomorphism
once its derivative is bijective. Source: Mathlib's inverse derivative theorem
for open partial homeomorphisms. No differentiability on a neighborhood is
required: use the continuous topological inverse and differentiate its inverse
identity at the chosen point, then compose. -/
theorem differentiableAt_of_comp_product_chart
    {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    (H : OpenPartialHomeomorph E F) (p : E) (hp : p ∈ H.source)
    (A : E →L[ℝ] F) (hA : HasFDerivAt H A p) (hbij : Function.Bijective A)
    (q : F → G) (hq : DifferentiableAt ℝ (q ∘ H) p) :
    DifferentiableAt ℝ q (H p) := by
  let e : E ≃L[ℝ] F := (LinearEquiv.ofBijective A.toLinearMap hbij).toContinuousLinearEquiv
  have he : (e : E →L[ℝ] F) = A := by ext; rfl
  have hi : HasFDerivAt H.symm (e.symm : F →L[ℝ] E) (H p) := by
    apply H.hasFDerivAt_symm (H.map_source hp)
    simpa only [H.left_inv hp, he] using hA
  have hq' : DifferentiableAt ℝ (q ∘ H) (H.symm (H p)) := by
    simpa only [H.left_inv hp] using hq
  have hc := hq'.comp (H p) hi.differentiableAt
  apply hc.congr_of_eventuallyEq
  filter_upwards [H.open_target.mem_nhds (H.map_source hp)] with z hz
  simp only [Function.comp_apply, H.right_inv hz]

end HolomorphicAnosov.Analysis

