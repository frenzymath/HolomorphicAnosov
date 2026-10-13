import Mathlib

/-! A differentiable map with zero derivative in every horizontal direction on an open product
domain is constant on each horizontal slice of a sufficiently small product ball. -/

open Set Topology _root_.Topology

namespace HolomorphicAnosov.FrobeniusSupport

variable {E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]
  [NormedAddCommGroup G] [NormedSpace ℂ G]

theorem exists_product_ball_transverse_independent
    {U : Set (E × F)} (hU : IsOpen U) (g : E × F → G)
    (hg : DifferentiableOn ℂ g U)
    (hzero : ∀ z ∈ U, ∀ v : E, fderiv ℂ g z (v, 0) = 0)
    {z : E × F} (hz : z ∈ U) :
    ∃ ε : ℝ, 0 < ε ∧
      Metric.ball z.1 ε ×ˢ Metric.ball z.2 ε ⊆ U ∧
      ∀ a ∈ Metric.ball z.1 ε ×ˢ Metric.ball z.2 ε,
        ∀ b ∈ Metric.ball z.1 ε ×ˢ Metric.ball z.2 ε,
          a.2 = b.2 → g a = g b := by
  obtain ⟨ε, hε, hsub⟩ := Metric.isOpen_iff.mp hU z hz
  have hprod : Metric.ball z.1 ε ×ˢ Metric.ball z.2 ε ⊆ U := by
    simpa only [ball_prod_same, Prod.eta] using hsub
  refine ⟨ε, hε, hprod, ?_⟩
  intro a ha b hb hab
  let f : E → G := fun x ↦ g (x, a.2)
  have hd : ∀ x ∈ Metric.ball z.1 ε, HasFDerivAt f (0 : E →L[ℂ] G) x := by
    intro x hx
    have hxu : (x, a.2) ∈ U := hprod ⟨hx, ha.2⟩
    have hcomp := ((hg.differentiableAt (hU.mem_nhds hxu)).hasFDerivAt).comp x
      (hasFDerivAt_prodMk_left (𝕜 := ℂ) x a.2)
    have heq : (fderiv ℂ g (x, a.2)).comp (ContinuousLinearMap.inl ℂ E F) = 0 := by
      ext v
      exact hzero (x, a.2) hxu v
    simpa only [heq, f, Function.comp_def] using hcomp
  have hconst := (convex_ball z.1 ε).is_const_of_fderivWithin_eq_zero (𝕜 := ℂ)
    (fun x hx ↦ (hd x hx).differentiableAt.differentiableWithinAt)
    (fun x hx ↦ (hd x hx).hasFDerivWithinAt.fderivWithin
      (Metric.isOpen_ball.uniqueDiffOn x hx)) ha.1 hb.1
  calc
    g a = f a.1 := rfl
    _ = f b.1 := hconst
    _ = g b := congrArg g (Prod.ext rfl hab)


end HolomorphicAnosov.FrobeniusSupport
