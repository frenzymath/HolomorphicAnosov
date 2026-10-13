import HolomorphicAnosov.Ghys.CurveContactScalarCoefficients



namespace HolomorphicAnosov.Ghys
open Set Filter _root_.Topology
open scoped Manifold ContDiff
universe u
variable {L : Type u} [TopologicalSpace L] [ChartedSpace ℂ L]
  [IsManifold 𝓘(ℂ) ∞ L]

omit [IsManifold 𝓘(ℂ) ∞ L] in
/-- Scalar functions equal near the base of an admissible curve germ give equal postcomposed germs.
(Ghys, p.591) -/
theorem curveParamGerm_map_congr {Y : Type*} (γ : CurveParamGerm L) (φ ψ : L → Y)
    (h : φ =ᶠ[𝓝 (curveGermBase L γ.val)] ψ) : γ.val.map φ = γ.val.map ψ := by
  obtain ⟨g, hg0, hg, _, hge⟩ := γ.property
  have hb : curveGermBase L γ.val = g 0 := by rw [← hge]; rfl
  rw [hb] at h
  rw [← hge]
  apply Germ.coe_eq.mpr
  exact h.comp_tendsto (hg.contMDiffAt (g.open_source.mem_nhds hg0)).continuousAt

omit [IsManifold 𝓘(ℂ) ∞ L] in
/-- The first and normalized second coefficients of scalar composition satisfy the complex chain
rule. (Ghys, p.591) -/
theorem curveParamGerm_scalar_chain (γ : CurveParamGerm L) (ψ : L → ℂ) (H : ℂ → ℂ)
    (hψ : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ∞ ψ (curveGermBase L γ.val))
    (hH : ContDiffAt ℂ 2 H (ψ (curveGermBase L γ.val))) :
    germFirst (γ.val.map (H ∘ ψ)) =
      deriv H (ψ (curveGermBase L γ.val)) * germFirst (γ.val.map ψ) ∧
    germSecond (γ.val.map (H ∘ ψ)) =
      deriv H (ψ (curveGermBase L γ.val)) * germSecond (γ.val.map ψ) +
        (iteratedDeriv 2 H (ψ (curveGermBase L γ.val)) / 2) *
          germFirst (γ.val.map ψ) ^ 2 := by
  obtain ⟨g, hg0, hg, _, hge⟩ := γ.property
  have hb : curveGermBase L γ.val = g 0 := by rw [← hge]; rfl
  rw [hb] at hψ hH ⊢
  have hψg : ContDiffAt ℂ 2 (ψ ∘ g) 0 :=
    (hψ.comp 0 (hg.contMDiffAt (g.open_source.mem_nhds hg0))).contDiffAt.of_le (by simp)
  rw [← hge]
  change deriv (H ∘ (ψ ∘ g)) 0 = _ * deriv (ψ ∘ g) 0 ∧
    iteratedDeriv 2 (H ∘ (ψ ∘ g)) 0 / 2 =
      _ * (iteratedDeriv 2 (ψ ∘ g) 0 / 2) + _ * deriv (ψ ∘ g) 0 ^ 2
  constructor
  · rw [deriv_comp 0 (hH.differentiableAt (by norm_num))
      (hψg.differentiableAt (by norm_num))]
    rfl
  · rw [iteratedDeriv_comp_two hH hψg]
    dsimp only [Function.comp_apply]
    ring

omit [IsManifold 𝓘(ℂ) ∞ L] in
/-- First-contact-equivalent curve germs have equal first coefficients after composition with a
scalar function holomorphic at their base. (Ghys, p.591) -/
theorem curveContact1_scalar_coefficient (γ δ : CurveParamGerm L)
    (h : CurveContact1 L γ δ) (φ : L → ℂ)
    (hφ : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ∞ φ (curveGermBase L γ.val)) :
    germFirst (γ.val.map φ) = germFirst (δ.val.map φ) := by
  obtain ⟨hb, e, he, ha⟩ := h
  have formula (η : CurveParamGerm L) (hs : curveGermBase L η.val ∈ e.val.source)
      (hp : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ∞ φ (curveGermBase L η.val)) :
      germFirst (η.val.map φ) =
        deriv (φ ∘ e.val.symm) (e.val (curveGermBase L η.val)) * curveGermFirst L e η := by
    have hψ := contMDiffAt_of_mem_maximalAtlas e.property hs
    have hH : ContDiffAt ℂ 2 (φ ∘ e.val.symm) (e.val (curveGermBase L η.val)) := by
      have hp' : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ∞ φ
          (e.val.symm (e.val (curveGermBase L η.val))) := by
        simpa only [e.val.left_inv hs] using hp
      exact (hp'.comp _ (contMDiffAt_symm_of_mem_maximalAtlas e.property
        (e.val.map_source hs))).contDiffAt.of_le (by simp)
    have heq : φ =ᶠ[𝓝 (curveGermBase L η.val)] (φ ∘ e.val.symm) ∘ e.val := by
      filter_upwards [e.val.open_source.mem_nhds hs] with x hx
      simp only [Function.comp_apply, e.val.left_inv hx]
    rw [curveParamGerm_map_congr η _ _ heq]
    exact (curveParamGerm_scalar_chain η e.val (φ ∘ e.val.symm) hψ hH).1
  rw [formula γ he hφ, formula δ (hb ▸ he) (hb ▸ hφ), hb, ha]

end HolomorphicAnosov.Ghys
