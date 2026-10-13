import HolomorphicAnosov.Ghys.AffineSchwarzianQuadraticForm
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# Scalar complex Schwarzian chain rule

DAG node: `analysis.schwarzian_chain_rule`.
Source: Dummit, *Dynamics, Chaos, and Fractals*, part 2 (2015), §2.2.1 p.11,
for the displayed derivative expansion and rational cancellation. His real-context
calculation is used only as commutative-field algebra: every derivative here is over
`ℂ` and follows from Mathlib's complex composition and product rules.
-/

noncomputable section
open Set Filter Topology _root_.Topology

namespace HolomorphicAnosov.Analysis.Complex
open HolomorphicAnosov.Ghys

/-- The Schwarzian chain rule on open holomorphic domains.

Source: Dummit, *Dynamics, Chaos, and Fractals*, part 2 (2015), §2.2.1 p.11.
Complex holomorphic derivative closure and the complex chain and product rules give,
with `fᵢ = F⁽ⁱ⁾(z)` and `gᵢ = G⁽ⁱ⁾(F z)`, the three derivatives of `G ∘ F`:
`g₁ f₁`, `g₂ f₁² + g₁ f₂`, and `g₃ f₁³ + 3 g₂ f₁ f₂ + g₁ f₃`.
These formulas hold throughout the original open domain, so they may be differentiated
again there. Substitute them in the definition of the Schwarzian. The product of
first derivatives is nonzero by the two explicit hypotheses. Clearing denominators
and cancelling the mixed terms gives exactly the displayed identity. No statement
about real derivatives is transported to the complex field. Empty domains are vacuous;
no global injectivity, connectedness, or nonvanishing away from `z` is needed. -/
theorem schwarzian_chain_rule
    {S T : Set ℂ} {F G : ℂ → ℂ}
    (hS : IsOpen S) (hT : IsOpen T)
    (hF : DifferentiableOn ℂ F S) (hG : DifferentiableOn ℂ G T)
    (hmap : MapsTo F S T) {z : ℂ} (hz : z ∈ S)
    (hf : deriv F z ≠ 0) (hg : deriv G (F z) ≠ 0) :
    schwarzian (G ∘ F) z =
      schwarzian F z + schwarzian G (F z) * deriv F z ^ 2 := by
  have hF₁ := hF.deriv hS
  have hF₂ := hF₁.deriv hS
  have hG₁ := hG.deriv hT
  have hG₂ := hG₁.deriv hT
  have D₁ : ∀ w ∈ S, deriv (G ∘ F) w = deriv G (F w) * deriv F w := by
    intro w hw
    exact (((hG (F w) (hmap hw)).differentiableAt (hT.mem_nhds (hmap hw))).hasDerivAt.comp w
      ((hF w hw).differentiableAt (hS.mem_nhds hw)).hasDerivAt).deriv
  have D₂ : ∀ w ∈ S, deriv (deriv (G ∘ F)) w =
      deriv (deriv G) (F w) * deriv F w ^ 2 + deriv G (F w) * deriv (deriv F) w := by
    intro w hw
    have df := ((hF w hw).differentiableAt (hS.mem_nhds hw)).hasDerivAt
    have df₁ := ((hF₁ w hw).differentiableAt (hS.mem_nhds hw)).hasDerivAt
    have dg₁ := ((hG₁ (F w) (hmap hw)).differentiableAt
      (hT.mem_nhds (hmap hw))).hasDerivAt
    have heq : deriv (G ∘ F) =ᶠ[𝓝 w] fun t ↦ deriv G (F t) * deriv F t :=
      Filter.Eventually.mono (hS.mem_nhds hw) (fun t ht ↦ D₁ t ht)
    rw [heq.deriv_eq]
    convert ((dg₁.comp w df).fun_mul df₁).deriv using 1 <;> simp [pow_two]; ring
  have df := ((hF z hz).differentiableAt (hS.mem_nhds hz)).hasDerivAt
  have df₁ := ((hF₁ z hz).differentiableAt (hS.mem_nhds hz)).hasDerivAt
  have df₂ := ((hF₂ z hz).differentiableAt (hS.mem_nhds hz)).hasDerivAt
  have dg₁ := ((hG₁ (F z) (hmap hz)).differentiableAt
    (hT.mem_nhds (hmap hz))).hasDerivAt
  have dg₂ := ((hG₂ (F z) (hmap hz)).differentiableAt
    (hT.mem_nhds (hmap hz))).hasDerivAt
  have D₃ : deriv (deriv (deriv (G ∘ F))) z =
      deriv (deriv (deriv G)) (F z) * deriv F z ^ 3 +
      3 * deriv (deriv G) (F z) * deriv F z * deriv (deriv F) z +
      deriv G (F z) * deriv (deriv (deriv F)) z := by
    have heq : deriv (deriv (G ∘ F)) =ᶠ[𝓝 z] fun t ↦
        deriv (deriv G) (F t) * deriv F t ^ 2 + deriv G (F t) * deriv (deriv F) t :=
      Filter.Eventually.mono (hS.mem_nhds hz) (fun t ht ↦ D₂ t ht)
    rw [heq.deriv_eq]
    convert (((dg₂.comp z df).fun_mul (df₁.pow 2)).fun_add
      ((dg₁.comp z df).fun_mul df₂)).deriv using 1 <;>
      simp [pow_two]; ring
  unfold schwarzian
  rw [D₃, D₂ z hz, D₁ z hz]
  field_simp [hf, hg]
  ring

end HolomorphicAnosov.Analysis.Complex
