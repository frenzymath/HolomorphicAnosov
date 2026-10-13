import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Complex.AbsMax

/-!
# Limits of normalized holomorphic disk maps

Source: Conway, *Functions of One Complex Variable*, VII Lemma 4.3, pp.161–163,
the compact limit step, and VII §2, p.151, the holomorphic limit theorem.
-/

namespace HolomorphicAnosov

open Set Filter
open scoped Topology _root_.Topology

/-- Compact-uniform limits of holomorphic maps to the disk fixing a marked point
at zero are still holomorphic maps to the open disk, and their derivatives converge.

Source: Conway VII Lemma 4.3, pp.161–163. Compact-uniform convergence on the open
domain is locally uniform, so the Weierstrass theorem gives holomorphy and derivative
convergence. Pointwise convergence preserves the marked value and the bound by one.
If the limit had modulus one somewhere, the maximum modulus principle would make
its modulus constant on the connected domain. Its zero value at the marked point
contradicts that constant modulus. No injectivity or nonconstant-limit premise is needed. -/
theorem conway_normalized_disk_limit
    {U : Set ℂ} (hUopen : IsOpen U) (hUconn : IsPreconnected U)
    {a : ℂ} (ha : a ∈ U) {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ}
    (hhol : ∀ n, DifferentiableOn ℂ (F n) U)
    (hmaps : ∀ n, MapsTo (F n) U (Metric.ball (0 : ℂ) 1))
    (hzero : ∀ n, F n a = 0)
    (hlim : ∀ K : Set ℂ, K ⊆ U → IsCompact K →
      TendstoUniformlyOn F f atTop K) :
    DifferentiableOn ℂ f U ∧ MapsTo f U (Metric.ball (0 : ℂ) 1) ∧
      f a = 0 ∧ TendstoLocallyUniformlyOn (fun n ↦ deriv (F n)) (deriv f) atTop U := by
  have hloc : TendstoLocallyUniformlyOn F f atTop U :=
    (tendstoLocallyUniformlyOn_iff_forall_isCompact hUopen).mpr hlim
  have hevent : ∀ᶠ n in atTop, DifferentiableOn ℂ (F n) U := Eventually.of_forall hhol
  have hf := hloc.differentiableOn hevent hUopen
  have hfa : f a = 0 := tendsto_nhds_unique (hloc.tendsto_at ha)
    (by simpa only [hzero] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (0 : ℂ)) atTop (𝓝 0)))
  have hbound : ∀ z ∈ U, ‖f z‖ ≤ 1 := by
    intro z hz
    exact le_of_tendsto (hloc.tendsto_at hz).norm
      (Eventually.of_forall fun n ↦ (mem_ball_zero_iff.mp (hmaps n hz)).le)
  refine ⟨hf, ?_, hfa, hloc.deriv hevent hUopen⟩
  intro z hz
  rw [mem_ball_zero_iff]
  by_contra hlt
  have heq : ‖f z‖ = 1 := le_antisymm (hbound z hz) (le_of_not_gt hlt)
  have hmax : IsMaxOn (norm ∘ f) U z := by
    intro w hw
    change ‖f w‖ ≤ ‖f z‖
    rw [heq]
    exact hbound w hw
  have hconstant := Complex.norm_eqOn_of_isPreconnected_of_isMaxOn
    hUconn hUopen hf hz hmax ha
  simp [hfa, heq] at hconstant


end HolomorphicAnosov
