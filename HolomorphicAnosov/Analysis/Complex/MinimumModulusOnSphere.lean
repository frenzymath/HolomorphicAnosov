import Mathlib.Analysis.Complex.AbsMax

/-!
# Minimum modulus on the boundary of a disk

Source: McMullen, *Complex Analysis*, author notes dated January 22, 2017,
Corollaries 1.10–1.11, printed p.9, maximum principle. The reciprocal application
is an agent-written expansion for the finite-limit step in Lyubich §4.4,
Theorem 4.12, pp.113–114.
-/

open Set Metric

namespace HolomorphicAnosov

/-- A nonvanishing function holomorphic on a disk and continuous on its closed
 disk takes a boundary value whose modulus is at most its modulus at the center.

Source: McMullen Corollaries 1.10–1.11, p.9, applied to the reciprocal. This
reciprocal application fills a step of `analysis.normalized_univalent_compactness`;
it is an agent-written alternative to the source's winding argument.

Proof: Nonvanishing on the entire closed disk makes the reciprocal holomorphic
on the open disk and continuous on its closure. The maximum-modulus theorem
supplies a point on the boundary sphere where the reciprocal norm is at least
its norm at the center. Both original norms are positive, so reversing the
reciprocal inequality proves the desired bound. Positive radius ensures that
the center lies in the disk and identifies its frontier with the sphere.
No boundary differentiability or injectivity is required. -/
theorem minimum_modulus_on_sphere (a : ℂ) (r : ℝ) (hr : 0 < r) (f : ℂ → ℂ)
    (hf : DiffContOnCl ℂ f (ball a r))
    (hne : ∀ z ∈ closedBall a r, f z ≠ 0) :
    ∃ z ∈ sphere a r, ‖f z‖ ≤ ‖f a‖ := by
  have hinv : DiffContOnCl ℂ (fun z ↦ (f z)⁻¹) (ball a r) :=
    hf.inv (fun z hz ↦ hne z (closure_ball_subset_closedBall hz))
  obtain ⟨z, hz, hmax⟩ := Complex.exists_mem_frontier_isMaxOn_norm
    isBounded_ball ⟨a, mem_ball_self hr⟩ hinv
  have hzs : z ∈ sphere a r := by rwa [frontier_ball a (ne_of_gt hr)] at hz
  have hle := hmax (subset_closure (mem_ball_self hr))
  simp only [Function.comp_apply, norm_inv] at hle
  exact ⟨z, hzs, (inv_le_inv₀ (norm_pos_iff.mpr (hne a (mem_closedBall_self hr.le)))
    (norm_pos_iff.mpr (hne z (sphere_subset_closedBall hzs)))).mp hle⟩


end HolomorphicAnosov

