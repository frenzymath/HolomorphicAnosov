import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.Analysis.Complex.Basic

namespace HolomorphicAnosov

/-- A complex linear functional dominated by the norm of a linear image
extends to a contraction on the ambient normed space of that image.

Source: Rudin, *Real and Complex Analysis*, third edition, Theorem 6.19,
printed p. 131, the passage from equation (5) to the L¹ extension before
equation (6), and the complex Hahn–Banach theorem.

Proof: domination forces the functional to vanish on the kernel of the map.
It therefore descends to the image, with norm at most one. Hahn–Banach
extends this bounded functional to the whole ambient space preserving its
norm. The extension agrees with the original functional on every image.
No injectivity, closedness, or density of the image is required. -/
theorem rudin_dominated_range_hahn_banach
    {E F : Type*} [AddCommGroup E] [Module ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    (J : E →ₗ[ℂ] F) (φ : E →ₗ[ℂ] ℂ)
    (hdom : ∀ x, ‖φ x‖ ≤ ‖J x‖) :
    ∃ T : F →L[ℂ] ℂ, ‖T‖ ≤ 1 ∧ ∀ x, T (J x) = φ x := by
  have hker : J.ker ≤ φ.ker := by
    intro x hx
    apply LinearMap.mem_ker.mpr
    apply norm_eq_zero.mp
    exact le_antisymm (by simpa [LinearMap.mem_ker.mp hx] using hdom x)
      (norm_nonneg _)
  let ψ : J.range →ₗ[ℂ] ℂ :=
    (J.ker.liftQ φ hker).comp J.quotKerEquivRange.symm.toLinearMap
  have hψ (x : E) : ψ ⟨J x, LinearMap.mem_range_self J x⟩ = φ x := by
    simp [ψ]
  have hbound (y : J.range) : ‖ψ y‖ ≤ 1 * ‖y‖ := by
    obtain ⟨x, hx⟩ := y.property
    have hy : y = ⟨J x, LinearMap.mem_range_self J x⟩ := Subtype.ext hx.symm
    rw [hy, hψ]
    simpa using hdom x
  let ψc : J.range →L[ℂ] ℂ := ψ.mkContinuous 1 hbound
  obtain ⟨T, hT, hnorm⟩ := exists_extension_norm_eq J.range ψc
  refine ⟨T, hnorm.trans_le (ψc.opNorm_le_bound zero_le_one hbound), ?_⟩
  intro x
  exact (hT ⟨J x, LinearMap.mem_range_self J x⟩).trans (hψ x)

end HolomorphicAnosov

