import HolomorphicAnosov.Dynamics.ProperRelativeMarkovPartitionG7
import HolomorphicAnosov.Dynamics.Bowen.StablePlaqueBackwardChart

/-!
# Integer transport of native stable-plaque germs

This is an agent-written inversion of the published backward-chart interface,
expanding the integer-iterate transport used in Bowen, Markov Partitions and
Minimal Sets for Axiom A Diffeomorphisms (1970), Lemma 2, pp. 908–909.
The domains may depend on both the basepoint and the integer iterate.
-/

namespace HolomorphicAnosov.Dynamics.Bowen
open Set

/-- Every integer iterate restricts to a homeomorphism of relatively open
neighborhoods in the native closed stable plaques at the two orbit points.
For nonpositive exponents use the backward chart. For positive exponents,
apply that chart at the forward image and invert it. No contraction or
compactness is needed, and no whole-plaque invariance is asserted. -/
theorem stablePlaqueIntegerChart
    {X : Type*} [MetricSpace X] (F : X ≃ₜ X) (γ : ℝ) (hγ : 0 < γ)
    (x : X) (n : ℤ) :
    ∃ O V : Set X,
      O ⊆ relativeClosedStablePlaque F γ x ∧
      V ⊆ relativeClosedStablePlaque F γ ((F ^ n) x) ∧
      x ∈ O ∧ (F ^ n) x ∈ V ∧
      IsOpen ((Subtype.val : relativeClosedStablePlaque F γ x → X) ⁻¹' O) ∧
      IsOpen ((Subtype.val : relativeClosedStablePlaque F γ ((F ^ n) x) → X) ⁻¹' V) ∧
      ∃ e : O ≃ₜ V, ∀ z : O, (e z : X) = (F ^ n) z := by
  cases n with
  | negSucc k =>
    have heq : -((k + 1 : ℕ) : ℤ) = Int.negSucc k := by omega
    rw [← heq]
    exact stablePlaqueBackwardChart F γ hγ x (k + 1)
  | ofNat k =>
    obtain ⟨O, V, hO, hV, hxO, hxV, hOopen, hVopen, e, he⟩ :=
      stablePlaqueBackwardChart F γ hγ ((F ^ (k : ℤ)) x) k
    have hbase : (F ^ (-(k : ℤ))) ((F ^ (k : ℤ)) x) = x := by
      rw [← Homeomorph.mul_apply, ← zpow_add, neg_add_cancel, zpow_zero,
        Homeomorph.one_apply]
    rw [hbase] at hV hxV hVopen
    refine ⟨V, O, hV, hO, hxV, hxO, hVopen, hOopen, e.symm, ?_⟩
    intro z
    have hh := congrArg (fun w : X ↦ (F ^ (k : ℤ)) w) (he (e.symm z))
    simp only [e.apply_symm_apply, ← Homeomorph.mul_apply, ← zpow_add,
      add_neg_cancel, zpow_zero, Homeomorph.one_apply] at hh
    exact hh.symm

end HolomorphicAnosov.Dynamics.Bowen

