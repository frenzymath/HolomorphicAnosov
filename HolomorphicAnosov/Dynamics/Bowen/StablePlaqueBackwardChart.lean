import HolomorphicAnosov.Dynamics.ProperRelativeMarkovPartitionG7
import Mathlib.Topology.Homeomorph.Lemmas
import Lean.Elab.Tactic.Omega

/-!
# Backward transport on strict stable-plaque germs

Bowen, *Markov Partitions and Minimal Sets for Axiom A Diffeomorphisms*
(1970), Lemma 2, pp. 908–909, transports stable germs by arbitrary integer
iterates. The finite-collar calculation below supplies the negative-time
part explicitly. It uses the original closed orbit plaques, including time
zero, and does not require connectedness or a manifold structure.
-/

namespace HolomorphicAnosov.Dynamics.Bowen

open Set

/-- A finite backward iterate restricts to a homeomorphism between relatively
open neighborhoods in the full stable plaques at the two orbit points.
The domains are obtained by imposing strict bounds at the finitely many
intermediate orbit times. Beyond these times the source plaque supplies all
remaining bounds. This expands the finite-iterate germ transport used in
Bowen 1970b, Lemma 2, p. 909; it asserts no global plaque invariance. -/
theorem stablePlaqueBackwardChart
    {X : Type*} [MetricSpace X] (F : X ≃ₜ X) (γ : ℝ) (hγ : 0 < γ)
    (x : X) (n : ℕ) :
    ∃ O V : Set X,
      O ⊆ relativeClosedStablePlaque F γ x ∧
      V ⊆ relativeClosedStablePlaque F γ ((F ^ (-(n : ℤ))) x) ∧
      x ∈ O ∧ (F ^ (-(n : ℤ))) x ∈ V ∧
      IsOpen ((Subtype.val : relativeClosedStablePlaque F γ x → X) ⁻¹' O) ∧
      IsOpen ((Subtype.val :
        relativeClosedStablePlaque F γ ((F ^ (-(n : ℤ))) x) → X) ⁻¹' V) ∧
      ∃ e : O ≃ₜ V, ∀ z : O, (e z : X) = (F ^ (-(n : ℤ))) z := by
  have hiter (k : ℕ) (z : X) : (F : X → X)^[k] z = (F ^ (k : ℤ)) z := by
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [Function.iterate_succ_apply', ih, Nat.cast_add, Nat.cast_one,
        zpow_add_one, Homeomorph.mul_apply]
      exact congrArg (fun g : X ≃ₜ X ↦ g z) (Commute.self_pow F k).eq
  have hcomp (a b : ℤ) (z : X) : (F ^ a) ((F ^ b) z) = (F ^ (a + b)) z := by
    rw [zpow_add, Homeomorph.mul_apply]
  let C : Set X := {z | ∀ j : Fin (n + 1),
    dist ((F ^ (-(j.val : ℤ))) z) ((F ^ (-(j.val : ℤ))) x) < γ}
  let D : Set X := {z | ∀ j : Fin (n + 1),
    dist ((F ^ (j.val : ℤ)) z)
      ((F ^ (j.val : ℤ)) ((F ^ (-(n : ℤ))) x)) < γ}
  let O := relativeClosedStablePlaque F γ x ∩ C
  let V := relativeClosedStablePlaque F γ ((F ^ (-(n : ℤ))) x) ∩ D
  have hC : IsOpen C := by
    simp only [C, ofPred_forall]
    exact isOpen_iInter_of_finite fun j : Fin (n + 1) ↦
      isOpen_lt ((F ^ (-(j.val : ℤ))).continuous.dist continuous_const) continuous_const
  have hD : IsOpen D := by
    simp only [D, ofPred_forall]
    exact isOpen_iInter_of_finite fun j : Fin (n + 1) ↦
      isOpen_lt ((F ^ (j.val : ℤ)).continuous.dist continuous_const) continuous_const
  have heq (z : X) : z ∈ O ↔ (F ^ (-(n : ℤ))) z ∈ V := by
    constructor
    · rintro ⟨hz, hc⟩
      constructor
      · intro k
        simp only [hiter, hcomp]
        by_cases hk : n ≤ k
        · have hh := hz (k - n)
          simpa only [hiter, Nat.cast_sub hk, sub_eq_add_neg] using hh
        · have hj : n - k < n + 1 := by omega
          have hh := (hc ⟨n - k, hj⟩).le
          have he : -((n - k : ℕ) : ℤ) = (k : ℤ) + -(n : ℤ) := by omega
          simpa only [he] using hh
      · intro j
        have hj : j.val ≤ n := by omega
        have hh := hc ⟨n - j.val, by omega⟩
        have he : -((n - j.val : ℕ) : ℤ) = (j.val : ℤ) + -(n : ℤ) := by omega
        simpa only [hcomp, he] using hh
    · rintro ⟨hz, hd⟩
      constructor
      · intro k
        have hh := hz (k + n)
        simpa only [hiter, hcomp, Nat.cast_add, add_neg_cancel_right] using hh
      · intro j
        have hj : j.val ≤ n := by omega
        have hh := hd ⟨n - j.val, by omega⟩
        have he : ((n - j.val : ℕ) : ℤ) + -(n : ℤ) = -(j.val : ℤ) := by omega
        simpa only [hcomp, he] using hh
  have hx : x ∈ O := ⟨fun _ ↦ by simp [hγ.le], fun _ ↦ by simpa using hγ⟩
  refine ⟨O, V, inter_subset_left, inter_subset_left, hx, (heq x).mp hx, ?_, ?_,
    (F ^ (-(n : ℤ))).subtype heq, fun _ ↦ rfl⟩
  · have hh := hC.preimage
      (continuous_subtype_val : Continuous (Subtype.val : relativeClosedStablePlaque F γ x → X))
    simpa only [O, preimage_inter, Subtype.coe_preimage_self, univ_inter] using hh
  · have hh := hD.preimage (continuous_subtype_val : Continuous
      (Subtype.val : relativeClosedStablePlaque F γ ((F ^ (-(n : ℤ))) x) → X))
    simpa only [V, preimage_inter, Subtype.coe_preimage_self, univ_inter] using hh

end HolomorphicAnosov.Dynamics.Bowen

