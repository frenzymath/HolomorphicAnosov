import HolomorphicAnosov.Dynamics.Bowen.BowenBasicSetMarkovCoding

namespace HolomorphicAnosov

open Set

/-- The exact all-integer itinerary singleton clause of a retained Bowen coding tuple
implies integer covariance, including genuine inverse iterates. Source: Bowen
Theorem 28 p.742; Manning Lemma 6 Steps 2–3. Translate the same legal code, check that
F^k of its image belongs to every translated rectangle, then use singleton uniqueness. -/
theorem coding_integer_covariance
    {N : ℕ} {X : Type*} [TopologicalSpace X] (F : X ≃ₜ X)
    (B : Fin N → Fin N → Prop) (R : Fin N → Set X)
    (coding : BowenBasicSetCoding.CodeSpace B → X)
    (hcode : ∀ a, {x : X | ∀ j : ℤ, (F ^ j) x ∈ R (a.val j)} = {coding a})
    (a : BowenBasicSetCoding.CodeSpace B) (k : ℤ) :
    let b : BowenBasicSetCoding.CodeSpace B :=
      ⟨SymbolicDynamics.FullShift.shift k a.val, fun j ↦ by
        simpa only [SymbolicDynamics.FullShift.shift_apply, add_assoc] using a.property (k + j)⟩
    coding b = (F ^ k) (coding a) := by
  dsimp only
  let b : BowenBasicSetCoding.CodeSpace B :=
    ⟨SymbolicDynamics.FullShift.shift k a.val, fun j ↦ by
      simpa only [SymbolicDynamics.FullShift.shift_apply, add_assoc] using a.property (k + j)⟩
  have hc : ∀ j : ℤ, (F ^ j) (coding a) ∈ R (a.val j) := by
    have hm : coding a ∈ ({coding a} : Set X) := mem_singleton _
    rw [← hcode a] at hm
    exact hm
  have htarget : (F ^ k) (coding a) ∈ {x : X | ∀ j : ℤ, (F ^ j) x ∈ R (b.val j)} := by
    intro j
    have hp : (F ^ j) ((F ^ k) (coding a)) = (F ^ (k + j)) (coding a) := by
      rw [← Homeomorph.mul_apply, ← zpow_add]
      congr 2
      omega
    rw [hp]
    exact hc (k + j)
  rw [hcode b] at htarget
  exact (mem_singleton_iff.mp htarget).symm

end HolomorphicAnosov
