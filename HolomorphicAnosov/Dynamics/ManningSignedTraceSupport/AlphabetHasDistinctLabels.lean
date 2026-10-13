import Mathlib.Combinatorics.Enumerative.Composition
import Mathlib.Data.Fintype.Powerset
import Mathlib.LinearAlgebra.Matrix.Trace
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.Alphabet

namespace HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7

open Set
open scoped BigOperators Classical
noncomputable section

/-- Manning pp.217–219: a positive composition different from `(1)` stores at least two
  distinct labels. If it has two blocks, disjointness separates their chosen labels. If it has
  one block, its size must exceed one, so that block contains two labels. -/
theorem alphabet_has_distinct_labels {Λ : Type u} {N r : ℕ}
    (R : Fin N → Set Λ) (c : Composition (r + 1)) (hc : c.blocks ≠ [1])
    (s : Alphabet R c) :
    ∃ (k l : Fin c.length) (i j : Fin N), i ∈ s.val k ∧ j ∈ s.val l ∧ i ≠ j := by
  classical
  have hlen : 0 < c.length := c.length_pos_of_pos (Nat.succ_pos r)
  let k : Fin c.length := ⟨0, hlen⟩
  by_cases htwo : 1 < c.length
  · let l : Fin c.length := ⟨1, htwo⟩
    obtain ⟨i, hi⟩ := s.property.1 k
    obtain ⟨j, hj⟩ := s.property.1 l
    refine ⟨k, l, i, j, hi, hj, ?_⟩
    intro hij
    have hkl : k ≠ l := by intro h; have := congrArg Fin.val h; simp [k, l] at this
    exact Finset.disjoint_left.mp (s.property.2.2.1 k l hkl) hi (hij ▸ hj)
  · have hlenone : c.length = 1 := by omega
    have hsingle : c = Composition.single (r + 1) (Nat.succ_pos r) :=
      (Composition.eq_single_iff_length (Nat.succ_pos r)).mpr hlenone
    have hr : 1 < r + 1 := by
      by_contra h
      have heq : r + 1 = 1 := by omega
      apply hc
      rw [hsingle, Composition.single_blocks, heq]
    have hcard : 1 < (s.val k).card := by
      rw [s.property.2.1 k]
      have hk : c.blocksFun k = r + 1 := by
        subst c
        exact Composition.single_blocksFun _ _
      rwa [hk]
    obtain ⟨i, hi, j, hj, hij⟩ := Finset.one_lt_card.mp hcard
    exact ⟨k, k, i, j, hi, hj, hij⟩


end
end HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7
