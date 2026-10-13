import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Data.Finsupp.SMul
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Tauto
import Mathlib.Tactic.Convert
noncomputable section
open scoped BigOperators
namespace HolomorphicAnosov
/-- Signed occurrences of a finite formal sum with boundary one generator
can be paired by equal labels and opposite signs, with one positive fixed point.
Source: Hatcher, Algebraic Topology, Theorem 2A.1 proof, p.167.

Proof: Evaluate the sum at every label. Positive and negative occurrences have
matching cardinalities except at the distinguished label, which has one extra
positive occurrence. Choose that occurrence, remove it, and choose a bijection
between positive and negative occurrences in each label fibre. Their union
is a label-preserving bijection. Interchange its paired occurrences and fix the
removed one. This is an involution with the asserted unique fixed point. -/
theorem finiteSignedOccurrenceMatching {I A : Type*} [Fintype I]
    (label : I → A) (sign : I → ℤ) (target : A)
    (hsign : ∀ i, sign i = -1 ∨ sign i = 1)
    (hsum : (∑ i, sign i • Finsupp.single (label i) (1 : ℤ)) =
      Finsupp.single target (1 : ℤ)) :
    ∃ (d : I) (pair : I → I),
      sign d = 1 ∧ label d = target ∧ Function.Involutive pair ∧
      pair d = d ∧ (∀ i, i ≠ d → pair i ≠ i) ∧
      (∀ i, label (pair i) = label i) ∧
      (∀ i, i ≠ d → sign (pair i) = -sign i) := by
  classical
  have hcount (a : A) :
      (Fintype.card {i // label i = a ∧ sign i = 1} : ℤ) -
      Fintype.card {i // label i = a ∧ sign i = -1} =
      if a = target then 1 else 0 := by
    have he := congrArg (fun c : A →₀ ℤ ↦ c a) hsum
    simp only [Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul,
      Finsupp.single_apply] at he
    simp only [Fintype.card_subtype, Nat.cast_sum, Finset.card_eq_sum_ones]
    rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_sub_distrib]
    convert he using 1
    · apply Finset.sum_congr rfl
      intro i hi
      rcases hsign i with h | h <;> by_cases ha : label i = a <;> simp [h, ha]
    · by_cases h : a = target
      · simp [h]
      · simp [h, Ne.symm h]
  have hpositive : 0 < Fintype.card {i // label i = target ∧ sign i = 1} := by
    have := hcount target
    simp only [ite_true] at this
    omega
  obtain ⟨⟨d, hdlabel, hdsign⟩⟩ := Fintype.card_pos_iff.mp hpositive
  let P := {i : I // sign i = 1 ∧ i ≠ d}
  let N := {i : I // sign i = -1}
  have hbalance (a : A) :
      Fintype.card {i : P // label i.1 = a} =
      Fintype.card {i : N // label i.1 = a} := by
    change Fintype.card {i : {i : I // sign i = 1 ∧ i ≠ d} // label i.1 = a} =
      Fintype.card {i : {i : I // sign i = -1} // label i.1 = a}
    rw [Fintype.card_congr (Equiv.subtypeSubtypeEquivSubtypeInter
        (fun i : I ↦ sign i = 1 ∧ i ≠ d) (fun i ↦ label i = a)),
      Fintype.card_congr (Equiv.subtypeSubtypeEquivSubtypeInter
        (fun i : I ↦ sign i = -1) (fun i ↦ label i = a))]
    have hp : Finset.univ.filter (fun i ↦ (sign i = 1 ∧ i ≠ d) ∧ label i = a) =
        (Finset.univ.filter (fun i ↦ label i = a ∧ sign i = 1)).erase d := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
      tauto
    have hn : Finset.univ.filter (fun i ↦ sign i = -1 ∧ label i = a) =
        Finset.univ.filter (fun i ↦ label i = a ∧ sign i = -1) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      tauto
    simp only [Fintype.card_subtype]
    rw [hp, hn, Finset.card_erase_eq_ite]
    have h := hcount a
    simp only [Fintype.card_subtype] at h
    by_cases ha : a = target
    · subst a
      simp only [Finset.mem_filter, Finset.mem_univ, hdlabel, hdsign, and_self, ite_true]
      simp only [ite_true] at h
      omega
    · simp only [Finset.mem_filter, Finset.mem_univ, hdlabel, hdsign,
        Ne.symm ha, false_and, and_false, ite_false]
      simp only [ha, ite_false] at h
      omega
  let E (a : A) : {i : P // label i.1 = a} ≃ {i : N // label i.1 = a} :=
    Fintype.equivOfCardEq (hbalance a)
  let e : P ≃ N := Equiv.ofFiberEquiv E
  have he (i : P) : label (e i).1 = label i.1 := Equiv.ofFiberEquiv_map E i
  have he' (i : N) : label (e.symm i).1 = label i.1 := by
    simpa only [Equiv.apply_symm_apply] using (he (e.symm i)).symm
  let pair (i : I) : I := if hd : i = d then i else
    if hp : sign i = 1 then (e ⟨i, hp, hd⟩).1
    else (e.symm ⟨i, (hsign i).resolve_right hp⟩).1
  have hpairP (i : P) : pair i.1 = (e i).1 := by
    simp only [pair, dite_eq_right i.2.2, dite_eq_left i.2.1]
    rfl
  have hpairN (i : N) : pair i.1 = (e.symm i).1 := by
    have hd : i.1 ≠ d := by intro hi; have := i.2; rw [hi, hdsign] at this; omega
    have hp : ¬sign i.1 = 1 := by have := i.2; omega
    simp only [pair, dite_eq_right hd, dite_eq_right hp]
    rfl
  refine ⟨d, pair, hdsign, hdlabel, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    by_cases hd : i = d
    · subst i
      simp only [pair, dite_eq_left rfl]
    · rcases hsign i with hi | hi
      · change pair (pair (⟨i, hi⟩ : N).1) = i
        rw [hpairN, hpairP, Equiv.apply_symm_apply]
      · change pair (pair (⟨i, hi, hd⟩ : P).1) = i
        rw [hpairP, hpairN, Equiv.symm_apply_apply]
  · simp only [pair, dite_eq_left rfl]
  · intro i hd hfix
    rcases hsign i with hi | hi
    · have hpi := (e.symm (⟨i, hi⟩ : N)).2.1
      have hval := hpairN (⟨i, hi⟩ : N)
      rw [← hval, hfix, hi] at hpi
      omega
    · have hpi := (e (⟨i, hi, hd⟩ : P)).2
      have hval := hpairP (⟨i, hi, hd⟩ : P)
      rw [← hval, hfix, hi] at hpi
      omega
  · intro i
    by_cases hd : i = d
    · subst i
      simp only [pair, dite_eq_left rfl]
    · rcases hsign i with hi | hi
      · rw [hpairN (⟨i, hi⟩ : N)]
        exact he' _
      · rw [hpairP (⟨i, hi, hd⟩ : P)]
        exact he _
  · intro i hd
    rcases hsign i with hi | hi
    · rw [hpairN (⟨i, hi⟩ : N), (e.symm (⟨i, hi⟩ : N)).2.1, hi]
      norm_num
    · rw [hpairP (⟨i, hi, hd⟩ : P), (e (⟨i, hi, hd⟩ : P)).2, hi]
end HolomorphicAnosov
