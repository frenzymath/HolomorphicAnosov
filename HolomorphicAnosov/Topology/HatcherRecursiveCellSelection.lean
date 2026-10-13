import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Order.WellFounded

namespace HolomorphicAnosov

open Set

/-- Recursive selection of compatible maps on cells with strictly lower-dimensional boundaries.

Source: Hatcher, Algebraic Topology, Theorem A.7, printed p.526. Process cells by their
natural-number dimension. Select a cell precisely when every lower boundary cell is selected
and an extension with the required property exists, agreeing with all previously selected maps.
Choose one such extension. Well-founded recursion makes these choices for all cells. For two
selected cells of different dimensions the defining extension equation proves agreement. For
distinct selected cells of equal dimension, every intersection point is on the first boundary;
a lower boundary cell contains that point, is selected, and its value agrees with both chosen
maps. Thus choices made independently at one dimension still agree on all overlaps. The result
retains the exact selection criterion, so a later local argument can prove that a particular
small cell is selected by constructing one admissible extension. -/
theorem hatcher_recursive_cell_selection
    {X Y ι : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (A B : ι → Set X) (dim : ι → ℕ)
    (Q : ∀ i, C(A i, Y) → Prop)
    (hinter : ∀ i j, i ≠ j → dim j ≤ dim i → A i ∩ A j ⊆ B i)
    (hfaces : ∀ i x, x ∈ B i →
      ∃ k, dim k < dim i ∧ A k ⊆ B i ∧ x ∈ A k) :
    ∃ (J : Set ι) (f : ∀ i : J, C(A i.val, Y)),
      (∀ i : J, Q i.val (f i)) ∧
      (∀ (i j : J) x (hi : x ∈ A i.val) (hj : x ∈ A j.val),
        f i ⟨x, hi⟩ = f j ⟨x, hj⟩) ∧
      ∀ i, i ∈ J ↔
        (∀ k, dim k < dim i → A k ⊆ B i → k ∈ J) ∧
        ∃ g : C(A i, Y), Q i g ∧
          ∀ (k : J), dim k.val < dim i →
            ∀ x (hi : x ∈ A i) (hk : x ∈ A k.val),
              g ⟨x, hi⟩ = f k ⟨x, hk⟩ := by
  classical
  let M (i : ι) := Option C(A i, Y)
  let P (i : ι) (r : ∀ k, dim k < dim i → M k) : Prop :=
    (∀ k hk, A k ⊆ B i → ∃ g, r k hk = some g) ∧
    ∃ g : C(A i, Y), Q i g ∧
      ∀ k hk h, r k hk = some h →
        ∀ x (hi : x ∈ A i) (hk' : x ∈ A k), g ⟨x, hi⟩ = h ⟨x, hk'⟩
  let step (i : ι) (r : ∀ k, dim k < dim i → M k) : M i :=
    if h : P i r then some h.2.choose else none
  let o : ∀ i, M i := (measure dim).wf.fix step
  have ho (i : ι) : o i = step i (fun k _ ↦ o k) :=
    (measure dim).wf.fix_eq step i
  have hsome (i : ι) (g : C(A i, Y)) (hg : o i = some g) :
      (∀ k, dim k < dim i → A k ⊆ B i → ∃ h, o k = some h) ∧
      Q i g ∧
      ∀ k, dim k < dim i → ∀ h, o k = some h →
        ∀ x (hi : x ∈ A i) (hk : x ∈ A k), g ⟨x, hi⟩ = h ⟨x, hk⟩ := by
    rw [ho] at hg
    dsimp only [step] at hg
    split_ifs at hg with hp
    · have heq := Option.some.inj hg
      subst g
      exact ⟨hp.1, hp.2.choose_spec.1, hp.2.choose_spec.2⟩
  let J : Set ι := {i | ∃ g, o i = some g}
  let f (i : J) : C(A i.val, Y) := i.property.choose
  have hf (i : J) : o i.val = some (f i) := i.property.choose_spec
  refine ⟨J, f, ?_, ?_, ?_⟩
  · intro i
    exact (hsome i.val (f i) (hf i)).2.1
  · intro i j x hi hj
    by_cases heq : i = j
    · subst j
      rfl
    have hij : i.val ≠ j.val := fun h ↦ heq (Subtype.ext h)
    have hle (i j : J) (hij : i.val ≠ j.val) (hdim : dim j.val ≤ dim i.val)
        (hi : x ∈ A i.val) (hj : x ∈ A j.val) : f i ⟨x, hi⟩ = f j ⟨x, hj⟩ := by
      by_cases hlt : dim j.val < dim i.val
      · exact (hsome i.val (f i) (hf i)).2.2 j.val hlt (f j) (hf j) x hi hj
      · have hd : dim j.val = dim i.val := Nat.le_antisymm hdim (Nat.le_of_not_lt hlt)
        obtain ⟨k, hkdim, hkB, hxk⟩ :=
          hfaces i.val x (hinter i.val j.val hij hdim ⟨hi, hj⟩)
        obtain ⟨g, hg⟩ := (hsome i.val (f i) (hf i)).1 k hkdim hkB
        exact ((hsome i.val (f i) (hf i)).2.2 k hkdim g hg x hi hxk).trans
          ((hsome j.val (f j) (hf j)).2.2 k (hd ▸ hkdim) g hg x hj hxk).symm
    rcases le_total (dim j.val) (dim i.val) with h | h
    · exact hle i j hij h hi hj
    · exact (hle j i hij.symm h hj hi).symm
  · intro i
    constructor
    · intro hi
      have hp := hsome i (f ⟨i, hi⟩) (hf ⟨i, hi⟩)
      refine ⟨hp.1, f ⟨i, hi⟩, hp.2.1, ?_⟩
      intro k hk x hxi hxk
      exact hp.2.2 k.val hk (f k) (hf k) x hxi hxk
    · rintro ⟨hready, g, hQ, hgood⟩
      have hp : P i (fun k _ ↦ o k) := by
        refine ⟨hready, g, hQ, ?_⟩
        intro k hk h hh x hxi hxk
        have hkJ : k ∈ J := ⟨h, hh⟩
        have heq : f ⟨k, hkJ⟩ = h := Option.some.inj ((hf ⟨k, hkJ⟩).symm.trans hh)
        simpa only [heq] using hgood ⟨k, hkJ⟩ hk x hxi hxk
      refine ⟨hp.2.choose, ?_⟩
      rw [ho]
      exact dite_eq_left hp


end HolomorphicAnosov
