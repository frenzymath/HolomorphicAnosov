import HolomorphicAnosov.Topology.SignedSingularCrossProduct

/-!
# Staircase recursion and its signs

Eilenberg–Mac Lane, *On the Groups H(Π,n), I* (1953), §5, p.65, equation (5.7),
partitions the signed shuffle by its first step. This file proves the exact finite
staircase partition and sign formula for the existing explicit grid paths. It
includes zero-degree smaller grids and uses no chain boundary theorem.
-/
noncomputable section
namespace HolomorphicAnosov.SignedSingularCrossProduct

/-- Prepend a horizontal step and shift the remaining path one unit right.
Source: EM1953 §5, proof of equation (5.7), p.65. -/
def prependHorizontal {p q : ℕ} (w : GridPath p q) : GridPath (p + 1) q :=
  fun k ↦ if h : k.val = 0 then (0, 0) else
    ((w ⟨k.val - 1, by omega⟩).1.succ, (w ⟨k.val - 1, by omega⟩).2)

/-- The shifted positive vertex evaluates to the corresponding old vertex. -/
theorem prependHorizontal_positive {p q : ℕ} (w : GridPath p q)
    (k : Fin (p + q + 1)) :
    prependHorizontal w ⟨k.val + 1, by omega⟩ = ((w k).1.succ, (w k).2) := by
  simp [prependHorizontal]

/-- Horizontal prepending preserves the inversion count. This is the positive
sign of the first term in EM1953 equation (5.7), p.65. -/
theorem inversionCount_prependHorizontal {p q : ℕ} (w : GridPath p q)
    (h0 : w 0 = (0, 0)) : inversionCount (prependHorizontal w) = inversionCount w := by
  classical
  unfold inversionCount
  symm
  apply Finset.card_bij (fun ij _ ↦
    ((⟨ij.1.val + 1, by omega⟩ : Fin (p + 1 + q)),
      (⟨ij.2.val + 1, by omega⟩ : Fin (p + 1 + q))))
  · intro ij hij
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hij ⊢
    rcases hij with ⟨hlt, hv, hh⟩
    dsimp
    simp only [prependHorizontal, Fin.val_succ,
      Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, dite_false,
      Nat.add_sub_cancel, Fin.val_succ]
    constructor
    · change ij.1.val + 1 < ij.2.val + 1
      exact Nat.add_lt_add_right hlt 1
    · constructor
      · exact hv
      · change (w ⟨ij.2.val + 1, _⟩).1.val = (w ⟨ij.2.val, _⟩).1.val + 1 at hh
        omega
  · intro ij hij kl hkl heq
    apply Prod.ext <;> apply Fin.ext
    · have h := congrArg (fun z : Fin (p + 1 + q) × Fin (p + 1 + q) ↦ z.1.val) heq
      dsimp only at h
      omega
    · have h := congrArg (fun z : Fin (p + 1 + q) × Fin (p + 1 + q) ↦ z.2.val) heq
      dsimp only at h
      omega
  · intro ij hij
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hij
    rcases hij with ⟨hlt, hv, hh⟩
    have hi : ij.1.val ≠ 0 := by
      intro hi
      have hzero : ij.1 = 0 := Fin.ext hi
      rw [hzero] at hv
      have ht : 1 < p + 1 + q + 1 := by omega
      simp [prependHorizontal, h0, Nat.mod_eq_of_lt ht] at hv
    have hj : ij.2.val ≠ 0 := by exact Nat.ne_zero_of_lt (lt_of_le_of_lt (Nat.zero_le _) hlt)
    refine ⟨(⟨ij.1.val - 1, by omega⟩, ⟨ij.2.val - 1, by omega⟩), ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      simp only [prependHorizontal, Fin.val_succ, Fin.val_castSucc,
        Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, dite_false,
        hi, hj, Nat.add_sub_cancel] at hv hh
      constructor
      · change ij.1.val - 1 < ij.2.val - 1
        change ij.1.val < ij.2.val at hlt
        omega
      · constructor
        · have he : (⟨ij.1.val - 1, by omega⟩ : Fin (p + q)).succ =
              (⟨ij.1.val, by omega⟩ : Fin (p + q + 1)) := by apply Fin.ext; dsimp; omega
          change (w (⟨ij.1.val - 1, _⟩ : Fin (p + q)).succ).2.val = _
          rw [he]
          exact hv
        · have he : (⟨ij.2.val - 1, by omega⟩ : Fin (p + q)).succ =
              (⟨ij.2.val, by omega⟩ : Fin (p + q + 1)) := by apply Fin.ext; dsimp; omega
          change (w (⟨ij.2.val - 1, _⟩ : Fin (p + q)).succ).1.val = _
          rw [he]
          exact Nat.add_right_cancel hh
    · apply Prod.ext <;> apply Fin.ext <;> dsimp <;> omega

/-- Horizontal prepending maps every staircase to a staircase. -/
theorem prependHorizontal_mem {p q : ℕ} (w : GridPath p q) (hw : w ∈ staircases p q) :
    prependHorizontal w ∈ staircases (p + 1) q := by
  classical
  simp only [staircases, Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
  rcases hw with ⟨h0, he, hs⟩
  refine ⟨?_, ?_, ?_⟩
  · simp [prependHorizontal]
  · have ht : p + 1 + q ≠ 0 := by omega
    simp only [prependHorizontal, Fin.val_last, ht, dite_false]
    have hf : (⟨p + 1 + q - 1, by omega⟩ : Fin (p + q + 1)) = Fin.last (p + q) := by
      apply Fin.ext; dsimp; omega
    rw [hf, he]
    rfl
  · intro i
    by_cases hi : i.val = 0
    · have ht : 1 < p + 1 + q + 1 := by omega
      have hz : i = 0 := Fin.ext hi
      rw [hz]
      simp [prependHorizontal, h0, Nat.mod_eq_of_lt ht]
    · have he : (⟨i.val - 1, by omega⟩ : Fin (p + q)).succ =
          (⟨i.val, by omega⟩ : Fin (p + q + 1)) := by apply Fin.ext; dsimp; omega
      have h := hs ⟨i.val - 1, by omega⟩
      rw [he] at h
      simp only [prependHorizontal, Fin.val_succ, Fin.val_castSucc, hi,
        Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, dite_false, Nat.add_sub_cancel]
      rcases h with ⟨ha, hb⟩ | ⟨ha, hb⟩
      · left
        constructor
        · exact congrArg (fun t ↦ t + 1) ha
        · exact hb
      · right
        constructor
        · exact congrArg Fin.succ ha
        · exact hb

/-- Horizontal prepending is injective: positive vertices recover every old vertex. -/
theorem prependHorizontal_injective {p q : ℕ} :
    Function.Injective (@prependHorizontal p q) := by
  intro w v h
  funext k
  have hh := congrFun h ⟨k.val + 1, by omega⟩
  rw [prependHorizontal_positive, prependHorizontal_positive] at hh
  apply Prod.ext
  · exact Fin.succ_injective _ (congrArg Prod.fst hh)
  · exact congrArg (fun z : Fin (p + 2) × Fin (q + 1) ↦ z.2) hh

/-- The coefficient of a horizontally prefixed staircase has no extra sign. -/
theorem orientation_prependHorizontal {p q : ℕ} (w : GridPath p q)
    (h0 : w 0 = (0, 0)) : orientation (prependHorizontal w) = orientation w := by
  simp only [orientation, inversionCount_prependHorizontal w h0]

/-- A monotone staircase has exactly p horizontal steps, including degenerate rows. -/
theorem horizontalSteps_card {p q : ℕ} (w : GridPath p q) (hw : w ∈ staircases p q) :
    (Finset.univ.filter (fun i : Fin (p + q) ↦
      (w i.succ).1.val = (w i.castSucc).1.val + 1)).card = p := by
  classical
  simp only [staircases, Finset.mem_filter, Finset.mem_univ, true_and] at hw
  rcases hw with ⟨h0, he, hs⟩
  have hsum : ∑ i : Fin (p + q),
      (if (w i.succ).1.val = (w i.castSucc).1.val + 1 then (1 : ℤ) else 0) =
      ∑ i : Fin (p + q), (((w i.succ).1.val : ℤ) - (w i.castSucc).1.val) := by
    apply Finset.sum_congr rfl
    intro i _
    rcases hs i with ⟨hi, _⟩ | ⟨hi, _⟩
    · rw [ite_eq_left hi, hi]
      push_cast
      omega
    · have hn : (w i.succ).1.val ≠ (w i.castSucc).1.val + 1 := by rw [hi]; omega
      rw [ite_eq_right hn, hi, sub_self]
  have htel : ∑ i : Fin (p + q), (((w i.succ).1.val : ℤ) - (w i.castSucc).1.val) = p := by
    rw [Finset.sum_sub_distrib]
    have ha := Fin.sum_univ_castSucc (fun k : Fin (p + q + 1) ↦ ((w k).1.val : ℤ))
    have hb := Fin.sum_univ_succ (fun k : Fin (p + q + 1) ↦ ((w k).1.val : ℤ))
    rw [he] at ha
    rw [h0] at hb
    dsimp at ha hb
    omega
  have hc := hsum.trans htel
  simpa only [Finset.sum_boole, Nat.cast_inj] using hc

/-- Prepend a vertical step and shift the remaining path one unit up.
Source: EM1953 §5, proof of equation (5.7), p.65. -/
def prependVertical {p q : ℕ} (w : GridPath p q) : GridPath p (q + 1) :=
  fun k ↦ if h : k.val = 0 then (0, 0) else
    ((w ⟨k.val - 1, by omega⟩).1, (w ⟨k.val - 1, by omega⟩).2.succ)

/-- Positive vertices recover the original path shifted up. -/
theorem prependVertical_positive {p q : ℕ} (w : GridPath p q)
    (k : Fin (p + q + 1)) :
    prependVertical w ⟨k.val + 1, by omega⟩ = ((w k).1, (w k).2.succ) := by
  simp [prependVertical]

/-- The inversions after the initial vertical step are the old inversions. -/
theorem prependVertical_tail_inversions {p q : ℕ} (w : GridPath p q) :
    ((Finset.univ.filter fun ij : Fin (p + (q + 1)) × Fin (p + (q + 1)) ↦
      ij.1 < ij.2 ∧
      (prependVertical w ij.1.succ).2.val =
        (prependVertical w ij.1.castSucc).2.val + 1 ∧
      (prependVertical w ij.2.succ).1.val =
        (prependVertical w ij.2.castSucc).1.val + 1).filter
      fun ij ↦ ¬ij.1.val = 0).card = inversionCount w := by
  classical
  unfold inversionCount
  symm
  apply Finset.card_bij (fun ij _ ↦
    ((⟨ij.1.val + 1, by omega⟩ : Fin (p + (q + 1))),
      (⟨ij.2.val + 1, by omega⟩ : Fin (p + (q + 1)))))
  · intro ij hij
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hij ⊢
    rcases hij with ⟨hlt, hv, hh⟩
    dsimp
    simp only [prependVertical, Fin.val_succ,
      Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, dite_false,
      Nat.add_sub_cancel, Fin.val_succ, not_false_eq_true, and_true]
    refine ⟨?_, ?_, hh⟩
    · change ij.1.val + 1 < ij.2.val + 1
      exact Nat.add_lt_add_right hlt 1
    · exact congrArg (fun n ↦ n + 1) hv
  · intro ij hij kl hkl heq
    apply Prod.ext <;> apply Fin.ext
    · have h := congrArg (fun z : Fin (p + (q + 1)) × Fin (p + (q + 1)) ↦ z.1.val) heq
      dsimp only at h
      omega
    · have h := congrArg (fun z : Fin (p + (q + 1)) × Fin (p + (q + 1)) ↦ z.2.val) heq
      dsimp only at h
      omega
  · intro ij hij
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hij
    rcases hij with ⟨⟨hlt, hv, hh⟩, hi⟩
    have hj : ij.2.val ≠ 0 := by
      change ij.1.val < ij.2.val at hlt
      omega
    refine ⟨(⟨ij.1.val - 1, by omega⟩, ⟨ij.2.val - 1, by omega⟩), ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      simp only [prependVertical, Fin.val_succ, Fin.val_castSucc,
        Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, dite_false,
        hi, hj, Nat.add_sub_cancel] at hv hh
      refine ⟨?_, ?_, ?_⟩
      · change ij.1.val - 1 < ij.2.val - 1
        change ij.1.val < ij.2.val at hlt
        omega
      · have he : (⟨ij.1.val - 1, by omega⟩ : Fin (p + q)).succ =
            (⟨ij.1.val, by omega⟩ : Fin (p + q + 1)) := by apply Fin.ext; dsimp; omega
        change (w (⟨ij.1.val - 1, _⟩ : Fin (p + q)).succ).2.val = _
        rw [he]
        exact Nat.add_right_cancel hv
      · have he : (⟨ij.2.val - 1, by omega⟩ : Fin (p + q)).succ =
            (⟨ij.2.val, by omega⟩ : Fin (p + q + 1)) := by apply Fin.ext; dsimp; omega
        change (w (⟨ij.2.val - 1, _⟩ : Fin (p + q)).succ).1.val = _
        rw [he]
        exact hh
    · apply Prod.ext <;> apply Fin.ext <;> dsimp <;> omega

/-- The initial vertical step contributes one inversion per horizontal step. -/
theorem prependVertical_head_inversions {p q : ℕ} (w : GridPath p q)
    (h0 : w 0 = (0, 0)) :
    ((Finset.univ.filter fun ij : Fin (p + (q + 1)) × Fin (p + (q + 1)) ↦
      ij.1 < ij.2 ∧
      (prependVertical w ij.1.succ).2.val =
        (prependVertical w ij.1.castSucc).2.val + 1 ∧
      (prependVertical w ij.2.succ).1.val =
        (prependVertical w ij.2.castSucc).1.val + 1).filter
      fun ij ↦ ij.1.val = 0).card =
      (Finset.univ.filter (fun i : Fin (p + q) ↦
        (w i.succ).1.val = (w i.castSucc).1.val + 1)).card := by
  classical
  symm
  apply Finset.card_bij (fun i _ ↦
    ((0 : Fin (p + (q + 1))), (⟨i.val + 1, by omega⟩ : Fin (p + (q + 1)))))
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    have ht : 1 < p + (q + 1) + 1 := by omega
    have hpos : (0 : Fin (p + (q + 1))) < ⟨i.val + 1, by omega⟩ := by
      change 0 < i.val + 1
      omega
    simp [prependVertical, h0, Nat.mod_eq_of_lt ht]
    exact ⟨hpos, hi⟩
  · intro i hi j hj heq
    apply Fin.ext
    have h := congrArg (fun z : Fin (p + (q + 1)) × Fin (p + (q + 1)) ↦ z.2.val) heq
    dsimp at h
    omega
  · intro ij hij
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hij
    rcases hij with ⟨⟨hlt, hv, hh⟩, hi⟩
    have hj : ij.2.val ≠ 0 := by
      change ij.1.val < ij.2.val at hlt
      omega
    refine ⟨⟨ij.2.val - 1, by omega⟩, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      simp only [prependVertical, Fin.val_succ, Fin.val_castSucc,
        Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, dite_false,
        hj, Nat.add_sub_cancel] at hh
      have he : (⟨ij.2.val - 1, by omega⟩ : Fin (p + q)).succ =
          (⟨ij.2.val, by omega⟩ : Fin (p + q + 1)) := by apply Fin.ext; dsimp; omega
      change (w (⟨ij.2.val - 1, _⟩ : Fin (p + q)).succ).1.val = _
      rw [he]
      exact hh
    · apply Prod.ext <;> apply Fin.ext <;> dsimp <;> omega

/-- Vertical prepending creates precisely p inversions. This gives the sign of the
second summand in EM1953 equation (5.7), p.65. -/
theorem inversionCount_prependVertical {p q : ℕ} (w : GridPath p q)
    (hw : w ∈ staircases p q) :
    inversionCount (prependVertical w) = p + inversionCount w := by
  classical
  have h0 : w 0 = (0, 0) := (Finset.mem_filter.mp hw).2.1
  have h := Finset.card_filter_add_card_filter_not
    (s := Finset.univ.filter fun ij : Fin (p + (q + 1)) × Fin (p + (q + 1)) ↦
      ij.1 < ij.2 ∧
      (prependVertical w ij.1.succ).2.val =
        (prependVertical w ij.1.castSucc).2.val + 1 ∧
      (prependVertical w ij.2.succ).1.val =
        (prependVertical w ij.2.castSucc).1.val + 1)
    (fun ij ↦ ij.1.val = 0)
  rw [prependVertical_head_inversions w h0, horizontalSteps_card w hw,
    prependVertical_tail_inversions w] at h
  exact h.symm

/-- A vertical prefix contributes the Koszul sign (-1)^p. -/
theorem orientation_prependVertical {p q : ℕ} (w : GridPath p q)
    (hw : w ∈ staircases p q) :
    orientation (prependVertical w) = (-1 : ℤ) ^ p * orientation w := by
  simp only [orientation, inversionCount_prependVertical w hw, pow_add]

/-- Vertical prepending maps every staircase to a staircase. -/
theorem prependVertical_mem {p q : ℕ} (w : GridPath p q) (hw : w ∈ staircases p q) :
    prependVertical w ∈ staircases p (q + 1) := by
  classical
  simp only [staircases, Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
  rcases hw with ⟨h0, he, hs⟩
  refine ⟨?_, ?_, ?_⟩
  · simp [prependVertical]
  · have ht : p + (q + 1) ≠ 0 := by omega
    simp only [prependVertical, Fin.val_last, ht, dite_false]
    have hf : (⟨p + (q + 1) - 1, by omega⟩ : Fin (p + q + 1)) = Fin.last (p + q) := by
      rfl
    rw [hf, he]
    rfl
  · intro i
    by_cases hi : i.val = 0
    · have ht : 1 < p + (q + 1) + 1 := by omega
      have hz : i = 0 := Fin.ext hi
      rw [hz]
      simp [prependVertical, h0, Nat.mod_eq_of_lt ht]
    · have he : (⟨i.val - 1, by omega⟩ : Fin (p + q)).succ =
          (⟨i.val, by omega⟩ : Fin (p + q + 1)) := by apply Fin.ext; dsimp; omega
      have h := hs ⟨i.val - 1, by omega⟩
      rw [he] at h
      simp only [prependVertical, Fin.val_succ, Fin.val_castSucc, hi,
        Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, dite_false, Nat.add_sub_cancel]
      rcases h with ⟨ha, hb⟩ | ⟨ha, hb⟩
      · left
        exact ⟨ha, congrArg Fin.succ hb⟩
      · right
        exact ⟨ha, congrArg (fun t ↦ t + 1) hb⟩

/-- Vertical prepending is injective: positive vertices recover every old vertex. -/
theorem prependVertical_injective {p q : ℕ} :
    Function.Injective (@prependVertical p q) := by
  intro w v h
  funext k
  have hh := congrFun h ⟨k.val + 1, by omega⟩
  rw [prependVertical_positive, prependVertical_positive] at hh
  apply Prod.ext
  · exact congrArg (fun z : Fin (p + 1) × Fin (q + 2) ↦ z.1) hh
  · exact Fin.succ_injective _ (congrArg Prod.snd hh)

/-- Every coordinate of a staircase is nondecreasing along the vertex order. -/
theorem staircase_coordinate_monotone {p q : ℕ} (w : GridPath p q)
    (hw : w ∈ staircases p q) :
    Monotone (fun k ↦ (w k).1.val) ∧ Monotone (fun k ↦ (w k).2.val) := by
  have hs := (Finset.mem_filter.mp hw).2.2.2
  constructor
  · apply Fin.monotone_iff_le_succ.mpr
    intro i
    rcases hs i with ⟨h, _⟩ | ⟨h, _⟩
    · omega
    · exact le_of_eq (congrArg Fin.val h).symm
  · apply Fin.monotone_iff_le_succ.mpr
    intro i
    rcases hs i with ⟨_, h⟩ | ⟨_, h⟩
    · exact le_of_eq (congrArg Fin.val h).symm
    · omega

/-- Remove the first vertex and shift all later vertices left. The inverse law
requires that the first step was horizontal. -/
def tailHorizontal {p q : ℕ} (w : GridPath (p + 1) q) : GridPath p q :=
  fun k ↦ (⟨(w ⟨k.val + 1, by omega⟩).1.val - 1, by
    have h := (w ⟨k.val + 1, by omega⟩).1.isLt
    omega⟩, (w ⟨k.val + 1, by omega⟩).2)

/-- A staircase whose first step is horizontal is recovered by horizontal prepending. -/
theorem prependHorizontal_tail {p q : ℕ} (w : GridPath (p + 1) q)
    (hw : w ∈ staircases (p + 1) q)
    (hfirst : w ⟨1, by omega⟩ = (⟨1, by omega⟩, 0)) :
    prependHorizontal (tailHorizontal w) = w := by
  have h0 := (Finset.mem_filter.mp hw).2.1
  have hm := (staircase_coordinate_monotone w hw).1
  funext k
  by_cases hk : k.val = 0
  · have he : k = 0 := Fin.ext hk
    rw [he]
    simpa [prependHorizontal] using h0.symm
  · have hpos : 1 ≤ (w k).1.val := by
      have h := hm (show (⟨1, by omega⟩ : Fin (p + 1 + q + 1)) ≤ k by
        change 1 ≤ k.val; omega)
      dsimp at h; rw [hfirst] at h
      exact h
    simp only [prependHorizontal, hk, dite_false, tailHorizontal]
    apply Prod.ext
    · apply Fin.ext
      dsimp
      have he : (⟨k.val - 1 + 1, by omega⟩ : Fin (p + 1 + q + 1)) = k := by
        apply Fin.ext; dsimp; omega
      rw [he]
      omega
    · have he : (⟨k.val - 1 + 1, by omega⟩ : Fin (p + 1 + q + 1)) = k := by
        apply Fin.ext; dsimp; omega
      exact congrArg (fun i ↦ (w i).2) he

/-- Removing a first horizontal step gives a staircase in the smaller grid. -/
theorem tailHorizontal_mem {p q : ℕ} (w : GridPath (p + 1) q)
    (hw : w ∈ staircases (p + 1) q)
    (hfirst : w ⟨1, by omega⟩ = (⟨1, by omega⟩, 0)) :
    tailHorizontal w ∈ staircases p q := by
  have hm := (staircase_coordinate_monotone w hw).1
  rcases (Finset.mem_filter.mp hw).2 with ⟨h0, he, hs⟩
  simp only [staircases, Finset.mem_filter, Finset.mem_univ, true_and]
  refine ⟨?_, ?_, ?_⟩
  · simp [tailHorizontal, hfirst]
  · have ht : (⟨p + q + 1, by omega⟩ : Fin (p + 1 + q + 1)) =
        Fin.last (p + 1 + q) := by apply Fin.ext; dsimp; omega
    simp only [tailHorizontal, Fin.val_last, ht, he]
    apply Prod.ext
    · apply Fin.ext
      simp
    · rfl
  · intro i
    have h := hs ⟨i.val + 1, by omega⟩
    have hpos : 1 ≤ (w ⟨i.val + 1, by omega⟩).1.val := by
      have hh := hm (show (⟨1, by omega⟩ : Fin (p + 1 + q + 1)) ≤
          ⟨i.val + 1, by omega⟩ by change 1 ≤ i.val + 1; omega)
      dsimp at hh; rw [hfirst] at hh
      exact hh
    simp only [tailHorizontal, Fin.val_succ, Fin.val_castSucc]
    rcases h with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · left
      constructor
      · change (w ⟨i.val + 1 + 1, _⟩).1.val = (w ⟨i.val + 1, _⟩).1.val + 1 at ha
        omega
      · exact hb
    · right
      constructor
      · apply Fin.ext
        exact congrArg (fun z ↦ z.val - 1) ha
      · exact hb

/-- Remove a first vertical step by shifting later vertices down. -/
def tailVertical {p q : ℕ} (w : GridPath p (q + 1)) : GridPath p q :=
  fun k ↦ ((w ⟨k.val + 1, by omega⟩).1, ⟨(w ⟨k.val + 1, by omega⟩).2.val - 1, by
    have h := (w ⟨k.val + 1, by omega⟩).2.isLt
    omega⟩)

/-- A staircase whose first step is vertical is recovered by vertical prepending. -/
theorem prependVertical_tail {p q : ℕ} (w : GridPath p (q + 1))
    (hw : w ∈ staircases p (q + 1))
    (hfirst : w ⟨1, by omega⟩ = (0, ⟨1, by omega⟩)) :
    prependVertical (tailVertical w) = w := by
  have h0 := (Finset.mem_filter.mp hw).2.1
  have hm := (staircase_coordinate_monotone w hw).2
  funext k
  by_cases hk : k.val = 0
  · have he : k = 0 := Fin.ext hk
    rw [he]
    simpa [prependVertical] using h0.symm
  · have hpos : 1 ≤ (w k).2.val := by
      have h := hm (show (⟨1, by omega⟩ : Fin (p + (q + 1) + 1)) ≤ k by
        change 1 ≤ k.val; omega)
      dsimp only at h
      rw [hfirst] at h
      exact h
    simp only [prependVertical, hk, dite_false, tailVertical]
    apply Prod.ext
    · have he : (⟨k.val - 1 + 1, by omega⟩ : Fin (p + (q + 1) + 1)) = k := by
        apply Fin.ext; dsimp; omega
      exact congrArg (fun i ↦ (w i).1) he
    · apply Fin.ext
      dsimp
      have he : (⟨k.val - 1 + 1, by omega⟩ : Fin (p + (q + 1) + 1)) = k := by
        apply Fin.ext; dsimp; omega
      rw [he]
      omega

/-- Removing a first vertical step gives a staircase in the smaller grid. -/
theorem tailVertical_mem {p q : ℕ} (w : GridPath p (q + 1))
    (hw : w ∈ staircases p (q + 1))
    (hfirst : w ⟨1, by omega⟩ = (0, ⟨1, by omega⟩)) :
    tailVertical w ∈ staircases p q := by
  have hm := (staircase_coordinate_monotone w hw).2
  rcases (Finset.mem_filter.mp hw).2 with ⟨h0, he, hs⟩
  simp only [staircases, Finset.mem_filter, Finset.mem_univ, true_and]
  refine ⟨?_, ?_, ?_⟩
  · simp only [tailVertical, Fin.val_zero, Nat.zero_add, hfirst]
    rfl
  · have ht : (⟨p + q + 1, by omega⟩ : Fin (p + (q + 1) + 1)) =
        Fin.last (p + (q + 1)) := by apply Fin.ext; dsimp; omega
    simp only [tailVertical, Fin.val_last, ht, he]
    apply Prod.ext
    · rfl
    · apply Fin.ext
      simp
  · intro i
    have h := hs ⟨i.val + 1, by omega⟩
    have hpos : 1 ≤ (w ⟨i.val + 1, by omega⟩).2.val := by
      have hh := hm (show (⟨1, by omega⟩ : Fin (p + (q + 1) + 1)) ≤
          ⟨i.val + 1, by omega⟩ by change 1 ≤ i.val + 1; omega)
      dsimp only at hh
      rw [hfirst] at hh
      exact hh
    simp only [tailVertical, Fin.val_succ, Fin.val_castSucc]
    rcases h with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · left
      constructor
      · exact ha
      · apply Fin.ext
        exact congrArg (fun z ↦ z.val - 1) hb
    · right
      constructor
      · exact ha
      · change (w ⟨i.val + 1 + 1, _⟩).2.val = (w ⟨i.val + 1, _⟩).2.val + 1 at hb
        omega

/-- The first step partitions a positive grid into horizontal and vertical prefixes.
Source: EM1953 §5, equation (5.7), p.65. -/
theorem staircases_succ_succ (p q : ℕ) :
    staircases (p + 1) (q + 1) =
      (staircases p (q + 1)).image prependHorizontal ∪
      (staircases (p + 1) q).image prependVertical := by
  classical
  ext w
  constructor
  · intro hw
    rcases (Finset.mem_filter.mp hw).2 with ⟨h0, he, hs⟩
    have hf := hs 0
    have hf0 : (0 : Fin (p + 1 + (q + 1))).castSucc = 0 := rfl
    have hf1 : (0 : Fin (p + 1 + (q + 1))).succ =
        ⟨1, by omega⟩ := rfl
    rw [hf0, hf1, h0] at hf
    rcases hf with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · have hfirst : w ⟨1, by omega⟩ = (⟨1, by omega⟩, 0) := by
        apply Prod.ext
        · exact Fin.ext ha
        · exact hb
      exact Finset.mem_union_left _ (Finset.mem_image.mpr
        ⟨tailHorizontal w, tailHorizontal_mem w hw hfirst, prependHorizontal_tail w hw hfirst⟩)
    · have hfirst : w ⟨1, by omega⟩ = (0, ⟨1, by omega⟩) := by
        apply Prod.ext
        · exact ha
        · exact Fin.ext hb
      exact Finset.mem_union_right _ (Finset.mem_image.mpr
        ⟨tailVertical w, tailVertical_mem w hw hfirst, prependVertical_tail w hw hfirst⟩)
  · intro hw
    rcases Finset.mem_union.mp hw with hw | hw
    · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hw
      exact prependHorizontal_mem v hv
    · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hw
      exact prependVertical_mem v hv

/-- The two initial-step classes are disjoint. -/
theorem staircase_prefix_disjoint (p q : ℕ) :
    Disjoint ((staircases p (q + 1)).image prependHorizontal)
      ((staircases (p + 1) q).image prependVertical) := by
  classical
  apply Finset.disjoint_left.mpr
  intro w hh hv
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hh
  obtain ⟨b, hb, he⟩ := Finset.mem_image.mp hv
  have ha0 := (Finset.mem_filter.mp ha).2.1
  have hb0 := (Finset.mem_filter.mp hb).2.1
  have h := congrFun he ⟨1, by omega⟩
  have hh := prependHorizontal_positive a 0
  have hv := prependVertical_positive b 0
  dsimp only [Fin.val_zero, Nat.zero_add] at hh hv
  rw [hh, hv, ha0, hb0] at h
  have := congrArg (fun z : Fin (p + 2) × Fin (q + 2) ↦ z.1.val) h
  norm_num at this

/-- For each positive rectangular grid, its monotone staircases are the disjoint union of horizontal prefixes of the grid with one fewer horizontal step and vertical prefixes of the grid with one fewer vertical step. Horizontal prefixing preserves the inversion count, while vertical prefixing adds the number of horizontal steps. Consequently, for every function f from grid paths to an abelian group, its signed staircase sum is the horizontal-prefix signed sum plus (−1) to the horizontal degree times the vertical-prefix signed sum, exactly as in the first-step recursion (5.7).

Source and proof origin: Eilenberg–Mac Lane, On the Groups H(Π,n), I (1953), §5 explicit first-slot partition and sign count immediately preceding equation (5.7), p.65. Supplied original: literature/G2-EM1953-full-supplied.txt and corresponding PDF.

Proof: Prepend (0,0) and shift the old coordinates right or up. The initial, terminal and unit-step conditions show each construction maps staircases to staircases; evaluation at positive indices gives injectivity. Coordinate monotonicity follows from the two permitted unit steps. Removing the first vertex and subtracting one from the appropriate coordinate therefore preserves all staircase conditions when that coordinate of the first step is one, and reconstructs the original path. The first step is exactly one of horizontal or vertical, so these images cover all paths and are disjoint.

For a horizontal prefix, every inversion is a uniquely shifted old inversion, since the initial step cannot be vertical. For a vertical prefix, partition inversion pairs according to whether the first index is zero. Pairs with nonzero first index are uniquely shifted old inversions. Pairs with first index zero are in bijection with horizontal steps of the old path. Sum the first-coordinate successive differences: each horizontal step contributes one and each vertical step zero, and telescoping from first vertex to last vertex gives exactly the horizontal degree. Hence vertical prefixing adds that degree to the inversion count. Taking powers of −1 proves both sign laws.

Split the finite sum over the disjoint prefix images and reindex each sum through its injective prefix map. Apply the two orientation laws termwise and distribute the common vertical sign over the sum. All constructions allow a zero dimension in the smaller grids; the inversion bijections then have the corresponding empty domains. -/
theorem signed_staircase_sum_recursion (p q : ℕ) {M : Type*} [AddCommGroup M]
    (f : GridPath (p + 1) (q + 1) → M) :
    ∑ w ∈ staircases (p + 1) (q + 1), orientation w • f w =
      (∑ w ∈ staircases p (q + 1), orientation w • f (prependHorizontal w)) +
      (-1 : ℤ) ^ (p + 1) •
        ∑ w ∈ staircases (p + 1) q, orientation w • f (prependVertical w) := by
  classical
  rw [staircases_succ_succ, Finset.sum_union (staircase_prefix_disjoint p q)]
  rw [Finset.sum_image (fun a _ b _ h ↦ prependHorizontal_injective h),
    Finset.sum_image (fun a _ b _ h ↦ prependVertical_injective h)]
  congr 1
  · apply Finset.sum_congr rfl
    intro w hw
    rw [orientation_prependHorizontal w (Finset.mem_filter.mp hw).2.1]
  · rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro w hw
    rw [orientation_prependVertical w hw, mul_smul]
end HolomorphicAnosov.SignedSingularCrossProduct
