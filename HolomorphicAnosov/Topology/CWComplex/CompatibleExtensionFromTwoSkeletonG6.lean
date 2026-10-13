import HolomorphicAnosov.Topology.CWComplex.HigherSkeletonExtensionG6

namespace HolomorphicAnosov
universe u v w

/-- A map on the original two-skeleton extends to a compatible family on all
finite skeleta when the target has a surjective contractible covering.

Source: Hatcher, Algebraic Topology, Proposition 1B.9 p.91. Recursively choose
successor extensions using higher-skeleton extension starting at dimension two.
On dimensions zero and one restrict the original two-skeleton map. Successor
agreement is immediate from the recursive choices and the restriction definitions;
induction along m ≤ n gives all the stated compatibility equalities. -/
theorem cw_compatible_extension_from_two_skeleton_g6
    {K : Type u} {Y : Type v} {E : Type w}
    [TopologicalSpace K] [TopologicalSpace Y] [TopologicalSpace E]
    [T2Space K] [Topology.CWComplex (Set.univ : Set K)] [ContractibleSpace E]
    (p : E → Y) (hp : IsCoveringMap p) (hsurj : Function.Surjective p)
    (f₂ : C((Topology.CWComplex.skeleton (Set.univ : Set K) (2 : ℕ∞) : Set K), Y)) :
    ∃ F : ∀ n : ℕ, C((Topology.CWComplex.skeleton
        (Set.univ : Set K) (n : ℕ∞) : Set K), Y),
      (∀ (m n : ℕ) (hmn : m ≤ n)
        (x : (Topology.CWComplex.skeleton (Set.univ : Set K) (m : ℕ∞) : Set K)),
        F m x = F n ⟨x.val, Topology.CWComplex.skeleton_mono
          (by exact_mod_cast hmn) x.property⟩) ∧ F 2 = f₂ := by
  classical
  let S (n : ℕ) : Set K := Topology.CWComplex.skeleton (Set.univ : Set K) (n : ℕ∞)
  let E (n : ℕ) := C(S n, Y)
  let step (n : ℕ) (f : E n) : E (n + 1) :=
    if hn : 2 ≤ n then (cw_higher_skeleton_extension_g6 p hp hsurj n hn f).choose
    else ⟨fun x ↦ f₂ ⟨x.val, Topology.CWComplex.skeleton_mono
      (by exact_mod_cast (show n + 1 ≤ 2 by omega)) x.property⟩,
      f₂.continuous.comp (continuous_subtype_val.subtype_mk _)⟩
  let F : ∀ n : ℕ, E n := fun n ↦ Nat.rec
    (⟨fun x ↦ f₂ ⟨x.val, Topology.CWComplex.skeleton_mono (by norm_num) x.property⟩,
      f₂.continuous.comp (continuous_subtype_val.subtype_mk _)⟩ : E 0) step n
  have htwo : F 2 = f₂ := by
    ext x
    rfl
  have hstep : ∀ (n : ℕ) (x : S n), F n x = F (n + 1)
      ⟨x.val, Topology.CWComplex.skeleton_mono
        (by exact_mod_cast Nat.le_succ n) x.property⟩ := by
    intro n x
    by_cases hn : 2 ≤ n
    · change F n x = step n (F n) _
      simp only [step, dite_eq_left hn]
      exact ((cw_higher_skeleton_extension_g6 p hp hsurj n hn (F n)).choose_spec x).symm
    · have hsmall : n = 0 ∨ n = 1 := by omega
      rcases hsmall with rfl | rfl <;> rfl
  refine ⟨F, ?_, htwo⟩
  intro m n hmn x
  induction n, hmn using Nat.le_induction with
  | base => rfl
  | succ n hmn ih =>
    exact ih.trans (hstep n ⟨x.val, Topology.CWComplex.skeleton_mono
      (by exact_mod_cast hmn) x.property⟩)

end HolomorphicAnosov
