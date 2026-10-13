import Mathlib.Topology.Subpath

/-!
# Finite path subdivision subordinate to an open cover

This file constructs a finite subdivision of a path subordinate to an open cover. (Hatcher, Lemma 1.15)
-/

namespace HolomorphicAnosov

universe u v

/-- Every continuous path admits a finite monotone subdivision whose closed subpaths lie in assigned members of any open cover of its image. (Hatcher, Lemma 1.15; Zhang, p. 14) -/
theorem exists_openCover_pathSubdivision
    {X : Type u} [TopologicalSpace X] {x y : X} {ι : Type v}
    (γ : Path x y) (U : ι → Set X) (hU : ∀ i, IsOpen (U i))
    (hcover : ∀ t : unitInterval, ∃ i, γ t ∈ U i) :
    ∃ n : ℕ, 0 < n ∧ ∃ t : Fin (n + 1) → unitInterval,
      t 0 = 0 ∧ t (Fin.last n) = 1 ∧ Monotone t ∧
        ∃ assigned : Fin n → ι, ∀ j : Fin n,
          Set.range (γ.subpath (t j.castSucc) (t j.succ)) ⊆ U (assigned j) := by
  classical
  let c : ι → Set unitInterval := fun i ↦ γ ⁻¹' U i
  have hc : ∀ i, IsOpen (c i) := fun i ↦ (hU i).preimage γ.continuous
  have hcov : Set.univ ⊆ ⋃ i, c i := by
    intro t _
    obtain ⟨i, hi⟩ := hcover t
    exact Set.mem_iUnion.mpr ⟨i, hi⟩
  obtain ⟨s, hs0, hsmono, ⟨n, hsn⟩, hsub⟩ :=
    exists_monotone_Icc_subset_open_cover_unitInterval hc hcov
  have hn : 0 < n := by
    by_contra h
    have he : n = 0 := Nat.eq_zero_of_not_pos h
    have hs1 := hsn 0 (by omega)
    rw [hs0] at hs1
    exact zero_ne_one hs1
  let t : Fin (n + 1) → unitInterval := fun j ↦ s j.val
  choose assigned hassigned using hsub
  refine ⟨n, hn, t, hs0, hsn n le_rfl, ?_, fun j ↦ assigned j.val, ?_⟩
  · intro i j hij
    exact hsmono hij
  · intro j
    rw [γ.range_subpath_of_le (t j.castSucc) (t j.succ) (hsmono (Nat.le_succ j.val))]
    rintro z ⟨u, hu, rfl⟩
    exact hassigned j.val hu


end HolomorphicAnosov
