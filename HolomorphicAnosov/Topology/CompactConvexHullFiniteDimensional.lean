import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.Analysis.Convex.Join
import Mathlib.Analysis.Convex.Topology
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

open Set
namespace HolomorphicAnosov

/-- The ordinary convex hull of a compact set in a finite-dimensional real
vector space is compact.

Source: Cairns (1951), section 3 Case II, p.863, compact hull construction;
Carathéodory's convexity theorem in pinned Mathlib `Analysis.Convex.Caratheodory`.
For each n, build a compact subset C_n of the hull containing the hull of every
subset with at most n points: start with the empty set, then take the union of
the original compact set with its convex join with C_n. A convex join is the
continuous image of the product of the two compact sets and [0,1]. Removing one
point from a finite set proves the induction. Carathéodory reduces every hull
point to an affinely independent set, of size at most dim(E)+1. Thus the final
compact approximant equals the entire ordinary convex hull. -/
theorem isCompact_convexHull_finiteDimensional
    {E : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    {S : Set E} (hS : IsCompact S) : IsCompact (convexHull ℝ S) := by
  classical
  have hjoin {A B : Set E} (hA : IsCompact A) (hB : IsCompact B) :
      IsCompact (convexJoin ℝ A B) := by
    let f : (E × E) × ℝ → E := fun p ↦ (1-p.2) • p.1.1 + p.2 • p.1.2
    have hf : Continuous f := by fun_prop
    have heq : convexJoin ℝ A B = f '' ((A ×ˢ B) ×ˢ Icc (0 : ℝ) 1) := by
      ext z
      simp only [mem_convexJoin, mem_image, mem_prod]
      constructor
      · rintro ⟨a, ha, b, hb, hz⟩
        rw [segment_eq_image] at hz
        obtain ⟨t, ht, rfl⟩ := hz
        exact ⟨((a,b),t), ⟨⟨ha,hb⟩,ht⟩, rfl⟩
      · rintro ⟨⟨⟨a,b⟩,t⟩, ⟨⟨ha,hb⟩,ht⟩, rfl⟩
        refine ⟨a, ha, b, hb, ?_⟩
        rw [segment_eq_image]
        exact ⟨t, ht, rfl⟩
    rw [heq]
    exact ((hA.prod hB).prod isCompact_Icc).image hf
  have hiter : ∀ n : ℕ, ∃ C : Set E, IsCompact C ∧ C ⊆ convexHull ℝ S ∧
      ∀ t : Finset E, (t : Set E) ⊆ S → t.card ≤ n → convexHull ℝ (t : Set E) ⊆ C := by
    intro n
    induction n with
    | zero =>
      refine ⟨∅, isCompact_empty, empty_subset _, ?_⟩
      intro t ht hcard
      have he : t = ∅ := Finset.card_eq_zero.mp (Nat.eq_zero_of_le_zero hcard)
      simp [he]
    | succ n ih =>
      obtain ⟨C, hC, hCsub, hCcover⟩ := ih
      refine ⟨S ∪ convexJoin ℝ S C, hS.union (hjoin hS hC), ?_, ?_⟩
      · refine union_subset (subset_convexHull ℝ S) ?_
        rintro x hx
        obtain ⟨a, ha, b, hb, hx⟩ := mem_convexJoin.mp hx
        exact (convex_convexHull ℝ S).segment_subset
          (subset_convexHull ℝ S ha) (hCsub hb) hx
      · intro t ht hcard
        by_cases ht0 : t = ∅
        · simp [ht0]
        obtain ⟨a, ha⟩ := Finset.nonempty_iff_ne_empty.mpr ht0
        have htsub : (t.erase a : Set E) ⊆ S := fun z hz ↦ ht (Finset.mem_of_mem_erase hz)
        have htcard : (t.erase a).card ≤ n := by
          rw [Finset.card_erase_of_mem ha]
          omega
        by_cases herase : t.erase a = ∅
        · have he : t = {a} := by
            rw [← Finset.insert_erase ha, herase]
            rfl
          simpa [he] using (subset_union_left.trans' (singleton_subset_iff.mpr (ht ha)))
        · have htEq : (t : Set E) = insert a (t.erase a : Set E) := by
            exact_mod_cast (Finset.insert_erase ha).symm
          rw [htEq, convexHull_insert (Finset.coe_nonempty.mpr
            (Finset.nonempty_iff_ne_empty.mpr herase))]
          apply Subset.trans _ subset_union_right
          exact convexJoin_mono (singleton_subset_iff.mpr (ht ha))
            (hCcover _ htsub htcard)
  obtain ⟨C, hC, hCsub, hcover⟩ := hiter (Module.finrank ℝ E + 1)
  have hreverse : convexHull ℝ S ⊆ C := by
    intro x hx
    rw [convexHull_eq_union] at hx
    simp only [mem_iUnion] at hx
    obtain ⟨t, ht, hind, hxt⟩ := hx
    apply hcover t ht _ hxt
    have hcard := hind.card_le_finrank_succ
    have hdim := (vectorSpan ℝ (range ((↑) : t → E))).finrank_le
    simpa using hcard.trans (Nat.add_le_add_right hdim 1)
  exact (Subset.antisymm hreverse hCsub) ▸ hC

end HolomorphicAnosov
