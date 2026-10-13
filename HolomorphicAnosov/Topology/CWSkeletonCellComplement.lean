import Mathlib.Topology.CWComplex.Classical.Subcomplex

/-!
# The complement of a top cell in its skeleton

Source: Fritsch–Piccinini, Cellular Structures in Topology (1990), proof of
Lemma 2.3.7, p.67: the mapping cone is attached to `Xⁿ \ e` with its inherited
CW structure. Proposition 1.4.4, p.35, proof (iii) implies (i), proves the
closed-cell criterion used here to verify that inherited subcomplex.
-/

open Set _root_.Topology

namespace HolomorphicAnosov

/-- Removing an `n`-dimensional open cell from the `n`-skeleton leaves a subcomplex
on the original topology. Source: Fritsch–Piccinini, Lemma 2.3.7, p.67,
with Proposition 1.4.4, p.35, proof (iii) implies (i).

Select every cell of dimension at most `n` except the prescribed cell. Their open
cells are exactly the stated complement, by the disjoint open-cell partition.
The frontier of every selected cell lies in strictly lower-dimensional cells,
which are also selected. Thus each selected closed cell stays in the union.
Mathlib's closed-cell subcomplex constructor supplies its inherited topology.
No restriction is made on higher-dimensional cells, whose boundaries may meet
the removed open cell; the assertion is specifically about its skeleton. -/
theorem cw_skeleton_cell_complement
    {X : Type*} [TopologicalSpace X] [T2Space X]
    {C : Set X} [CWComplex C] (n : ℕ) (i : RelCWComplex.cell C n) :
    ∃ A : CWComplex.Subcomplex C,
      (A : Set X) = (CWComplex.skeleton C n : Set X) \ CWComplex.openCell n i := by
  classical
  let I : (m : ℕ) → Set (RelCWComplex.cell C m) :=
    fun m ↦ {j | m ≤ n ∧ (⟨m, j⟩ : Σ k, RelCWComplex.cell C k) ≠ ⟨n, i⟩}
  let E := ⋃ (m : ℕ) (j : I m), CWComplex.openCell m j.val
  have hclosed : ∀ m (j : I m), CWComplex.closedCell m j.val ⊆ E := by
    intro m j x hx
    rw [← CWComplex.cellFrontier_union_openCell_eq_closedCell] at hx
    rcases hx with hx | hx
    · obtain ⟨J, hJ⟩ := CWComplex.cellFrontier_subset_finite_openCell m j.val
      have hxJ := hJ hx
      simp only [mem_iUnion, exists_prop] at hxJ
      obtain ⟨k, hkm, l, hl, hxl⟩ := hxJ
      have hkn : k < n := hkm.trans_le j.property.1
      have hne : (⟨k, l⟩ : Σ t, RelCWComplex.cell C t) ≠ ⟨n, i⟩ := by
        intro heq
        have := congrArg Sigma.fst heq
        exact (Nat.ne_of_lt hkn) this
      exact mem_iUnion.mpr ⟨k, mem_iUnion.mpr ⟨⟨l, hkn.le, hne⟩, hxl⟩⟩
    · exact mem_iUnion.mpr ⟨m, mem_iUnion.mpr ⟨j, hx⟩⟩
  refine ⟨CWComplex.Subcomplex.mk' C E I hclosed rfl, ?_⟩
  change E = _
  ext x
  constructor
  · rintro hx
    obtain ⟨m, hm⟩ := mem_iUnion.mp hx
    obtain ⟨j, hxj⟩ := mem_iUnion.mp hm
    refine ⟨CWComplex.mem_skeleton_iff.mpr ⟨m, by exact_mod_cast j.property.1,
      j.val, hxj⟩, ?_⟩
    exact (CWComplex.disjoint_openCell_of_ne j.property.2).notMem_of_mem_left hxj
  · rintro ⟨hx, hxi⟩
    obtain ⟨m, hmn, j, hxj⟩ := CWComplex.mem_skeleton_iff.mp hx
    have hne : (⟨m, j⟩ : Σ k, RelCWComplex.cell C k) ≠ ⟨n, i⟩ := by
      intro heq
      cases heq
      exact hxi hxj
    exact mem_iUnion.mpr ⟨m, mem_iUnion.mpr
      ⟨⟨j, by exact ⟨by exact_mod_cast hmn, hne⟩⟩, hxj⟩⟩

end HolomorphicAnosov
