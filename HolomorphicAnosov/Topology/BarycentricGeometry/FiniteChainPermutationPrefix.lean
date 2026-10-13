import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Card

/-!
# Extending a finite chain of subsets to permutation prefixes

Source: Schultz, Mathematics 246A §I.2, Proposition 3 proof, p.23.
The source extends a chain of faces to a full flag. The sorting construction
below is an agent-written expansion of that finite combinatorial step.
-/

open scoped Classical
namespace HolomorphicAnosov.BarycentricGeometry

/-- Any finite nested family of nonempty subsets of `Fin m` occurs among the
nonempty prefixes of one permutation. Source: Schultz, Mathematics 246A §I.2,
Proposition 3 proof p.23; the explicit sorting proof is agent-written.

Assign to each vertex the number of chain members omitting it and sort by that
number. If `i` belongs to a face `F` but `j` does not, every chain member omitting
`i` also omits `j`, and `F` contributes an additional omission of `j`. Thus the
omission number of `i` is strictly smaller. Each face is consequently an initial
segment of the sorted vertices; its nonempty inverse image has a largest index,
which gives the required prefix. The empty family and `m=0` are allowed. -/
theorem finite_chain_exists_permutation_prefix
    (m : ℕ) (C : Finset (Finset (Fin m)))
    (hne : ∀ F ∈ C, F.Nonempty)
    (hchain : ∀ F ∈ C, ∀ G ∈ C, F ⊆ G ∨ G ⊆ F) :
    ∃ σ : Equiv.Perm (Fin m), ∀ F ∈ C, ∃ k : Fin m,
      F = (Finset.univ.filter (fun j ↦ j ≤ k)).image σ := by
  classical
  let w : Fin m → ℕ := fun i ↦ (C.filter (fun F ↦ i ∉ F)).card
  let σ := Tuple.sort w
  have hsort : Monotone (w ∘ σ) := Tuple.monotone_sort w
  have hsep : ∀ F ∈ C, ∀ i ∈ F, ∀ j, j ∉ F → w i < w j := by
    intro F hF i hi j hj
    apply Finset.card_lt_card
    refine Finset.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩
    · intro G hG
      obtain ⟨hGC, hiG⟩ := Finset.mem_filter.mp hG
      refine Finset.mem_filter.mpr ⟨hGC, ?_⟩
      intro hjG
      rcases hchain F hF G hGC with hFG | hGF
      · exact hiG (hFG hi)
      · exact hj (hGF hjG)
    · intro heq
      have hFj : F ∈ C.filter (fun G ↦ j ∉ G) := Finset.mem_filter.mpr ⟨hF, hj⟩
      have hFi := heq.symm ▸ hFj
      exact (Finset.mem_filter.mp hFi).2 hi
  refine ⟨σ, ?_⟩
  intro F hF
  let T := F.image σ.symm
  have hT : T.Nonempty := (hne F hF).image _
  let k := T.max' hT
  have hkT : k ∈ T := T.max'_mem hT
  have hkF : σ k ∈ F := by
    obtain ⟨i, hi, heq⟩ := Finset.mem_image.mp hkT
    simpa only [← heq, σ.apply_symm_apply] using hi
  refine ⟨k, ?_⟩
  ext i
  constructor
  · intro hi
    refine Finset.mem_image.mpr ⟨σ.symm i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩,
      σ.apply_symm_apply i⟩
    exact T.le_max' _ (Finset.mem_image.mpr ⟨i, hi, rfl⟩)
  · intro hi
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
    by_contra hjF
    exact (not_lt_of_ge (hsort (Finset.mem_filter.mp hj).2)) (hsep F hF (σ k) hkF (σ j) hjF)

end HolomorphicAnosov.BarycentricGeometry
