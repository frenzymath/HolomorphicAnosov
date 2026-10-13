import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Lattice.Union
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Ring

namespace HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7

open Set
open scoped Classical
noncomputable section

/-- Manning's complement-pair cancellation on one periodic fibre. A partial
ordered family of shift-invariant blocks has a nonempty invariant complement;
appending that complement is legal and changes the trace sign. This is the
pairwise algebra in Manning 1971, pp. 218–219, before summing the pairs. -/
theorem invariant_complement_sign_pair {A : Type*} [Fintype A] [DecidableEq A]
    (g : A ≃ A) {k : ℕ} (S : Fin k → Finset A)
    (hS : ∀ i, (S i).image g = S i)
    (hproper : (Finset.univ.biUnion S) ≠ Finset.univ) :
    let C := (Finset.univ : Finset A) \ Finset.univ.biUnion S
    C.Nonempty ∧ (∀ i, Disjoint (S i) C) ∧ C.image g = C ∧
      (-1 : ℤ) ^ (k + 1) + (-1 : ℤ) ^ (k + 2) = 0 := by
  classical
  let U : Finset A := Finset.univ.biUnion S
  have hU : U.image g = U := by
    simp only [U, Finset.biUnion_image, hS]
  have hC : ((Finset.univ : Finset A) \ U).image g = Finset.univ \ U := by
    rw [Finset.image_sdiff _ _ g.injective, Finset.image_univ_equiv g, hU]
  have hnon : ((Finset.univ : Finset A) \ U).Nonempty := by
    apply Finset.sdiff_nonempty.mpr
    intro h
    exact hproper (Finset.Subset.antisymm (Finset.subset_univ U) h)
  refine ⟨hnon, ?_, hC, ?_⟩
  · intro i
    apply Finset.disjoint_left.mpr
    intro a ha hb
    exact (Finset.mem_sdiff.mp hb).2 (Finset.mem_biUnion.mpr
      ⟨i, Finset.mem_univ i, ha⟩)
  · rw [show k + 2 = (k + 1) + 1 by omega, pow_succ]
    ring


end
end HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7
