import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Card

namespace HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7
open scoped Classical
noncomputable section

/-- A proper disjoint family of nonempty blocks has fewer blocks than labels.
Choose one label in each block. Disjointness makes this choice injective into
the union, whose cardinality is strictly smaller than the whole alphabet.
This is the upper boundary in Manning's finite block cancellation (1971), pp.218–219. -/
theorem disjoint_nonempty_blocks_length_lt {A : Type*} [Fintype A] [DecidableEq A]
    {k : ℕ} (S : Fin k → Finset A) (hne : ∀ i, (S i).Nonempty)
    (hdis : Pairwise fun i j ↦ Disjoint (S i) (S j))
    (hproper : Finset.univ.biUnion S ≠ Finset.univ) : k < Fintype.card A := by
  classical
  let U := Finset.univ.biUnion S
  let e : Fin k → ↥U := fun i ↦ ⟨(hne i).choose,
    Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, (hne i).choose_spec⟩⟩
  have hinj : Function.Injective e := by
    intro i j hij
    by_contra hneij
    have heq := congrArg Subtype.val hij
    change (hne i).choose = (hne j).choose at heq
    exact (Finset.disjoint_left.mp (hdis hneij)) (hne i).choose_spec
      (heq.symm ▸ (hne j).choose_spec)
  have hle : k ≤ U.card := by
    simpa only [Fintype.card_fin, Fintype.card_coe] using
      Fintype.card_le_of_injective e hinj
  have hlt : U.card < Fintype.card A := by
    simpa only [Finset.card_univ] using
      Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_univ U, hproper⟩)
  exact hle.trans_lt hlt

end
end HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7
