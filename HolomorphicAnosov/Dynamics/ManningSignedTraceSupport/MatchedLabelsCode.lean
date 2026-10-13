import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.IntegerEquivalencePath
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.BlockMatching
import HolomorphicAnosov.Dynamics.Bowen.BowenBasicSetMarkovCoding

namespace HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7.CodingAdapter
open Set BowenBasicSetCoding
open scoped Classical
noncomputable section

/-- A two-sided sequence of nonempty matched label sets determines an admissible code whose label at each time lies in the prescribed set. (Manning, pp. 218–219) -/
theorem matched_labels_code {N : ℕ} (B : Fin N → Fin N → Prop)
    (T : Matrix (Fin N) (Fin N) ℤ) (hT : ∀ i k, T i k = 1 ↔ B i k)
    (S : ℤ → Finset (Fin N)) (hmatch : ∀ j, BlockMatching T (S j) (S (j + 1)))
    (j₀ : ℤ) (i : Fin N) (hi : i ∈ S j₀) :
    ∃ a : CodeSpace B, a.val j₀ = i ∧ ∀ j, a.val j ∈ S j := by
  let E : ∀ j, ↥(S j) ≃ ↥(S (j + 1)) := fun j ↦ Classical.choose (hmatch j)
  obtain ⟨a, ha, hedge⟩ := integer_equivalence_path E j₀ ⟨i, hi⟩
  refine ⟨⟨fun j ↦ (a j).val, ?_⟩, congrArg Subtype.val ha, fun j ↦ (a j).property⟩
  intro j
  apply (hT _ _).mp
  have h := Classical.choose_spec (hmatch j) (a j)
  simpa only [← hedge j] using h

end
end HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7.CodingAdapter
