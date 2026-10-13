import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.BlockMatching
import Mathlib.Data.Fintype.Basic

namespace HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7
open scoped Classical
noncomputable section

/-- A block matching between two coordinate label sets preserves their pullback
to the coding fibre when every legal edge follows the same fibre element.
Forwards, choose the matching target and use the no-cross property. Backwards,
choose the inverse matching source and use the same property. This is the
coordinate-subset identification in Manning (1971), pp.218–219. -/
theorem blockMatching_pullback_eq {A : Type*} [Fintype A] {N : ℕ}
    (T : Matrix (Fin N) (Fin N) ℤ) (l r : A → Fin N)
    (hforced : ∀ a b, T (l a) (r b) = 1 → a = b)
    {s t : Finset (Fin N)}
    (hs : ∀ i ∈ s, ∃ a, l a = i) (ht : ∀ i ∈ t, ∃ a, r a = i)
    (hmatch : BlockMatching T s t) :
    Finset.univ.filter (fun a ↦ l a ∈ s) = Finset.univ.filter (fun a ↦ r a ∈ t) := by
  classical
  obtain ⟨e, he⟩ := hmatch
  ext a
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro ha
    let i : ↥s := ⟨l a, ha⟩
    obtain ⟨b, hb⟩ := ht (e i).val (e i).property
    have hab : a = b := hforced a b (by simpa only [hb] using he i)
    simpa only [hab, hb] using (e i).property
  · intro ha
    let j : ↥t := ⟨r a, ha⟩
    obtain ⟨b, hb⟩ := hs (e.symm j).val (e.symm j).property
    have hba : b = a := hforced b a (by
      have h := he (e.symm j)
      simpa only [e.apply_symm_apply, hb] using h)
    simpa only [← hba, hb] using (e.symm j).property

end
end HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7
