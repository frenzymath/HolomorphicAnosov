import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.BlockMatchingPullbackEq
import Mathlib.Data.Int.Init

namespace HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7
open scoped Classical
noncomputable section

/-- For a two-sided matched block itinerary, pulling every block back through
its coding-coordinate map gives the same subset of the fibre at every time,
provided all legal edges follow individual fibre elements. Consecutive equality
is the public matching-pullback lemma; two-sided integer induction gives the
assertion at every time. Source: Manning (1971), pp.218–219. -/
theorem matched_blocks_pullback_constant {A : Type*} [Fintype A] {N : ℕ}
    (T : Matrix (Fin N) (Fin N) ℤ) (l : ℤ → A → Fin N)
    (hforced : ∀ j a b, T (l j a) (l (j + 1) b) = 1 → a = b)
    (S : ℤ → Finset (Fin N))
    (hs : ∀ j i, i ∈ S j → ∃ a, l j a = i)
    (hmatch : ∀ j, BlockMatching T (S j) (S (j + 1))) (j : ℤ) :
    Finset.univ.filter (fun a ↦ l j a ∈ S j) =
      Finset.univ.filter (fun a ↦ l 0 a ∈ S 0) := by
  classical
  have hstep (k : ℤ) := blockMatching_pullback_eq T (l k) (l (k + 1))
    (hforced k) (hs k) (hs (k + 1)) (hmatch k)
  refine Int.inductionOn' j 0 rfl ?_ ?_
  · intro k _ ih
    exact (hstep k).symm.trans ih
  · intro k _ ih
    have h := (hstep (k - 1))
    simpa only [sub_add_cancel] using h.trans (by simpa only [sub_add_cancel] using ih)

end
end HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7
