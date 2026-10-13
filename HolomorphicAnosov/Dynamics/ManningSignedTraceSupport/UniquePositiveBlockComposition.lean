import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.BlockCardComposition
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.DisjointBlockTotalBounds
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.PositiveComposition

namespace HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7
open scoped BigOperators Classical
noncomputable section

/-- Every positive-length ordered nonempty disjoint block family on a finite
alphabet belongs to exactly one positive composition of size at most q, if q
bounds the alphabet cardinality. Its composition list is the ordered list of
block cardinalities. Summing that list determines the total index; composition
extensionality then determines the composition itself. Source: Manning (1971),
pp.217–219, the indexing of the ordered block alphabets. -/
theorem unique_positive_block_composition {A : Type*} [Fintype A] {k q : ℕ}
    (hk : 0 < k) (S : Fin k → Finset A) (hne : ∀ i, (S i).Nonempty)
    (hdis : Pairwise fun i j ↦ Disjoint (S i) (S j)) (hq : Fintype.card A ≤ q) :
    ∃! c : PositiveComposition q, c.2.blocks = List.ofFn (fun i ↦ (S i).card) := by
  classical
  let n := ∑ i, (S i).card
  have hn : 0 < n ∧ n ≤ q := by
    have h := disjoint_block_total_bounds hk S hne hdis
    exact ⟨h.1, h.2.trans hq⟩
  let r : Fin q := ⟨n - 1, by omega⟩
  let c : Composition (r.val + 1) :=
    (blockCardComposition S hne).cast (by dsimp [r]; omega)
  refine ⟨⟨r, c⟩, rfl, ?_⟩
  rintro ⟨r', c'⟩ hc'
  have hr : r' = r := by
    apply Fin.ext
    have hsum : r'.val + 1 = n := by
      rw [← c'.blocks_sum, hc', List.sum_ofFn]
    dsimp [r]
    omega
  subst r'
  have hcomp : c' = c := Composition.ext hc'
  exact congrArg (fun d : Composition (r.val + 1) ↦ (⟨r, d⟩ : PositiveComposition q)) hcomp

end
end HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7
