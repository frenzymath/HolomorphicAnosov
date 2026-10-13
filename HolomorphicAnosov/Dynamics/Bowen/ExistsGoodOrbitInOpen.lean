import HolomorphicAnosov.Topology.ManningBowenInitialCoverUniformSaturation
import HolomorphicAnosov.Dynamics.Bowen.CompactLocalProductData

namespace HolomorphicAnosov.Dynamics.Bowen

open Set

/-- The good-orbit witness after Bowen Lemma 24, p.739: every nonempty open
transition contains a point whose first `m + 1` orbit points lie in the open dense
quadrant set. This uses only finitely many preimages under the original map. -/
theorem exists_good_orbit_in_open
    {X : Type*} [TopologicalSpace X] (f : X ≃ₜ X)
    {Z W : Set X} (hZopen : IsOpen Z) (hZdense : Dense Z)
    (hWopen : IsOpen W) (hW : W.Nonempty) (m : ℕ) :
    ∃ x ∈ W, ∀ k ≤ m, (f ^ k) x ∈ Z := by
  have hd (T : Finset (Fin (m + 1))) :
      Dense (⋂ k ∈ T, (⇑(f ^ k.val) : X → X) ⁻¹' Z) := by
    induction T using Finset.induction_on with
    | empty => simp
    | @insert k T hk ih =>
        simpa only [Finset.mem_insert, iInter_iInter_eq_or_left] using
          (hZdense.preimage (f ^ k.val).isOpenMap).inter_of_isOpen_left ih
            (hZopen.preimage (f ^ k.val).continuous)
  have hdall : Dense (⋂ k : Fin (m + 1), (⇑(f ^ k.val) : X → X) ⁻¹' Z) := by
    simpa using hd Finset.univ
  obtain ⟨x, hxW, hxZ⟩ := hdall.inter_open_nonempty W hWopen hW
  refine ⟨x, hxW, fun k hk ↦ ?_⟩
  exact mem_iInter.mp hxZ ⟨k, by omega⟩

end HolomorphicAnosov.Dynamics.Bowen
