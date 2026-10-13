import Mathlib.Data.Set.Lattice.Indexed
import Mathlib.Data.Set.Disjoint

/-!
# Bowen's anchor argument for atom membership profiles

Source: Bowen, *Markov Partitions for Axiom A Diffeomorphisms* (1970), Lemma 20(b),
p.736, with the neighbor stars defined on p.735.
DAG node: `topo.bowen_atom_membership_profile_g18`.
-/

namespace HolomorphicAnosov.Topology

open Set

/-- Every point of a Bowen atom has the same original-set and neighbor-star profile
as its indexing point, even when that point lies on a quadrant frontier.

Source: Bowen (1970), Lemma 20(b), p.736. Choose an original set containing `z` as
an anchor. For any original set containing `z`, its own star is active, and its
selected set lies inside it. Thus every atom point belongs to the anchor and all
original sets containing `z`. Conversely, an original set containing an atom point
meets the anchor, so its star is active at `z`. If it missed `z`, its selected set
would be disjoint from it, a contradiction. Equality of star profiles then follows
from the definition as unions of original sets. In the parent, `U i` is the chosen
quadrant interior. The positive containment and negative disjointness are supplied
by the quadrant geometry; this statement does not assume the desired profile law.
-/
theorem bowen_atom_membership_profile {X ι : Type*}
    (A U : ι → Set X) (z : X) (hz : ∃ i, z ∈ A i)
    (hpositive : ∀ i, z ∈ A i → U i ⊆ A i)
    (hnegative : ∀ i, z ∉ A i → Disjoint (U i) (A i)) :
    let V := fun i ↦ ⋃ j, ⋃ (_ : (A i ∩ A j).Nonempty), A j
    let N := fun q ↦ {i | q ∈ V i}
    let O := ⋂ i, ⋂ (_ : z ∈ V i), U i
    ∀ t ∈ O, (∀ i, t ∈ A i ↔ z ∈ A i) ∧ N t = N z := by
  classical
  dsimp only
  intro t ht
  simp only [mem_iInter] at ht
  have hforward : ∀ i, z ∈ A i → t ∈ A i := by
    intro i hi
    apply hpositive i hi
    exact ht i (mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨⟨z, hi, hi⟩, hi⟩⟩)
  obtain ⟨a, hza⟩ := hz
  have hta := hforward a hza
  have hprofile : ∀ i, t ∈ A i ↔ z ∈ A i := by
    intro i
    refine ⟨?_, hforward i⟩
    intro hti
    by_contra hzi
    have hactive : z ∈ ⋃ j, ⋃ (_ : (A i ∩ A j).Nonempty), A j :=
      mem_iUnion.mpr ⟨a, mem_iUnion.mpr ⟨⟨t, hti, hta⟩, hza⟩⟩
    exact Set.disjoint_left.mp (hnegative i hzi) (ht i hactive) hti
  refine ⟨hprofile, ?_⟩
  ext i
  simp only [mem_ofPred_eq, mem_iUnion]
  constructor
  · rintro ⟨j, hj, htj⟩
    exact ⟨j, hj, (hprofile j).mp htj⟩
  · rintro ⟨j, hj, hzj⟩
    exact ⟨j, hj, (hprofile j).mpr hzj⟩

end HolomorphicAnosov.Topology
