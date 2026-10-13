import Mathlib.Analysis.Complex.Circle
import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Boundary images preserve disjoint parameter arcs

This helper isolates the elementary injectivity step needed in the accumulating
chord construction: a boundary homeomorphism carries pairwise disjoint subsets
of the parameter circle to pairwise disjoint image subsets.
-/

namespace HolomorphicAnosov

open Set

/--
The homeomorphism induced by an embedding's range preserves pairwise disjoint
families of subsets of the parameter circle.

The map `p ↦ h ⟨σ p, ⟨p, rfl⟩⟩` is injective because the embedding `σ` is
injective and `h` is a homeomorphism.  Images of disjoint sets under an
injective map are disjoint.
-/
theorem accumulatingChord_boundary_image_pairwise_disjoint
    {ι : Type*}
    (σ : Circle → ℂ) (hσ : Topology.IsEmbedding σ)
    (h : (Set.range σ) ≃ₜ Circle)
    (arcs : ι → Set Circle)
    (hArcsDisjoint : Pairwise fun i j ↦ Disjoint (arcs i) (arcs j)) :
    Pairwise (fun i j ↦
      Disjoint
        ((fun p : Circle ↦ (h ⟨σ p, ⟨p, rfl⟩⟩ : Circle)) '' arcs i)
        ((fun p : Circle ↦ (h ⟨σ p, ⟨p, rfl⟩⟩ : Circle)) '' arcs j)) := by
  have hg : Function.Injective (fun p : Circle ↦
      (h ⟨σ p, ⟨p, rfl⟩⟩ : Circle)) := by
    intro p q hpq
    apply hσ.injective
    exact congrArg Subtype.val (h.injective hpq)
  intro i j hij
  apply Set.disjoint_left.mpr
  rintro z ⟨p, hp, hpz⟩ ⟨q, hq, hqz⟩
  have hpq : p = q := hg (hpz.trans hqz.symm)
  subst q
  exact Set.disjoint_left.mp (hArcsDisjoint hij) hp hq

end HolomorphicAnosov
