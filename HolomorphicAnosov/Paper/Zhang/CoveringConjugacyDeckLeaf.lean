import HolomorphicAnosov.Geometry.LiftedIntrinsicLeafRange
import Mathlib.Topology.Covering.Basic

open Set
open scoped Topology _root_.Topology

universe u
namespace HolomorphicAnosov

/-- Deck transformations preserve the exact lifted intrinsic path carrier. -/
theorem covering_conjugacy_deck_leaf_g15
    {X Y L : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace L]
    (p : Y → X) (j : L → X) (a : L) (y : Y)
    (D : Y ≃ₜ Y) (hD : ∀ z, p (D z) = p z) :
    D '' liftedIntrinsicLeafRange p j a y =
      liftedIntrinsicLeafRange p j a (D y) := by
  ext z
  constructor
  · rintro ⟨w, ⟨b, γ, η, he⟩, rfl⟩
    refine ⟨b, γ, η.map D.continuous, ?_⟩
    intro t
    exact (hD (η t)).trans (he t)
  · rintro ⟨b, γ, η, he⟩
    have hi (w : Y) : p (D.symm w) = p w := by
      simpa only [D.apply_symm_apply] using (hD (D.symm w)).symm
    refine ⟨D.symm z, ?_, D.apply_symm_apply z⟩
    let η' : Path y (D.symm z) :=
      { toContinuousMap := ⟨fun t ↦ D.symm (η t), D.symm.continuous.comp η.continuous⟩
        source' := by simp
        target' := by simp }
    refine ⟨b, γ, η', ?_⟩
    intro t
    exact (hi (η t)).trans (he t)


end HolomorphicAnosov
