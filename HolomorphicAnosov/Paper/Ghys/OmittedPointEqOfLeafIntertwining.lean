import HolomorphicAnosov.Paper.Ghys.ProjectiveDeveloping
import HolomorphicAnosov.Paper.Zhang.StableFoliations
import HolomorphicAnosov.Topology.FreeAffineActionTranslations
import HolomorphicAnosov.Paper.Zhang.Anosov
import HolomorphicAnosov.Paper.Zhang.ComplexManifold
import HolomorphicAnosov.Geometry.Manifold.VectorBundle.ComplexTangentRankOne
import HolomorphicAnosov.Geometry.NativeTransverseAsymptoticIdentification
import HolomorphicAnosov.Geometry.GlobalHolonomy
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Topology.Covering.Deck
import Mathlib.Geometry.Manifold.LocalDiffeomorph


noncomputable section
open scoped ContDiff Manifold Topology
open Filter Set _root_.Topology

universe u v w
namespace HolomorphicAnosov.Ghys
attribute [local instance] complex_isManifold_real

/-- A biholomorphic leaf transport preserving the developing coordinate also preserves the omitted projective point. (Ghys, Theorem B, p.598) -/
theorem omitted_point_eq_of_leaf_intertwining
    {L L' Z : Type*} (h : L ≃ L') (D : L → Z) (D' : L' → Z)
    {o o' : Z}
    (hrange : Set.range D = {z | z ≠ o})
    (hrange' : Set.range D' = {z | z ≠ o'})
    (hintertwine : ∀ x, D' (h x) = D x) :
    o = o' := by
  have himage : Set.range D' = Set.range D := by
    ext z
    constructor
    · rintro ⟨y, rfl⟩
      obtain ⟨x, rfl⟩ := h.surjective y
      exact ⟨x, (hintertwine x).symm⟩
    · rintro ⟨x, rfl⟩
      exact ⟨h x, hintertwine x⟩
  rw [hrange, hrange'] at himage
  by_contra hne
  have hz : o' ∈ ({z | z ≠ o} : Set Z) := by
    intro heq
    exact hne heq.symm

  have hz' : o' ∉ ({z | z ≠ o'} : Set Z) := by simp
  exact hz' (himage ▸ hz)

end HolomorphicAnosov.Ghys

