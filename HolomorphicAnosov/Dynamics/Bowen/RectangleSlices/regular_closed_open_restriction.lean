import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Constructions

namespace HolomorphicAnosov.Bowen.RectangleSlicesPreparation

open Set

theorem regular_closed_open_restriction {Y : Type*} [TopologicalSpace Y]
    (S U : Set Y) (hS : IsClosed S) (hU : IsOpen U) (hSU : S ⊆ U)
    (hr : Subtype.val ⁻¹' S =
      closure (interior (Subtype.val ⁻¹' S : Set U))) :
    S = closure (interior S) := by
  apply Subset.antisymm
  · intro x hx
    have hy : (⟨x, hSU hx⟩ : U) ∈ closure (interior (Subtype.val ⁻¹' S : Set U)) :=
      hr ▸ hx
    have hz := image_closure_subset_closure_image continuous_subtype_val
      ⟨⟨x, hSU hx⟩, hy, rfl⟩
    apply closure_mono (s := Subtype.val '' interior (Subtype.val ⁻¹' S : Set U)) _ hz
    apply interior_maximal
    · rintro y ⟨z, hz, rfl⟩
      exact (interior_subset (s := Subtype.val ⁻¹' S) hz)
    · exact hU.isOpenMap_subtype_val _ isOpen_interior
  · exact closure_minimal interior_subset hS

end HolomorphicAnosov.Bowen.RectangleSlicesPreparation
