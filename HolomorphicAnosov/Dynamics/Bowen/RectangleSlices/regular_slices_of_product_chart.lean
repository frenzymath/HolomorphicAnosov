import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Constructions
import HolomorphicAnosov.Dynamics.Bowen.RectangleSlices.regular_closed_open_restriction
import HolomorphicAnosov.Dynamics.Bowen.RectangleSlices.regular_closed_prod_left
import HolomorphicAnosov.Dynamics.Bowen.RectangleSlices.regular_closed_prod_right

namespace HolomorphicAnosov.Bowen.RectangleSlicesPreparation

open Set

theorem regular_slices_of_product_chart {X Y Z : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (A W : Set X) (U C : Set Y) (V D : Set Z) (hW : IsOpen W)
    (hU : IsOpen U) (hV : IsOpen V) (hC : IsClosed C) (hD : IsClosed D)
    (hCU : C ⊆ U) (hDV : D ⊆ V) (hCn : C.Nonempty) (hDn : D.Nonempty)
    (h : (U × V) ≃ₜ W) (hA : A = closure (interior A))
    (hpre : h ⁻¹' (Subtype.val ⁻¹' A) =
      (Subtype.val ⁻¹' C : Set U) ×ˢ (Subtype.val ⁻¹' D : Set V)) :
    C = closure (interior C) ∧ D = closure (interior D) := by
  have hr : (Subtype.val ⁻¹' A : Set W) =
      closure (interior (Subtype.val ⁻¹' A : Set W)) := by
    rw [← hW.isOpenMap_subtype_val.preimage_interior_eq_interior_preimage
      continuous_subtype_val, ← hW.isOpenMap_subtype_val.preimage_closure_eq_closure_preimage
      continuous_subtype_val, ← hA]
  have hp : (Subtype.val ⁻¹' C : Set U) ×ˢ (Subtype.val ⁻¹' D : Set V) =
      closure (interior ((Subtype.val ⁻¹' C : Set U) ×ˢ (Subtype.val ⁻¹' D : Set V))) := by
    rw [← hpre, ← h.preimage_interior, ← h.preimage_closure, ← hr]
  have hCn' : (Subtype.val ⁻¹' C : Set U).Nonempty := by
    obtain ⟨c, hc⟩ := hCn
    exact ⟨⟨c, hCU hc⟩, hc⟩
  have hDn' : (Subtype.val ⁻¹' D : Set V).Nonempty := by
    obtain ⟨d, hd⟩ := hDn
    exact ⟨⟨d, hDV hd⟩, hd⟩
  exact ⟨regular_closed_open_restriction C U hC hU hCU
    (regular_closed_prod_left _ _ (hC.preimage continuous_subtype_val) hDn' hp),
    regular_closed_open_restriction D V hD hV hDV
      (regular_closed_prod_right _ _ (hD.preimage continuous_subtype_val) hCn' hp)⟩

end HolomorphicAnosov.Bowen.RectangleSlicesPreparation
