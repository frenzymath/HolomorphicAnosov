import Mathlib.Topology.Connected.PathConnected

/-!
Path-component membership along covering sheets. (Bredon, II §14, pp.111–112; Hatcher, pp.60–62)
-/

noncomputable section
open Set _root_.Topology
namespace HolomorphicAnosov
universe u v w
variable {E : Type u} {B : Type v} {I : Type w}
variable [TopologicalSpace E] [TopologicalSpace B] [TopologicalSpace I]

/-- Over a path-connected base, membership in a fixed path component is constant along each covering
sheet. (Bredon, II §14, pp.111–112; Hatcher, pp.60–62) -/
theorem coveringSheet_component_iff (f : E → B) (V : Set B)
    (H : f ⁻¹' V ≃ₜ V × I) [PathConnectedSpace V]
    (e0 : E) (v0 v : V) (i : I) :
    (H.symm (v, i)).val ∈ pathComponent e0 ↔
      (H.symm (v0, i)).val ∈ pathComponent e0 := by
  let γ := PathConnectedSpace.somePath v0 v
  have hjoin : Joined (H.symm (v0, i)).val (H.symm (v, i)).val :=
    ⟨γ.map (continuous_subtype_val.comp
      (H.symm.continuous.comp (continuous_id.prodMk continuous_const)))⟩
  exact ⟨fun hc ↦ hc.trans hjoin.symm, fun hc ↦ hc.trans hjoin⟩

end HolomorphicAnosov

