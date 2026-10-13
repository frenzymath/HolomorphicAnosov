import HolomorphicAnosov.Geometry.IntrinsicCoveringPullbackLeaf
import Mathlib.Topology.Covering.Basic
import Mathlib.Topology.Connected.LocallyPathConnected
import HolomorphicAnosov.Geometry.CoveringSheetRestrict
import HolomorphicAnosov.Geometry.CoveringComponentSheet

/-!
Restriction of covering maps to path components. (Bredon, II §14, pp.111–112; Hatcher, pp.60–62)
-/

noncomputable section
open Set _root_.Topology
namespace HolomorphicAnosov
universe u v w
variable {E : Type u} {B : Type v} {I : Type w}
variable [TopologicalSpace E] [TopologicalSpace B] [TopologicalSpace I]

/-- A covering map over a locally path-connected base remains a covering map when restricted to a
path component of its total space. (Bredon, II §14, pp.111–112; Hatcher, pp.60–62) -/
theorem isCoveringMap_pathComponent_restrict [LocallyPathConnectedSpace B]
    (f : E → B) (hf : IsCoveringMap f) (e0 : E) :
    IsCoveringMap (fun z : pathComponent e0 ↦ f z.val) := by
  intro b
  obtain ⟨inst, U, hbU, hU, hfU, H, hH⟩ := hf b
  obtain ⟨V, ⟨hV, hbV, hconn⟩, hVU⟩ :=
    (isOpen_isPathConnected_basis b).mem_iff.mp (hU.mem_nhds hbU)
  have : PathConnectedSpace V := isPathConnected_iff_pathConnectedSpace.mp hconn
  let H' := coveringSheetRestrict f hf.continuous U V hVU H hH
  have hH' : ∀ z, (H' z).1.val = f z := fun _ ↦ rfl
  let J := {i : f ⁻¹' {b} // (H'.symm (⟨b, hbV⟩, i)).val ∈ pathComponent e0}
  have : DiscreteTopology J := inferInstance
  apply IsEvenlyCovered.to_isEvenlyCovered_preimage (I := J)
  exact ⟨inferInstance, V, hbV, hV,
    hV.preimage (hf.continuous.comp continuous_subtype_val),
    coveringComponentSheet f V H' hH' e0 ⟨b, hbV⟩, fun _ ↦ rfl⟩

end HolomorphicAnosov
