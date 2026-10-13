import Mathlib.Topology.Connected.LocallyPathConnected
import Mathlib.Topology.IsLocalHomeomorph

open Set Filter Topology _root_.Topology

namespace HolomorphicAnosov

/-!
Transfer local path connectedness backwards through a local homeomorphism.

The source is not assumed Hausdorff, connected, or second countable.  The
argument shrinks an arbitrary open neighborhood through one local inverse and
uses the path-connected neighborhood basis in the target.
-/
theorem locallyPathConnectedSpace_of_isLocalHomeomorph
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [LocallyPathConnectedSpace Y] {f : X → Y}
    (hf : IsLocalHomeomorph f) : LocallyPathConnectedSpace X := by
  rw [locallyPathConnectedSpace_iff_pathComponentIn_mem_nhds]
  intro x U hU hxU
  obtain ⟨e, hxe, hfe⟩ := hf x
  have hEU : IsOpen (e.source ∩ U) := e.open_source.inter hU
  have hIm : IsOpen (e '' (e.source ∩ U)) :=
    e.isOpen_image_of_subset_source hEU inter_subset_left
  have hy : f x ∈ e '' (e.source ∩ U) := by
    refine ⟨x, ⟨hxe, hxU⟩, ?_⟩
    exact (congrFun hfe x).symm
  obtain ⟨W, ⟨hWopen, hyW, hWpath⟩, hWsub⟩ :=
    (isOpen_isPathConnected_basis (f x)).mem_iff.mp (hIm.mem_nhds hy)
  have hImageTarget : e '' (e.source ∩ U) ⊆ e.target := by
    rintro y ⟨z, hz, rfl⟩
    exact e.map_source hz.1
  have hWtarget : W ⊆ e.target := hWsub.trans hImageTarget
  let O : Set X := e.symm '' W
  have hOopen : IsOpen O := e.isOpen_image_symm_of_subset_target hWopen hWtarget
  have hxO : x ∈ O := by
    refine ⟨f x, hyW, ?_⟩
    rw [hfe]
    exact e.left_inv hxe
  have hOsub : O ⊆ U := by
    rintro z ⟨w, hw, rfl⟩
    obtain ⟨z', hz', rfl⟩ := hWsub hw
    simpa only [e.left_inv hz'.1] using hz'.2
  have hOpath : IsPathConnected O := by
    exact hWpath.image' (e.symm.continuousOn.mono hWtarget)
  exact mem_of_superset (hOopen.mem_nhds hxO)
    (hOpath.subset_pathComponentIn hxO hOsub)

end HolomorphicAnosov
