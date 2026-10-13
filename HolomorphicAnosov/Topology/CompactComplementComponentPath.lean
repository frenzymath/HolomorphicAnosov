import Mathlib.Topology.Connected.LocallyPathConnected

/-!
# Paths in open components of compact complements

This is the component-path step used in Conway's Janiszewski nonseparation argument.
A compact set is closed in a Hausdorff space, so its complement is open; local path
connectedness then upgrades the connected component containing a marked point to a
path-connected set.  The theorem is stated generically because this construction is
independent of the later Jordan and winding argument.

Source: John B. Conway, *Functions of One Complex Variable II*, GTM 159, Springer (1995),
Chapter 14, Lemma 5.4, printed p.49 (PDF64), path selection in the individual
complements.  The proof uses the pinned Mathlib component and local path-connectivity APIs.
DAG node: `topo.compact_complement_component_path_g10`.
-/

open Set

namespace HolomorphicAnosov.Topology

/-- A compact complement component in a locally path connected Hausdorff space contains
an actual path between any two of its points. -/
theorem joinedIn_compl_of_compact_component
    {X : Type*} [TopologicalSpace X] [T2Space X] [LocallyPathConnectedSpace X]
    (A : Set X) (hA : IsCompact A) (x y : X) (hxA : x ∉ A)
    (hxyA : y ∈ connectedComponentIn Aᶜ x) : JoinedIn Aᶜ x y := by
  have hop : IsOpen (connectedComponentIn Aᶜ x) :=
    hA.isClosed.isOpen_compl.connectedComponentIn
  have hpc := hop.isConnected_iff_isPathConnected.mp
    (isConnected_connectedComponentIn_iff.mpr hxA)
  exact (hpc.joinedIn x (mem_connectedComponentIn hxA) y hxyA).mono
    (connectedComponentIn_subset _ _)

end HolomorphicAnosov.Topology

