import HolomorphicAnosov.Topology.Homotopy.MappingTelescopeSequence
import Mathlib.Topology.Connected.Basic

/-!
# Connectedness of the original mapping telescope

The concrete endpoint quotient is the mapping telescope of Hatcher §3.F p.312
and Proposition A.11 p.528. The connectedness argument is an elementary
connected-chain proof, without any prior CW structure or separation assumption.
DAG node: `topo.mapping_telescope_connected_g6`.
-/

namespace HolomorphicAnosov
open MappingTelescope.Sequence

/-- A sequence of nonempty connected spaces has a nonempty connected mapping
telescope, for the original coproduct-cylinder quotient topology.

Source: Hatcher's mapping telescope construction, §3.F p.312 and A.11 p.528;
the following elementary connected-chain argument expands the connectedness
clause of the cellular-telescope proof. Each original cylinder is connected,
so its continuous image in the quotient is connected. Consecutive cylinder
images meet at the actual top-to-next-bottom seam, witnessed by any source
point. Quotient induction proves that the images cover the entire telescope.
Mathlib's connected-chain union theorem therefore makes the whole quotient
connected and nonempty. No CW, Hausdorff, cellularity, injectivity, or finite
cell assumption is used. Nonempty levels are essential to the intersection
argument; arbitrary noninjective continuous bonds are permitted. -/
theorem cellular_telescope_connected_of_layers
    {X : ℕ → Type*} [∀ n, TopologicalSpace (X n)]
    (c : ∀ n, C(X n, X (n + 1)))
    (hX : ∀ n, Nonempty (X n) ∧ ConnectedSpace (X n)) :
    Nonempty (telescope c) ∧ ConnectedSpace (telescope c) := by
  classical
  let (n : ℕ) : ConnectedSpace (X n) := (hX n).2
  have hconn (n : ℕ) : IsConnected (Set.range (cylinder c n)) :=
    isConnected_range (cylinder c n).continuous
  have hmeet (n : ℕ) :
      (Set.range (cylinder c n) ∩ Set.range (cylinder c (n + 1))).Nonempty := by
    obtain ⟨x⟩ := (hX n).1
    refine ⟨cylinder c n (x, 1), ⟨(x, 1), rfl⟩, (c n x, 0), ?_⟩
    exact (levelTop_eq c n x).symm
  have hall : (⋃ n, Set.range (cylinder c n)) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro z
    refine Quotient.inductionOn z ?_
    rintro ⟨n, x, t⟩
    exact Set.mem_iUnion.mpr ⟨n, ⟨(x, t), rfl⟩⟩
  have hc : IsConnected (Set.univ : Set (telescope c)) := by
    rw [← hall]
    exact IsConnected.iUnion_of_chain hconn hmeet
  have : ConnectedSpace (telescope c) := connectedSpace_iff_univ.mpr hc
  exact ⟨inferInstance, inferInstance⟩

end HolomorphicAnosov

