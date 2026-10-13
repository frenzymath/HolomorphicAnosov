import HolomorphicAnosov.Topology.CWComplex.CellularApproximation
import HolomorphicAnosov.Topology.CellularMappingTelescopeCW
import HolomorphicAnosov.Topology.Homotopy.MappingTelescopeHomotopyComparisons
import HolomorphicAnosov.Topology.Homotopy.MappingTelescopeSequence
import Mathlib.Topology.CWComplex.Classical.Basic
import Mathlib.Topology.Homotopy.Equiv

/-!
# Cellular CW telescope model

A cellular approximation of a self-map of a connected Hausdorff CW complex has a
connected Hausdorff CW mapping telescope, together with the homotopy equivalence
from the original telescope. Source: Hatcher, Theorem 4.8, p.349, and
Proposition A.11, pp.528–529.
-/

namespace HolomorphicAnosov

universe v

/-- Cellular approximation supplies a connected Hausdorff CW telescope for a self-map.
Source: Hatcher, Theorem 4.8, p.349, and Proposition A.11, pp.528-529. -/
theorem cellular_telescope_model
    (P : Type v) [TopologicalSpace P] [T2Space P] [ConnectedSpace P]
    [Topology.CWComplex (Set.univ : Set P)] (a : C(P, P)) :
    ∃ c : C(P, P),
      (∀ d : ℕ, Set.MapsTo c
        (Topology.CWComplex.skeleton (Set.univ : Set P) d : Set P)
        (Topology.CWComplex.skeleton (Set.univ : Set P) d : Set P)) ∧
      a.Homotopic c ∧
      T2Space (MappingTelescope.Sequence.telescope (fun _ : ℕ ↦ c)) ∧
      Nonempty (Topology.CWComplex
        (Set.univ : Set (MappingTelescope.Sequence.telescope (fun _ : ℕ ↦ c)))) ∧
      ConnectedSpace (MappingTelescope.Sequence.telescope (fun _ : ℕ ↦ c)) ∧
      Nonempty (ContinuousMap.HomotopyEquiv
        (MappingTelescope.Sequence.telescope (fun _ : ℕ ↦ a))
        (MappingTelescope.Sequence.telescope (fun _ : ℕ ↦ c))) := by
  let A : Topology.RelCWComplex.Subcomplex (Set.univ : Set P) :=
    Topology.CWComplex.skeletonLT (Set.univ : Set P) 0
  have hA : (A : Set P) = ∅ := Topology.CWComplex.skeletonLT_zero_eq_empty
  obtain ⟨c, hc, hhom⟩ :=
    HolomorphicAnosov.Topology.CWComplex.cellularApproximation A a (by
      intro d x hx
      exact (hA ▸ hx.1).elim)
  have hc' : ∀ d : ℕ, Set.MapsTo c
      (Topology.CWComplex.skeleton (Set.univ : Set P) d : Set P)
      (Topology.CWComplex.skeleton (Set.univ : Set P) d : Set P) := hc
  obtain ⟨hT2, ⟨cw, _⟩, hconnected⟩ :=
    cellular_mapping_telescope_cw_structure (fun _ : ℕ ↦ c) (fun _ d ↦ hc' d)
  have hconn := (hconnected (fun _ ↦ ⟨inferInstance, inferInstance⟩)).2
  have hhom' := ContinuousMap.HomotopicRel.homotopic hhom
  obtain ⟨d, _, _, _, _⟩ :=
    (MappingTelescope.Sequence.mapping_telescope_homotopy_comparisons
      (fun _ : ℕ ↦ P) (fun _ ↦ a) P).1 (fun _ ↦ c) (fun _ ↦ hhom')
  exact ⟨c, hc', hhom', hT2, ⟨cw⟩, hconn, ⟨d⟩⟩


end HolomorphicAnosov
