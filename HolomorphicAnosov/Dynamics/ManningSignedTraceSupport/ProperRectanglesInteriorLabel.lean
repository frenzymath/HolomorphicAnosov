import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.MetricSpace.Pseudo.Pi
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Tactic.Linarith

namespace HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7.MetricAdapter

open Set Filter _root_.Topology
open scoped BigOperators ENNReal Classical
noncomputable section

/-- A point in the interior of one proper rectangle cannot belong to another rectangle; hence its code label is unique. -/
theorem proper_rectangles_interior_label {X : Type*} [TopologicalSpace X]
 {N : ℕ} (R : Fin N → Set X)
 (hproper : ∀ i, R i = closure (interior (R i)))
 (hdisjoint : ∀ i j, i ≠ j → Disjoint (interior (R i)) (interior (R j)))
 {i k : Fin N} {x : X} (hxi : x∈interior (R i)) (hxk : x∈R k) : k=i := by
 by_contra hki
 have hxcl : x∈closure (interior (R k)) := by rw [←hproper]; exact hxk
 obtain ⟨y,hyi,hyk⟩ := (mem_closure_iff.mp hxcl) _ isOpen_interior hxi
 exact (Set.disjoint_left.mp (hdisjoint i k (Ne.symm hki))) hyi hyk


end
end HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7.MetricAdapter
