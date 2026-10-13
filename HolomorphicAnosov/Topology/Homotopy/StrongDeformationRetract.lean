import Mathlib.Topology.Homotopy.Basic

/-!
# Strong deformation retract data

Source: Hatcher, *Algebraic Topology*, printed pp.2–3, deformation retraction and
retraction onto a subspace; Proposition 2.22, printed p.124, uses a deformation
retraction of a neighborhood. This module defines the data of DAG node
`topo.def_good_pair_strong_deformation_retract_g8`.
-/

namespace HolomorphicAnosov.Topology.Homotopy

universe u

/-- A strong deformation retract of `V` onto its subspace `A`.

Source: Hatcher, *Algebraic Topology*, printed pp.2–3 and Proposition 2.22, p.124.
Both sets carry the induced topology from the same ambient space `X`.
The continuous retraction restricts to the identity on `A`; the homotopy goes
from the identity on `V` to inclusion after retraction and fixes the copy of `A`
inside `V` at every time in the closed unit interval. `HomotopyRel` supplies
joint continuity and both endpoint laws as actual data.

No openness, closedness, neighborhood, nonemptiness, compactness or separation
condition is part of this definition. If `A = V`, the identity and its constant
homotopy supply the usual data. If both sets are empty, the fields are vacuous;
if `A` is empty and `V` is inhabited, the retraction field cannot be supplied.
This definition asserts no existence theorem.
-/
structure StrongDeformationRetract {X : Type u} [TopologicalSpace X]
    (A V : Set X) (hAV : A ⊆ V) where
  /-- The continuous map retracting the larger subspace onto the smaller one. -/
  retraction : C(V, A)
  /-- Retraction after inclusion is the identity on the smaller subspace. -/
  retraction_inclusion : retraction.comp (ContinuousMap.inclusion hAV) = ContinuousMap.id A
  /-- The deformation of the identity fixes every point of the smaller subspace. -/
  homotopy : ContinuousMap.HomotopyRel (ContinuousMap.id V)
    ((ContinuousMap.inclusion hAV).comp retraction) {v : V | v.val ∈ A}

end HolomorphicAnosov.Topology.Homotopy
