import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.MetricSpace.Pseudo.Pi
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Tactic.Linarith

namespace HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7.CarrierAdapter

open Set Filter _root_.Topology
open scoped BigOperators ENNReal Classical
noncomputable section

/-- Extend an actually supplied continuous bracket on the closed close-pair subtype to a total function by setting its value to the first endpoint off that domain. On the domain the extension equals the supplied bracket pointwise and is continuous by the native subtype/domRestrict criterion. No off-domain continuity or off-domain membership law is asserted. -/
theorem extend_closed_pair_bracket {X:Type*}[MetricSpace X] {ε:ℝ}
 (B:{p:X×X//dist p.1 p.2≤ε}→X) (hB:Continuous B):
 ∃g:X→X→X,
 (∀p:{p:X×X//dist p.1 p.2≤ε},g p.val.1 p.val.2=B p) ∧
 ContinuousOn (fun p:X×X=>g p.1 p.2) {p|dist p.1 p.2≤ε} := by
 classical
 let g:X→X→X:=fun x y => if h:dist x y≤ε then B ⟨(x,y),h⟩ else x
 have hg:∀p:{p:X×X//dist p.1 p.2≤ε},g p.val.1 p.val.2=B p:= by
  intro p
  exact dite_eq_left p.property
 refine ⟨g,hg,?_⟩
 apply continuousOn_iff_continuous_domRestrict.mpr
 exact hB.congr (fun p=> (hg p).symm)


end
end HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7.CarrierAdapter
