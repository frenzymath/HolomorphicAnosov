import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.MetricSpace.Pseudo.Pi
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Tactic.Linarith
import HolomorphicAnosov.Dynamics.ProperRelativeMarkovPartitionG7
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.ExtendClosedPairBracket

namespace HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7.CarrierAdapter

open Set Filter _root_.Topology
open scoped BigOperators ENNReal Classical
noncomputable section

/-- Constructs a proper relative Markov partition from the original metric, bracket, rectangles, and Markov inclusions. -/
noncomputable def originalRectanglesToPublicPartition {M:Type*}[MetricSpace M]
 (f:M≃ₜM)(Λ:Set M)(hne:Λ.Nonempty)(hcompact:IsCompact Λ)
 (F:Λ≃ₜΛ)(hF:∀x:Λ,(F x).val=f x.val)
 (γ ε s:ℝ)(hγ:0<γ)(hε:0<ε)(hs:0<s)(hsε:s≤ε)
 (B:{p:Λ×Λ//dist p.1 p.2≤ε}→Λ) (hB:Continuous B)
 (hBmem:∀p,B p∈relativeClosedStablePlaque F γ p.val.1∩relativeClosedUnstablePlaque F γ p.val.2)
 (hBunique:∀p,∀z:Λ,z∈relativeClosedStablePlaque F γ p.val.1∩relativeClosedUnstablePlaque F γ p.val.2→z=B p)
 {N:ℕ}(R:Fin N→Set Λ)
 (hshape:∀i,(R i).Nonempty∧IsCompact (R i)∧R i=closure (interior (R i)))
 (hsmall:∀i,Metric.diam (R i)≤s)
 (hprod:∀i,∀x∈R i,∀y∈R i,∃z∈R i,z∈relativeClosedStablePlaque F γ x∩relativeClosedUnstablePlaque F γ y)
 (hcover:∀x:Λ,∃i,x∈R i)
 (hdisjoint:∀i j,i≠j→Disjoint (interior (R i)) (interior (R j)))
 (hmarkov:∀i j,∀x:Λ,x∈interior (R i)→F x∈interior (R j)→
    F '' (R i∩relativeClosedStablePlaque F γ x)⊆R j∩relativeClosedStablePlaque F γ (F x)∧
    R j∩relativeClosedUnstablePlaque F γ (F x)⊆F '' (R i∩relativeClosedUnstablePlaque F γ x)) :
 ProperRelativeMarkovPartition f Λ := by
 classical
 let g := Classical.choose (extend_closed_pair_bracket B hB)
 have hg : ∀p:{p:Λ×Λ//dist p.1 p.2≤ε},g p.val.1 p.val.2=B p := (Classical.choose_spec (extend_closed_pair_bracket B hB)).1
 have hgc := (Classical.choose_spec (extend_closed_pair_bracket B hB)).2
 exact {
   nonempty:=hne
   compact:=hcompact
   onSet:=F
   onSet_eq:=hF
   γ:=γ
   γ_pos:=hγ
   ε:=ε
   ε_pos:=hε
   bracket:=g
   bracket_mem:=by
     intro x y hxy
     rw [hg ⟨(x,y),hxy⟩]
     exact hBmem _
   bracket_unique:=by
     intro x y hxy z hz
     rw [hg ⟨(x,y),hxy⟩]
     exact hBunique _ z hz
   bracket_continuous:=hgc
   rectangleScale:=s
   rectangleScale_pos:=hs
   rectangleScale_le_close:=hsε
   N:=N
   rectangles:=R
   rectangles_nonempty:=fun i=>(hshape i).1
   rectangles_closed:=fun i=>(hshape i).2.1.isClosed
   rectangles_regularClosed:=fun i=>(hshape i).2.2.symm
   rectangles_small:=hsmall
   rectangles_bracket:=by
     intro i x hx y hy
     have hd:dist x y≤ε:=(Metric.dist_le_diam_of_mem (hshape i).2.1.isBounded hx hy).trans ((hsmall i).trans hsε)
     obtain ⟨z,hzR,hz⟩:=hprod i x hx y hy
     have hzB:z=g x y:=by
       rw [hg ⟨(x,y),hd⟩]
       exact hBunique _ z hz
     exact hzB ▸ hzR
   cover:=hcover
   disjoint_interiors:=hdisjoint
   stable_markov:=fun i j x hxi hxj=>(hmarkov i j x hxi hxj).1
   unstable_markov:=fun i j x hxi hxj=>(hmarkov i j x hxi hxj).2
 }


end
end HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7.CarrierAdapter
