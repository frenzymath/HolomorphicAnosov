import HolomorphicAnosov.Dynamics.Bowen.BowenBasicSetMarkovCoding

namespace HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7.CodingAdapter

open Set Filter _root_.Topology
open scoped BigOperators ENNReal ContDiff Manifold Bundle Classical
noncomputable section
open BowenBasicSetCoding

/-- Manning Lemma2 (p.217): the literal legal code obtained by following a through the crossing time j and b afterwards. The single witnessed crossing edge supplies adjacency at j; all other edges are inherited from the original codes. This is genuine piecewise finite-alphabet data, including all negative integer indices. -/
def spliceAt {N:ℕ} {B:Fin N→Fin N→Prop} (a b:CodeSpace B) (j:ℤ)
 (hcross:B (a.val j) (b.val (j+1))) : CodeSpace B :=
 ⟨fun k => if k≤j then a.val k else b.val k,by
   intro k
   by_cases hkj:k<j
   · have hk:k≤j:=by omega
     have hk1:k+1≤j:=by omega
     simpa only [ite_eq_left_iff,ite_eq_left hk,ite_eq_left hk1] using a.property k
   · by_cases hk:k=j
     · subst k
       simpa using hcross
     · have hk0:¬k≤j:=by omega
       have hk1:¬k+1≤j:=by omega
       simpa only [ite_eq_right hk0,ite_eq_right hk1] using b.property k⟩


end
end HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7.CodingAdapter
