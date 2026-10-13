import HolomorphicAnosov.Dynamics.Bowen.BowenBasicSetMarkovCoding

namespace HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7.CodingAdapter

open Set Filter _root_.Topology
open scoped BigOperators ENNReal ContDiff Manifold Bundle Classical
noncomputable section
open BowenBasicSetCoding

/-- Related codes have a common rectangle point at every time and therefore determine the same physical image. (Manning, Lemma 1, p. 216) -/
theorem related_codes_same_image {X:Type*}[MetricSpace X][CompactSpace X]
 (F:X≃ₜX){N:ℕ}(R:Fin N→Set X)(B:Fin N→Fin N→Prop)
 (coding:CodeSpace B→X){e:ℝ}
 (hexp:∀x y:X,(∀j:ℤ,dist ((F^j) x) ((F^j) y)≤e)→x=y)
 (hsmall:∀i,Metric.diam (R i)<e/2)
 (horbit:∀a:CodeSpace B,∀j:ℤ,(F^j) (coding a)∈R (a.val j))
 {a b:CodeSpace B}
 (hrelated:∀j:ℤ,(R (a.val j)∩R (b.val j)).Nonempty):
 coding a=coding b := by
 apply hexp
 intro j
 obtain ⟨z,hza,hzb⟩:=hrelated j
 have ha:=Metric.dist_le_diam_of_mem (Metric.isBounded_of_compactSpace (s:=R (a.val j)))
   (horbit a j) hza
 have hb:=Metric.dist_le_diam_of_mem (Metric.isBounded_of_compactSpace (s:=R (b.val j)))
   hzb (horbit b j)
 have htri:=dist_triangle ((F^j) (coding a)) z ((F^j) (coding b))
 have hsa:=hsmall (a.val j)
 have hsb:=hsmall (b.val j)
 linarith


end
end HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7.CodingAdapter
