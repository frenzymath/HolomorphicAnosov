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

/-- The adapted Fact1 bracket has a uniform diagonal buffer on its compact closed pair domain. Uniform continuity compares (x,y) to (x,x), where the bracket is x. A half-radius bound and the triangle inequality make the bracket strictly close to BOTH endpoints. This is a metric-topology calculation, not a change of the source bracket or an identification of arbitrary same-radius plaque sets. -/
theorem continuous_bracket_diagonal_buffer {X : Type*} [MetricSpace X] [CompactSpace X]
 {ε₀ : ℝ} (hε₀ : 0 ≤ ε₀)
 (B : {p : X×X // dist p.1 p.2 ≤ ε₀} → X) (hB : Continuous B)
 (hdiag : ∀ x:X, B ⟨(x,x),by simpa using hε₀⟩ = x)
 {r:ℝ} (hr:0<r) :
 ∃ a>0, ∀ p : {p : X×X // dist p.1 p.2 ≤ ε₀},
 dist p.val.1 p.val.2 < a →
 dist (B p) p.val.1 < r ∧ dist (B p) p.val.2 < r := by
 let K : Set (X×X) := {p | dist p.1 p.2 ≤ ε₀}
 have hK : IsCompact K := (isClosed_le (continuous_fst.dist continuous_snd) continuous_const).isCompact
 let hC : CompactSpace {p : X×X // dist p.1 p.2 ≤ ε₀} := isCompact_iff_compactSpace.mp hK
 have hUC : UniformContinuous B := CompactSpace.uniformContinuous_of_continuous hB
 obtain ⟨a,ha,hmod⟩ := Metric.uniformContinuous_iff.mp hUC (r/2) (half_pos hr)
 refine ⟨min a (r/2), lt_min ha (half_pos hr), ?_⟩
 intro p hp
 have hpd : dist p (⟨(p.val.1,p.val.1),by simpa using hε₀⟩ :
   {p : X×X // dist p.1 p.2 ≤ ε₀}) < a := by
   simpa [Subtype.dist_eq,Prod.dist_eq,dist_comm] using hp.trans_le (min_le_left a (r/2))
 have hb : dist (B p) p.val.1 < r/2 := by
  simpa only [hdiag] using hmod hpd
 refine ⟨hb.trans (half_lt_self hr),?_⟩
 have hxy : dist p.val.1 p.val.2 < r/2 := hp.trans_le (min_le_right a (r/2))
 exact (dist_triangle _ _ _).trans_lt (by linarith)


end
end HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7.MetricAdapter
