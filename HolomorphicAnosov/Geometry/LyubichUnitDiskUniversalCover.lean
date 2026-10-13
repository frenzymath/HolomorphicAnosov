import Mathlib.Analysis.Complex.Basic
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Convex.Contractible

/-! The open unit disk subtype used as the source of the modular-lambda universal cover. (Lyubich, §2.4.13.) -/

namespace HolomorphicAnosov

/-- The open unit disk subtype used by the modular-lambda map is simply connected. -/
theorem lyubich_unit_disk_universal_cover_source :
    SimplyConnectedSpace ({z : ℂ // ‖z‖ < 1}) := by
  have hset : {z : ℂ | ‖z‖ < 1} = Metric.ball (0 : ℂ) 1 := by
    ext z
    simp [Metric.mem_ball, dist_zero_right]
  let hsconv : Convex ℝ {z : ℂ | ‖z‖ < 1} :=
    hset ▸ convex_ball (0 : ℂ) 1
  let : ContractibleSpace ({z : ℂ // ‖z‖ < 1}) :=
    hsconv.contractibleSpace ⟨0, by norm_num⟩
  exact SimplyConnectedSpace.ofContractible _

end HolomorphicAnosov
