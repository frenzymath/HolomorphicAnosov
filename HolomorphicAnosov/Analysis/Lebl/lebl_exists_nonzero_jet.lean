import HolomorphicAnosov.Analysis.Complex.LeblPolydiscCoordinateDerivatives
import HolomorphicAnosov.Analysis.Complex.PolydiscCauchyPowerSeries
import HolomorphicAnosov.Analysis.Complex.WindingHolomorphicZeroCount
import Mathlib.Analysis.Calculus.FDeriv.Defs
import Mathlib.Analysis.Calculus.FDeriv.Pi
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Topology.Connected.Basic
import HolomorphicAnosov.Analysis.Lebl.lebl_analyticOnNhd

namespace HolomorphicAnosov.Analysis

open Set
open scoped ContDiff

/-- Lebl, Tasty Bits of Several Complex Variables v3.4, §1.6 Theorem 1.6.2 p.36.
Public auxiliary result in the regular-hypersurface proof. -/
lemma lebl_exists_nonzero_jet {d : ℕ} (hd : 1 ≤ d)
    {U : Set (Fin d → ℂ)} {a : (Fin d → ℂ) → ℂ}
    (hU : IsOpen U) (hconnected : IsConnected U)
    (ha : DifferentiableOn ℂ a U) (hnonzero : ∃ z ∈ U, a z ≠ 0)
    {p : Fin d → ℂ} (hp : p ∈ U) :
    ∃ J : List (Fin d),
      HolomorphicAnosov.Analysis.Complex.LeblPolydisc.orderedDerivative a J p ≠ 0 := by
  classical
  by_contra! hall
  have hα : ∀ α : Fin d → ℕ,
      HolomorphicAnosov.Analysis.Complex.LeblPolydisc.multiIndexDerivative a α p = 0 :=
    fun α ↦ hall _
  obtain ⟨V, hV, hpV, hVU, hvzero⟩ :=
    (HolomorphicAnosov.Analysis.Complex.lebl_polydisc_holomorphic_coordinate_derivatives
      hd U hU a ha).2.2.2.2 p hp hα
  have heq : a =ᶠ[nhds p] (fun _ ↦ (0 : ℂ)) :=
    Filter.eventually_of_mem (hV.mem_nhds hpV) hvzero
  have hz := (lebl_analyticOnNhd hd hU ha).eqOn_of_preconnected_of_eventuallyEq
    analyticOnNhd_const hconnected.isPreconnected hp heq
  obtain ⟨z, hzU, hza⟩ := hnonzero
  exact hza (hz hzU)

end HolomorphicAnosov.Analysis
