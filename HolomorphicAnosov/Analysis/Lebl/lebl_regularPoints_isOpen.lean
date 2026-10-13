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
import HolomorphicAnosov.Analysis.Lebl.leblHolomorphicZeroSet
import HolomorphicAnosov.Analysis.Lebl.leblHolomorphicHypersurfaceRegularPoints
import HolomorphicAnosov.Analysis.Lebl.isOpen_leblCoordinatePolydisc

namespace HolomorphicAnosov.Analysis

open Set
open scoped ContDiff

/-- Lebl, Tasty Bits of Several Complex Variables v3.4, §1.6 Theorem 1.6.2 p.36.
Public auxiliary result in the regular-hypersurface proof. -/
lemma lebl_regularPoints_isOpen {n : ℕ}
    (U : Set (Fin (n + 1) → ℂ)) (a : (Fin (n + 1) → ℂ) → ℂ) :
    IsOpen (leblHolomorphicHypersurfaceRegularPoints U a) := by
  classical
  apply isOpen_iff_mem_nhds.mpr
  intro p hp
  obtain ⟨hpN, σ, c, r, d, s, g, hr, hs, hpV, hpD, hg, hmaps, hinside, hgraph⟩ := hp
  have hhead : Continuous (fun q : leblHolomorphicZeroSet U a ↦
      fun i : Fin n ↦ q.val (σ i.castSucc)) :=
    continuous_pi fun i ↦ (continuous_apply _).comp continuous_subtype_val
  have hlast : Continuous (fun q : leblHolomorphicZeroSet U a ↦
      q.val (σ (Fin.last n))) := (continuous_apply _).comp continuous_subtype_val
  have hVN := (isOpen_leblCoordinatePolydisc c r).preimage hhead
  have hDN := (Metric.isOpen_ball (x := d) (ε := s)).preimage hlast
  apply Filter.mem_of_superset ((hVN.inter hDN).mem_nhds ⟨hpV, by simpa [dist_eq_norm] using hpD⟩)
  intro q hq
  exact ⟨q.property, σ, c, r, d, s, g, hr, hs, hq.1,
    by simpa [dist_eq_norm] using hq.2, hg, hmaps, hinside, hgraph⟩

end HolomorphicAnosov.Analysis
