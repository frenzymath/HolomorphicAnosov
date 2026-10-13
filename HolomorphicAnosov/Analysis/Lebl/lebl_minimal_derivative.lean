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
import HolomorphicAnosov.Analysis.Lebl.lebl_exists_nonzero_jet

namespace HolomorphicAnosov.Analysis

open Set
open scoped ContDiff

/-- Lebl, Tasty Bits of Several Complex Variables v3.4, §1.6 Theorem 1.6.2 p.36.
Public auxiliary result in the regular-hypersurface proof. -/
lemma lebl_minimal_derivative {d : ℕ} (hd : 1 ≤ d)
    {U W : Set (Fin d → ℂ)} {a : (Fin d → ℂ) → ℂ}
    (hU : IsOpen U) (hconnected : IsConnected U)
    (ha : DifferentiableOn ℂ a U) (hnonzero : ∃ z ∈ U, a z ≠ 0)
    (hNW : ∃ p ∈ U ∩ W, a p = 0) :
    ∃ (h : (Fin d → ℂ) → ℂ) (j : Fin d) (p : Fin d → ℂ),
      p ∈ U ∩ W ∧ a p = 0 ∧ ContDiffOn ℂ ∞ h U ∧ DifferentiableOn ℂ h U ∧
      (∀ z ∈ U ∩ W, a z = 0 → h z = 0) ∧
      HolomorphicAnosov.Analysis.Complex.LeblPolydisc.coordinateDerivative j h p ≠ 0 := by
  classical
  let P : ℕ → Prop := fun k ↦ ∃ (J : List (Fin d)) (p : Fin d → ℂ),
    J.length = k ∧ p ∈ U ∩ W ∧ a p = 0 ∧
      HolomorphicAnosov.Analysis.Complex.LeblPolydisc.orderedDerivative a J p ≠ 0
  obtain ⟨p₀, hp₀, ha₀⟩ := hNW
  obtain ⟨J₀, hJ₀⟩ := lebl_exists_nonzero_jet hd hU hconnected ha hnonzero hp₀.1
  have hex : ∃ k, P k := ⟨J₀.length, J₀, p₀, rfl, hp₀, ha₀, hJ₀⟩
  obtain ⟨J, p, hlen, hp, hap, hJ⟩ := Nat.find_spec hex
  have hJnil : J ≠ [] := by
    intro he
    subst J
    exact hJ hap
  obtain ⟨L, j, hsplit⟩ := J.eq_nil_or_concat'.resolve_left hJnil
  have hshort : L.length < Nat.find hex := by
    rw [← hlen, hsplit, List.length_append, List.length_singleton]
    omega
  let h := HolomorphicAnosov.Analysis.Complex.LeblPolydisc.orderedDerivative a L
  have hzero : ∀ z ∈ U ∩ W, a z = 0 → h z = 0 := by
    intro z hz haz
    by_contra hn
    have hpL : P L.length := ⟨L, z, rfl, hz, haz, hn⟩
    exact Nat.not_lt_of_ge (Nat.find_min' hex hpL) hshort
  have hh := (HolomorphicAnosov.Analysis.Complex.lebl_polydisc_holomorphic_coordinate_derivatives
    hd U hU a ha).1 L
  refine ⟨h, j, p, hp, hap, hh.1, hh.2, hzero, ?_⟩
  simpa [h, hsplit, HolomorphicAnosov.Analysis.Complex.LeblPolydisc.orderedDerivative,
    List.foldl_append] using hJ

end HolomorphicAnosov.Analysis
