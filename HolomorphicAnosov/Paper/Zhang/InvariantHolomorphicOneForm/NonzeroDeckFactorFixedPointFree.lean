import HolomorphicAnosov.Topology.DiscreteOrbitLimitFixed
import Mathlib.Analysis.Complex.Basic

open Set

open scoped _root_.Topology

noncomputable section
namespace HolomorphicAnosov.Paper.Zhang


universe u

/-- A nonzero deck label induces a fixed-point-free scalar map when its inverse orbit stays in a
discrete set and tends to zero whenever the label lies in the unstable subspace. (Zhang, Lemma
4.2) -/
theorem nonzero_deck_factor_fixed_point_free
    {V Y : Type*} [TopologicalSpace V] [AddCommGroup V] [Module ℝ V]
    (U : Submodule ℝ V) (Z : Set V) (T : V → V)
    (hTi : Function.Injective T) (hZd : IsDiscrete Z)
    (hTZ : Set.MapsTo T Z Z) (hzero : (0 : V) ∈ Z) (hTzero : T 0 = 0)
    (H : Y → V) (q : Y → ℂ) (hq : Function.Surjective q)
    (hfibre : ∀ y z, q y = q z ↔ H y - H z ∈ U)
    (γ : V) (hγ : γ ∈ Z) (hγzero : γ ≠ 0)
    (hdecay : γ ∈ U → Filter.Tendsto (fun n : ℕ ↦ T^[n] γ)
      Filter.atTop (𝓝 0))
    (D : Y → Y) (hdeck : ∀ y, H (D y) = H y + γ)
    (G : ℂ → ℂ) (hdesc : ∀ y, q (D y) = G (q y)) :
    ∀ w, G w ≠ w := by
  intro w hfix
  obtain ⟨y, hy⟩ := hq w
  have hsame : q (D y) = q y := by rw [hdesc, hy, hfix]
  have hU := (hfibre (D y) y).mp hsame
  rw [hdeck] at hU
  have hγU : γ ∈ U := by simpa only [add_sub_cancel_left] using hU
  exact hγzero (discrete_orbit_limit_fixed.1 V T Z hTi hZd hTZ
    γ 0 hγ hzero hTzero (hdecay hγU))


end HolomorphicAnosov.Paper.Zhang
