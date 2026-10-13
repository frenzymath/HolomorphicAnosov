import Mathlib.Topology.Continuous
import Mathlib.Order.Filter.Tendsto
import HolomorphicAnosov.Dynamics.Anosov.LiftedLeafAffineImage.FullDecaySubmodule

open scoped Topology _root_.Topology
open Filter Set

namespace HolomorphicAnosov

/-- A continuous linear map commuting with an automorphism preserves its full
forward-decay submodule. This is the direct limit calculation used for the
invariant stable and unstable planes in Zhang, Section 4, before Lemma 4.2:
commutation gives `Aⁿ(Bv)=B(Aⁿv)`, and continuity of `B` carries convergence to
zero to convergence to `B 0=0`. The proof needs no spectral assumption or finite
dimension, and includes the zero submodule and zero map. -/
theorem fullDecaySubmodule_mapsTo_of_commute
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (A : V ≃L[ℝ] V) (B : V →L[ℝ] V) (hBA : Function.Commute B A) :
    Set.MapsTo B (fullDecaySubmodule A) (fullDecaySubmodule A) := by
  intro v hv
  have hv' : Tendsto (fun n : ℕ ↦ (A : V → V)^[n] v) atTop (𝓝 0) := hv
  have hlim := B.continuous.continuousAt.tendsto.comp hv'
  change Tendsto (fun n : ℕ ↦ (A : V → V)^[n] (B v)) atTop (𝓝 0)
  simpa only [Function.comp_def, map_zero, (hBA.iterate_right _).eq] using hlim


end HolomorphicAnosov
