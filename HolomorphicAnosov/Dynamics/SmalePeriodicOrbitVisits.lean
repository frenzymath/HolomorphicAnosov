import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Dynamics.PeriodicPts.Defs

namespace HolomorphicAnosov

open Set

/-- If a homeomorphism has a dense full orbit and dense periodic points, one periodic orbit meets
any two nonempty open sets (Shub, Prop. 9.7). -/
theorem smale_periodic_orbit_visits_two_open_sets
    {X : Type*} [TopologicalSpace X] (f : X ≃ₜ X)
    (x : X) (hx : Dense (Set.range (fun k : ℤ ↦ (f ^ k) x)))
    (hper : Dense (Function.periodicPts (f : X → X)))
    (U V : Set X) (hU : IsOpen U) (hUn : U.Nonempty)
    (hV : IsOpen V) (hVn : V.Nonempty) :
    ∃ p ∈ Function.periodicPts (f : X → X),
      ∃ m n : ℤ, (f ^ m) p ∈ U ∧ (f ^ n) p ∈ V := by
  obtain ⟨y, hyU, m, rfl⟩ := hx.inter_open_nonempty U hU hUn
  obtain ⟨z, hzV, n, rfl⟩ := hx.inter_open_nonempty V hV hVn
  let W := (f ^ m) ⁻¹' U ∩ (f ^ n) ⁻¹' V
  have hW : IsOpen W :=
    (hU.preimage (f ^ m).continuous).inter (hV.preimage (f ^ n).continuous)
  obtain ⟨p, hpW, hp⟩ := hper.inter_open_nonempty W hW ⟨x, hyU, hzV⟩
  exact ⟨p, hp, m, n, hpW⟩

end HolomorphicAnosov
