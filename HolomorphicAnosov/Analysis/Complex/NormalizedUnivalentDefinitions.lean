import Mathlib.Analysis.Complex.UnitDisc.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Topology.ContinuousMap.Algebra

/-! The disk-domain definitions of Lyubich §4.4, Theorem 4.12, pp.113–114.
Separated from the compactness proof so conditional continuity statements need
only their declared compactness hypothesis. -/
namespace HolomorphicAnosov

/-- Extend a disk-domain map by zero outside the open disk, solely to express
complex differentiability and its derivative in ambient coordinates.

Source: the domain `D = {z : ℂ | ‖z‖ < 1}` in Lyubich §4.4, Theorem 4.12,
printed p.113. On `D` this definition is exactly the supplied map. Values off
`D` impose no regularity condition and do not enter the family topology. -/
noncomputable def unitDiscExtension (f : C(Complex.UnitDisc, ℂ)) : ℂ → ℂ := by
  classical
  exact fun z => if hz : z ∈ Metric.ball (0 : ℂ) 1 then f ⟨z, hz⟩ else 0

/-- The normalized univalent family in Lyubich §4.4, Theorem 4.12, printed
p.113: a holomorphic injective map of the open unit disk fixing zero whose
complex derivative at zero has modulus one. Its derivative argument is free.

Continuity is already part of the disk-domain map type; it follows from
holomorphy for every map in the original family. The extension is used only
on the open disk, so this predicate does not require entire functions. -/
def IsNormalizedUnivalent (f : C(Complex.UnitDisc, ℂ)) : Prop :=
  DifferentiableOn ℂ (unitDiscExtension f) (Metric.ball (0 : ℂ) 1) ∧
    Function.Injective f ∧ f 0 = 0 ∧ ‖deriv (unitDiscExtension f) 0‖ = 1

end HolomorphicAnosov
