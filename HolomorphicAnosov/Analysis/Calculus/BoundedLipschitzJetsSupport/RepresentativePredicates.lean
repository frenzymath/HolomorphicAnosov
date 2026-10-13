import Mathlib.Analysis.Calculus.FDeriv.Defs
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.Order.LiminfLimsup

noncomputable section

namespace HolomorphicAnosov.BoundedLipschitzJets

open Filter Set
open scoped Topology _root_.Topology

variable (X Y : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- HPS pp. 26–27: a representative fixes zero and has a finite eventual slope bound. -/
def IsBoundedRepresentative (q : X → Y) : Prop :=
  q 0 = 0 ∧ ∃ C : ℝ, 0 ≤ C ∧
    ∀ᶠ x in 𝓝[≠] (0 : X), ‖q x‖ ≤ C * ‖x‖

/-- HPS pp. 26–27: the normalized difference from zero tends to zero.
This epsilon formulation also applies to the zero domain. -/
def IsLittleORepresentative (q : X → Y) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ x in 𝓝[≠] (0 : X), ‖q x‖ ≤ ε * ‖x‖


end HolomorphicAnosov.BoundedLipschitzJets
