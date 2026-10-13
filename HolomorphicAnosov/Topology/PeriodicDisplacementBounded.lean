import HolomorphicAnosov.Linear.HyperbolicRealSplitting
import HolomorphicAnosov.Topology.InvertibleLinearLocalDegree
import HolomorphicAnosov.Topology.TorusStandardWinding
import HolomorphicAnosov.Topology.EuclideanFixedPointIndex
import HolomorphicAnosov.Paper.Zhang.IntegralToralMap
import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Instances.AddCircle.Real
import Mathlib.Topology.Homotopy.Path
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.FieldTheory.IsAlgClosed.Spectrum
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Topology.Covering.Basic
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Topology.Covering.AddCircle
import Mathlib.Algebra.Module.ZLattice.Basic

/-! Public auxiliary result used by torus lift fixed-point existence. -/

universe u

noncomputable section

open scoped ContDiff

namespace HolomorphicAnosov.Topology

/-- Integer-periodic continuous displacement is uniformly bounded on the original
finite coordinate space; every vector reduces by its coordinate floors to the compact cube. -/
theorem periodic_displacement_bounded (n : ℕ)
    (e : C((Fin n → ℝ), (Fin n → ℝ)))
    (he : ∀ v (z : Fin n → ℤ), e (v + fun i ↦ (z i : ℝ)) = e v) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ v, ‖e v‖ ≤ K := by
  let cube : Set (Fin n → ℝ) := Set.Icc 0 1
  obtain ⟨B, hB⟩ := (isCompact_Icc : IsCompact cube).exists_bound_of_continuousOn
    e.continuous.continuousOn
  refine ⟨max 0 B, le_max_left _ _, ?_⟩
  intro v
  let z : Fin n → ℤ := fun i ↦ -⌊v i⌋
  let w : Fin n → ℝ := v + fun i ↦ (z i : ℝ)
  have hw : w ∈ cube := by
    constructor
    · intro i
      change 0 ≤ v i + ((-⌊v i⌋ : ℤ) : ℝ)
      rw [Int.cast_neg]
      linarith [Int.floor_le (v i)]
    · intro i
      change v i + ((-⌊v i⌋ : ℤ) : ℝ) ≤ 1
      rw [Int.cast_neg]
      linarith [Int.lt_floor_add_one (v i)]
  have heq : e w = e v := he v z
  exact (heq ▸ hB w hw).trans (le_max_right _ _)


end HolomorphicAnosov.Topology
