import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
import Mathlib.Topology.Instances.AddCircle.Real
import Mathlib.Topology.Covering.AddCircle
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Analysis.Convex.Contractible

open CategoryTheory
open scoped BigOperators
noncomputable section
universe u
namespace HolomorphicAnosov

/-- Every torus loop lifts from zero to an integer vector, by lifting each
 coordinate through the genuine quotient-circle covering. Source: Hatcher
 Theorem1.7 and its path-lifting proof, pp.29–31. -/
theorem torus_loop_integer_endpoint_lift (n : ℕ)
    (p : Path (0 : UnitAddTorus (Fin n)) 0) :
    ∃ (z : Fin n → ℤ) (l : Path (0 : Fin n → ℝ) (fun i ↦ (z i : ℝ))),
      ∀ t i, (l t i : UnitAddCircle) = p t i := by
  classical
  let c : IsCoveringMap ((↑) : ℝ → UnitAddCircle) := AddCircle.isCoveringMap_coe 1
  let γ : Fin n → C(unitInterval, UnitAddCircle) := fun i ↦
    ⟨fun t ↦ p t i, (continuous_apply i).comp p.continuous⟩
  have hγ : ∀ i, γ i 0 = ((0 : ℝ) : UnitAddCircle) := by
    intro i
    change p 0 i = 0
    rw [p.source]
    rfl
  let L : Fin n → C(unitInterval, ℝ) := fun i ↦ c.liftPath (γ i) 0 (hγ i)
  have hL : ∀ i t, (L i t : UnitAddCircle) = p t i := by
    intro i t
    exact congrFun (c.liftPath_lifts (γ i) 0 (hγ i)) t
  have hz : ∀ i, ∃ z : ℤ, (z : ℝ) = L i 1 := by
    intro i
    have hi : (L i 1 : UnitAddCircle) = 0 := by rw [hL, p.target]; rfl
    obtain ⟨z, hz⟩ := (AddCircle.coe_eq_zero_iff (1 : ℝ)).mp hi
    exact ⟨z, by simpa using hz⟩
  choose z hz using hz
  refine ⟨z, { toFun := fun t i ↦ L i t, continuous_toFun := by fun_prop
               source' := ?_, target' := ?_ }, ?_⟩
  · ext i
    exact c.liftPath_zero (γ i) 0 (hγ i)
  · ext i
    exact (hz i).symm
  · exact fun t i ↦ hL i t


end HolomorphicAnosov
