import HolomorphicAnosov.Topology.TorusWindingOfLift
import HolomorphicAnosov.Topology.TorusLoopIntegerLift
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

/-- The normalized winding equivalence has exactly the real-lift characterization
 used by the determinant theorem. Source: Hatcher Theorem1.7 pp.29–31;
 existence of lifts and the endpoint-fixed real homotopy were proved above. -/
theorem normalized_winding_lift_characterization (n : ℕ)
    (w : FundamentalGroup (UnitAddTorus (Fin n)) 0 ≃* Multiplicative (Fin n → ℤ))
    (hnorm : ∀ z : Fin n → ℤ, ∃ p : Path (0 : UnitAddTorus (Fin n)) 0,
      (∀ (t : unitInterval) (j : Fin n),
        p t j = (((t : ℝ) * (z j : ℝ) : ℝ) : UnitAddCircle)) ∧
      w (FundamentalGroup.fromPath ⟦p⟧) = Multiplicative.ofAdd z) :
    ∀ (p : Path (0 : UnitAddTorus (Fin n)) 0) (z : Fin n → ℤ),
      w (FundamentalGroup.fromPath ⟦p⟧) = Multiplicative.ofAdd z ↔
        ∃ l : Path (0 : Fin n → ℝ) (fun i ↦ (z i : ℝ)),
          ∀ t i, (l t i : UnitAddCircle) = p t i := by
  intro p z
  constructor
  · intro hw
    obtain ⟨z₀, l, hl⟩ := torus_loop_integer_endpoint_lift n p
    have hz : z₀ = z := by
      exact (winding_of_integer_endpoint_lift n w hnorm p z₀ l hl).symm.trans hw
    subst z₀
    exact ⟨l, hl⟩
  · rintro ⟨l, hl⟩
    exact winding_of_integer_endpoint_lift n w hnorm p z l hl



end HolomorphicAnosov
