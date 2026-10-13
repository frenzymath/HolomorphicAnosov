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

/-- A real lift with integer endpoint has that positive winding vector.
 Source: Hatcher's endpoint-fixed normal form for circle lifts, pp.29–31,
 applied coordinatewise. The two real paths are homotopic because the real
 vector space is contractible, and projection preserves that homotopy. -/
theorem winding_of_integer_endpoint_lift (n : ℕ)
    (w : FundamentalGroup (UnitAddTorus (Fin n)) 0 ≃* Multiplicative (Fin n → ℤ))
    (hnorm : ∀ z : Fin n → ℤ, ∃ p : Path (0 : UnitAddTorus (Fin n)) 0,
      (∀ (t : unitInterval) (j : Fin n),
        p t j = (((t : ℝ) * (z j : ℝ) : ℝ) : UnitAddCircle)) ∧
      w (FundamentalGroup.fromPath ⟦p⟧) = Multiplicative.ofAdd z)
    (p : Path (0 : UnitAddTorus (Fin n)) 0) (z : Fin n → ℤ)
    (l : Path (0 : Fin n → ℝ) (fun i ↦ (z i : ℝ)))
    (hl : ∀ t i, (l t i : UnitAddCircle) = p t i) :
    w (FundamentalGroup.fromPath ⟦p⟧) = Multiplicative.ofAdd z := by
  obtain ⟨p₀, hp₀, hw₀⟩ := hnorm z
  let s : Path (0 : Fin n → ℝ) (fun i ↦ (z i : ℝ)) :=
    { toFun := fun t i ↦ (t : ℝ) * (z i : ℝ)
      continuous_toFun := by fun_prop
      source' := by ext i; simp
      target' := by ext i; simp }
  let c : C(Fin n → ℝ, UnitAddTorus (Fin n)) :=
    ⟨fun x i ↦ (x i : UnitAddCircle), by fun_prop⟩
  have h0 : (0 : UnitAddTorus (Fin n)) = c 0 := by ext i; rfl
  have hz : (0 : UnitAddTorus (Fin n)) = c (fun i ↦ (z i : ℝ)) := by
    ext i
    exact ((AddCircle.coe_eq_zero_iff (1 : ℝ)).mpr ⟨z i, by simp⟩).symm
  have hpaths : (l.map c.continuous).cast h0 hz = p := by
    ext t i
    exact hl t i
  have hstraight : (s.map c.continuous).cast h0 hz = p₀ := by
    ext t i
    exact (hp₀ t i).symm
  have heq := congrArg (fun a : Path.Homotopic.Quotient
      (0 : Fin n → ℝ) (fun i ↦ (z i : ℝ)) ↦ (a.map c).cast h0 hz)
    (Path.Homotopic.Quotient.eq.mpr (SimplyConnectedSpace.paths_homotopic l s))
  simp only [← Path.Homotopic.Quotient.mk_map, ← Path.Homotopic.Quotient.mk_cast,
    hpaths, hstraight] at heq
  exact (congrArg w heq).trans hw₀


end HolomorphicAnosov
