import HolomorphicAnosov.Paper.Zhang.IntegralToralMap

/-!
The coordinate projection from real space to the unit torus is an additive homomorphism. (Brin–Stuck, §1.7, pp.14–15)
-/

noncomputable section

namespace HolomorphicAnosov.Theorem11SupportW03

universe u
open Set Function

/-- The additive map sending each real coordinate to its class modulo one. -/
def coordinateProjection (n : ℕ) : (Fin n → ℝ) →+ UnitAddTorus (Fin n) where
  toFun x i := (x i : AddCircle (1 : ℝ))
  map_zero' := by ext i; rfl
  map_add' x y := by ext i; exact AddCircle.coe_add _ _ _

end HolomorphicAnosov.Theorem11SupportW03

