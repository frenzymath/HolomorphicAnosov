import HolomorphicAnosov.Paper.Zhang.IntegralToralMap
import HolomorphicAnosov.Topology.IntegralToralMapComp

namespace HolomorphicAnosov

/-- Invertibility of the original integer matrix makes the literal toral map
injective. Source: Manning's hyperbolic automorphism, Lemma 6; compose with its
integral inverse using the same-coordinate composition law. -/
theorem integral_toral_map_injective
    {n : ℕ} (A : Matrix.GeneralLinearGroup (Fin n) ℤ) :
    Function.Injective (integralToralMap A) := by
  have hid : ∀ x : UnitAddTorus (Fin n), integralToralMap 1 x = x := by
    intro x
    funext i
    change (∑ j : Fin n, (1 : Matrix (Fin n) (Fin n) ℤ) i j • x j) = x i
    simp [Matrix.one_apply]
  intro x y hxy
  have h := congrArg (integralToralMap A⁻¹) hxy
  simpa only [integral_toral_map_comp, inv_mul_cancel, hid] using h

end HolomorphicAnosov
