import HolomorphicAnosov.Topology.FranksIntegralToralContinuousMap
import HolomorphicAnosov.Topology.FranksWindingLemmas
import HolomorphicAnosov.Topology.TorusStandardWinding
import HolomorphicAnosov.Paper.Zhang.IntegralToralMap
import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
import Mathlib.Topology.ContinuousMap.Algebra
import Mathlib.Topology.Covering.Basic
import Mathlib.Topology.Covering.Deck

/-! The induced winding-coordinate action of the canonical integral toral map.
Source: Franks (1970), pp. 70–71, together with the standard torus winding theorem. -/

namespace HolomorphicAnosov

open _root_.Topology

theorem winding_matrix_action {n : ℕ}
    (cov : IsCoveringMap (fun x : Fin n → ℝ ↦ fun j ↦ (x j : UnitAddCircle)))
    (zeroT : (fun x : Fin n → ℝ ↦ fun j ↦ (x j : UnitAddCircle)) ⁻¹'
      {(0 : UnitAddTorus (Fin n))}) (hz : (zeroT : Fin n → ℝ) = 0)
    (w : FundamentalGroup (UnitAddTorus (Fin n)) 0 ≃* Multiplicative (Fin n → ℤ))
    (hw : ∀ q : FundamentalGroup (UnitAddTorus (Fin n)) 0,
      (cov.monodromy (FundamentalGroup.toPath q) zeroT : Fin n → ℝ) =
        fun j ↦ ((w q).toAdd j : ℝ))
    (A : Matrix.GeneralLinearGroup (Fin n) ℤ)
    (ha : franksIntegralToralContinuousMap A 0 = 0)
    (γ : FundamentalGroup (UnitAddTorus (Fin n)) 0) :
    (w (FundamentalGroup.mapOfEq (franksIntegralToralContinuousMap A) ha γ)).toAdd =
      Matrix.mulVec (A : Matrix (Fin n) (Fin n) ℤ) (w γ).toAdd := by
  obtain ⟨e, he, _, heA⟩ := torus_pi1_standard_winding n
  have hwe := winding_equiv_unique cov zeroT hz w hw e he
  obtain ⟨F, hF, hFzero, hmatrix⟩ := heA A
  have hFeq : F = franksIntegralToralContinuousMap A := by
    apply ContinuousMap.ext
    intro x
    rw [hF x]
    ext i
    simp [franksIntegralToralContinuousMap, integralToralMap, ContinuousMap.pi]
  subst F
  simpa only [hwe] using hmatrix γ


end HolomorphicAnosov
