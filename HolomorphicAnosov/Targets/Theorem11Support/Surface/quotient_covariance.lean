import HolomorphicAnosov.Paper.Zhang.TorusModel
import HolomorphicAnosov.Geometry.Manifold.ComplexTorus.Quotient
import HolomorphicAnosov.Geometry.Manifold.ComplexTorus.LatticeLinearEquiv
import HolomorphicAnosov.Paper.Zhang.IntegralToralMap

/-!
Lattice quotient coordinates intertwine a lattice automorphism with its integral toral map. (Brin–Stuck, §1.7, pp.14–15; Zhang, §2, p.4)
-/

noncomputable section

namespace HolomorphicAnosov.Surface11SupportW06

universe u

/-- If real coordinates intertwine `B.linear` with `A`, the induced quotient coordinates intertwine
`quotientLinearEquiv B` with `integralToralMap A`. (Zhang, Theorem 1.1) -/
theorem quotient_covariance {d n : ℕ} (L : FullComplexLattice d)
    (B : LatticeLinearEquiv L)
    (P : ComplexModel d ≃L[ℝ] (Fin n → ℝ))
    (A : Matrix.GeneralLinearGroup (Fin n) ℤ)
    (q : ComplexTorus L ≃ₜ UnitAddTorus (Fin n))
    (hq : ∀ (v : ComplexModel d) (i : Fin n),
      q (QuotientAddGroup.mk v) i = (P v i : AddCircle (1 : ℝ)))
    (hPB : ∀ v : ComplexModel d, ∀ i,
      P (B.linear v) i = ∑ j, (A i j : ℝ) * P v j)
    (z : ComplexTorus L) :
    q (quotientLinearEquiv B z) = integralToralMap A (q z) := by
  induction z using QuotientAddGroup.induction_on with
  | H v =>
    have hq' : ∀ v : ComplexModel d,
        q (QuotientAddGroup.mk v) = fun i ↦ (P v i : AddCircle (1 : ℝ)) :=
      fun v ↦ funext (hq v)
    have hb : quotientLinearEquiv B (QuotientAddGroup.mk v) =
        QuotientAddGroup.mk (B.linear v) := rfl
    rw [hb, hq', hq']
    funext i
    simp only [integralToralMap, hPB]
    change (QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℝ)))
      (∑ j, (A i j : ℝ) * P v j) = _
    rw [map_sum]
    congr 1
    funext j
    rw [← zsmul_eq_mul, map_zsmul]
    rfl

end HolomorphicAnosov.Surface11SupportW06

