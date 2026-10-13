import HolomorphicAnosov.Topology.PairedSignedSumDistinguished
import Mathlib.Algebra.BigOperators.Fin

open scoped BigOperators
namespace HolomorphicAnosov.Topology

/-- If each triangle boundary vanishes in an abelian group and all its signed
edge occurrences cancel in pairs except a positive distinguished edge, that
edge has zero class. Source: Hatcher, Algebraic Topology, Theorem 2A.1 proof
p.167. Sum the triangle boundary equations with their integer coefficients.
Expand the three alternating faces and regroup as a sum over occurrences.
Paired opposite coefficients cancel and leave the distinguished edge alone.
The abelian group may have torsion; triangle signs need not be restricted to
plus or minus one for this algebraic conclusion. -/
theorem pairedTriangle_boundary_sum_zero {A : Type*} [AddCommGroup A] (m : ℕ)
    (ε : Fin m → ℤ) (label : Fin m × Fin 3 → A)
    (d : Fin m × Fin 3) (pair : Fin m × Fin 3 → Fin m × Fin 3)
    (hpair : Function.Involutive pair) (hd : pair d = d)
    (hfree : ∀ o, o ≠ d → pair o ≠ o)
    (hsign : ∀ o, o ≠ d →
      ε (pair o).1 * (-1 : ℤ) ^ (pair o).2.val = -(ε o.1 * (-1 : ℤ) ^ o.2.val))
    (hlabel : ∀ o, label (pair o) = label o)
    (hdpos : ε d.1 * (-1 : ℤ) ^ d.2.val = 1)
    (htriangle : ∀ i, label (i, 0) - label (i, 1) + label (i, 2) = 0) :
    label d = 0 := by
  have hsum := pairedSigned_sum_distinguished d pair hpair hd hfree
    (fun o ↦ ε o.1 * (-1 : ℤ) ^ o.2.val) label hsign hlabel
  rw [hdpos, one_zsmul] at hsum
  rw [← hsum, Fintype.sum_prod_type]
  apply Finset.sum_eq_zero
  intro i _
  simpa [Fin.sum_univ_succ, mul_zsmul, sub_eq_add_neg, zsmul_add, zsmul_neg, zsmul_zero, add_assoc] using
    congrArg (fun a ↦ ε i • a) (htriangle i)

end HolomorphicAnosov.Topology
