import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
import Mathlib.Topology.Instances.AddCircle.Real
import Mathlib.LinearAlgebra.Trace

open CategoryTheory
open scoped BigOperators
noncomputable section
universe u
namespace HolomorphicAnosov

/-- Basepoint change is independent of the connecting path when the receiving
 fundamental group embeds in the abelian winding group. Source: Hatcher's
 basepoint-change conjugation formula, pp.29–34; the inner conjugation vanishes. -/
theorem winding_basepoint_change_independent
    (n : ℕ) {X : Type u} [TopologicalSpace X] {x y : X}
    (w : FundamentalGroup X y ≃* Multiplicative (Fin n → ℤ))
    (p q : Path x y) (γ : FundamentalGroup X x) :
    FundamentalGroup.fundamentalGroupMulEquivOfPath p γ =
      FundamentalGroup.fundamentalGroupMulEquivOfPath q γ := by
  let α := (Groupoid.isoEquivHom (FundamentalGroupoid.mk x) (FundamentalGroupoid.mk y)).symm (Path.Homotopic.Quotient.mk p)
  let β := (Groupoid.isoEquivHom (FundamentalGroupoid.mk x) (FundamentalGroupoid.mk y)).symm (Path.Homotopic.Quotient.mk q)
  let l := α.symm ≪≫ β
  have hcomm : ∀ a b : FundamentalGroup X y, a * b = b * a := by
    intro a b
    apply w.injective
    simp only [map_mul, mul_comm]
  have hinner : l.conj (α.conj γ) = α.conj γ := by
    rw [CategoryTheory.Iso.conj_apply]
    have hc : l.inv ≫ α.conj γ = α.conj γ ≫ l.inv :=
      hcomm (α.conj γ) l.inv
    rw [← Category.assoc, hc, Category.assoc, l.inv_hom_id, Category.comp_id]
  have htrans : l.conj (α.conj γ) = β.conj γ := by
    rw [← CategoryTheory.Iso.trans_conj]
    simp [l, ← CategoryTheory.Iso.trans_assoc]
  exact hinner.symm.trans htrans


end HolomorphicAnosov
