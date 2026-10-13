import HolomorphicAnosov.Topology.TorusStandardWinding
import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
import Mathlib.Topology.ContinuousMap.Algebra
import Mathlib.Topology.Covering.Basic
import Mathlib.Topology.Covering.Deck

/-! Public winding lemmas for the standard torus covering.
Source: Franks (1970), pp. 70–71; these are the path-lift and uniqueness
calculations used to identify winding coordinates. -/

namespace HolomorphicAnosov

open _root_.Topology

theorem winding_integral_loop {n : ℕ}
    (cov : IsCoveringMap (fun x : Fin n → ℝ ↦ fun j ↦ (x j : UnitAddCircle)))
    (zeroT : (fun x : Fin n → ℝ ↦ fun j ↦ (x j : UnitAddCircle)) ⁻¹'
      {(0 : UnitAddTorus (Fin n))}) (hz : (zeroT : Fin n → ℝ) = 0)
    (w : FundamentalGroup (UnitAddTorus (Fin n)) 0 ≃* Multiplicative (Fin n → ℤ))
    (hw : ∀ q : FundamentalGroup (UnitAddTorus (Fin n)) 0,
      (cov.monodromy (FundamentalGroup.toPath q) zeroT : Fin n → ℝ) =
        fun j ↦ ((w q).toAdd j : ℝ))
    (z : Fin n → ℤ) (p : Path (0 : UnitAddTorus (Fin n)) 0)
    (hp : ∀ (t : unitInterval) (j : Fin n), p t j =
      (((t : ℝ) * (z j : ℝ) : ℝ) : UnitAddCircle)) :
    w (FundamentalGroup.fromPath ⟦p⟧) = Multiplicative.ofAdd z := by
  let l : C(unitInterval, Fin n → ℝ) :=
    ⟨fun t j ↦ (t : ℝ) * (z j : ℝ),
      continuous_pi fun j ↦ continuous_subtype_val.mul_const _⟩
  have hl : l = cov.liftPath p zeroT (p.source.trans zeroT.2.symm) := by
    apply (cov.eq_liftPath_iff' _).mpr
    constructor
    · funext t
      ext j
      exact (hp t j).symm
    · change (fun j ↦ (0 : ℝ) * (z j : ℝ)) = (zeroT : Fin n → ℝ)
      rw [hz]
      ext j
      simp
  have hm : (cov.monodromy (FundamentalGroup.toPath
      (FundamentalGroup.fromPath ⟦p⟧)) zeroT : Fin n → ℝ) = fun j ↦ (z j : ℝ) := by
    change cov.liftPath p zeroT (p.source.trans zeroT.2.symm) 1 = _
    rw [← hl]
    ext j
    simp [l]
  have hw' := hw (FundamentalGroup.fromPath ⟦p⟧)
  apply congrArg Multiplicative.ofAdd
  apply funext
  intro j
  apply Int.cast_injective (α := ℝ)
  exact congrFun (hw'.symm.trans hm) j

theorem winding_equiv_unique {n : ℕ}
    (cov : IsCoveringMap (fun x : Fin n → ℝ ↦ fun j ↦ (x j : UnitAddCircle)))
    (zeroT : (fun x : Fin n → ℝ ↦ fun j ↦ (x j : UnitAddCircle)) ⁻¹'
      {(0 : UnitAddTorus (Fin n))}) (hz : (zeroT : Fin n → ℝ) = 0)
    (w : FundamentalGroup (UnitAddTorus (Fin n)) 0 ≃* Multiplicative (Fin n → ℤ))
    (hw : ∀ q : FundamentalGroup (UnitAddTorus (Fin n)) 0,
      (cov.monodromy (FundamentalGroup.toPath q) zeroT : Fin n → ℝ) =
        fun j ↦ ((w q).toAdd j : ℝ))
    (e : FundamentalGroup (UnitAddTorus (Fin n)) 0 ≃* Multiplicative (Fin n → ℤ))
    (he : ∀ z : Fin n → ℤ,
      ∃ p : Path (0 : UnitAddTorus (Fin n)) 0,
        (∀ (t : unitInterval) (j : Fin n),
          p t j = (((t : ℝ) * (z j : ℝ) : ℝ) : UnitAddCircle)) ∧
        e (FundamentalGroup.fromPath ⟦p⟧) = Multiplicative.ofAdd z) : w = e := by
  apply MulEquiv.ext
  intro q
  obtain ⟨p, hp, hep⟩ := he (e q).toAdd
  have hpq : FundamentalGroup.fromPath ⟦p⟧ = q := e.injective hep
  rw [← hpq]
  exact (winding_integral_loop cov zeroT hz w hw _ p hp).trans hep.symm


end HolomorphicAnosov
