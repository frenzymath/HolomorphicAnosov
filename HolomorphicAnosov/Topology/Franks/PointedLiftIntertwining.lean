import HolomorphicAnosov.Topology.OriginalTorusLiftFixedPointExistence
import HolomorphicAnosov.Topology.FranksMatrixAction

/-!
# Pointed lift compatibility on the original torus pullback

Franks (1970), Proposition (2.1), pp.70–71, compares the pointed lifts of the
semiconjugacy square. Hatcher Proposition 1.34, p.62, gives uniqueness on the
connected covering domain. The carrier here is the original pullback, not a
replacement smooth structure. The argument works in every finite dimension.
-/

open Set _root_.Topology
namespace HolomorphicAnosov.Topology

/-- A pointed lift of a toral semiconjugacy intertwines the chosen pointed source
lift with the actual real matrix action, and hence intertwines every forward iterate.

Proof: projection of the finite real matrix sum equals the integer toral action.
Thus `H ∘ F` and `realAction A ∘ H` lift the same downstairs map. The original
pullback is homeomorphic to real coordinate space via the second coordinate,
so it is connected. Both lifts vanish at the specified fixed point. Covering-map
uniqueness proves equality, and iteration follows from `Function.Semiconj`.

Source: Franks, Anosov Diffeomorphisms (1970), Proposition (2.1), pp.70–71;
Hatcher, Algebraic Topology, Proposition 1.34, p.62. No hyperbolicity or
surjectivity of the semiconjugacy is needed for this compatibility step.
-/
theorem pointed_pullback_lift_intertwining
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    (q : M ≃ₜ UnitAddTorus (Fin n)) (u0 : OriginalTorusPullback q)
    (f : M → M) (A : Matrix.GeneralLinearGroup (Fin n) ℤ)
    (k : M → UnitAddTorus (Fin n))
    (hk : ∀ x, k (f x) = integralToralMap A (k x))
    (F : C(OriginalTorusPullback q, OriginalTorusPullback q))
    (hF : ∀ x, (F x).val.1 = f x.val.1) (hF0 : F u0 = u0)
    (H : C(OriginalTorusPullback q, Fin n → ℝ)) (hH0 : H u0 = 0)
    (hH : ∀ x, coordinateProjection n (H x) = k x.val.1) :
    Function.Semiconj H F (FranksMatrix.realAction A) ∧
      ∀ r : ℕ, ∀ x, H (F^[r] x) = (FranksMatrix.realAction A)^[r] (H x) := by
  classical
  let Q : OriginalTorusPullback q ≃ₜ (Fin n → ℝ) := {
    toFun := fun x ↦ x.val.2
    invFun := fun v ↦ ⟨(q.symm (originalTorusProjection n v), v), q.apply_symm_apply _⟩
    left_inv := fun x ↦ by
      apply Subtype.ext
      apply Prod.ext
      · exact (congrArg q.symm x.property).symm.trans (q.symm_apply_apply _)
      · rfl
    right_inv := fun _ ↦ rfl
    continuous_toFun := continuous_snd.comp continuous_subtype_val
    continuous_invFun := ((q.symm.continuous.comp (originalTorusProjection n).continuous).prodMk
      continuous_id).subtype_mk _ }
  have : SimplyConnectedSpace (OriginalTorusPullback q) :=
    Q.toHomotopyEquiv.simplyConnectedSpace
  have hprojA (v : Fin n → ℝ) :
      coordinateProjection n (FranksMatrix.realAction A v) =
        integralToralMap A (coordinateProjection n v) := by
    ext i
    simp only [coordinateProjection, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
      FranksMatrix.realAction_apply, integralToralMap]
    simp only [← AddCircle.coe_zsmul, zsmul_eq_mul]
    exact map_sum (QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℝ))) _ _
  have hcomp : coordinateProjection n ∘ (fun x ↦ H (F x)) =
      coordinateProjection n ∘ (fun x ↦ FranksMatrix.realAction A (H x)) := by
    funext x
    exact (hH (F x)).trans ((congrArg k (hF x)).trans
      ((hk x.val.1).trans ((congrArg (integralToralMap A) (hH x)).symm.trans
        (hprojA (H x)).symm)))
  have heq := (coordinateProjection_cover n).isCoveringMap.eq_of_comp_eq
    (H.continuous.comp F.continuous)
    ((FranksMatrix.realAction A).toContinuousLinearEquiv.continuous.comp H.continuous)
    hcomp u0 (by simp only [Function.comp_apply, hF0, hH0, map_zero])
  have hsem : Function.Semiconj H F (FranksMatrix.realAction A) := congrFun heq
  exact ⟨hsem, fun r x ↦ hsem.iterate_right r x⟩

end HolomorphicAnosov.Topology
