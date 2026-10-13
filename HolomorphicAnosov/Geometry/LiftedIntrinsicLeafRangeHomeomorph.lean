import HolomorphicAnosov.Geometry.LiftedIntrinsicLeafRange

namespace HolomorphicAnosov.Theorem12LiftedFoliationAssembly
open Set
noncomputable section
universe u v w z

/-- A pointed intrinsic homeomorphism preserves the literal lifted path range (Hatcher path lifting pp.60--62, applied to the actual same-point native rebase homeomorphism).-/
theorem lifted_range_homeomorph
    {X : Type u} {Y : Type v} {L : Type w} {L' : Type z}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace L]
    [TopologicalSpace L'] (p : Y → X) (j : L → X) (j' : L' → X)
    (T : L ≃ₜ L') (hj : ∀ t, j' (T t) = j t) (a : L) (y : Y) :
    liftedIntrinsicLeafRange p j a y = liftedIntrinsicLeafRange p j' (T a) y := by
  ext q
  constructor
  · rintro ⟨b, γ, η, h⟩
    exact ⟨T b, γ.map T.continuous, η, fun t ↦ (h t).trans (hj (γ t)).symm⟩
  · rintro ⟨b, γ, η, h⟩
    let γ' : Path a (T.symm b) :=
      (γ.map T.symm.continuous).cast (T.symm_apply_apply a).symm rfl
    refine ⟨T.symm b, γ', η, ?_⟩
    intro t
    exact (h t).trans ((congrArg j' (T.apply_symm_apply (γ t))).symm.trans
      (hj (T.symm (γ t))))

end
end HolomorphicAnosov.Theorem12LiftedFoliationAssembly

