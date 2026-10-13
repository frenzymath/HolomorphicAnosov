import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup

namespace HolomorphicAnosov

/-- A constant based continuous map induces the trivial fundamental-group homomorphism.
Source: Hatcher, Algebraic Topology, §1.1, the constant-loop identity element;
Mathlib's `FundamentalGroup.mapOfEq` acts by postcomposition on loop classes. -/
theorem constant_continuousMap_mapOfEq
    {X : Type*} {Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (x₀ : X) (y₀ : Y) :
    FundamentalGroup.mapOfEq
      (⟨fun _ : X ↦ y₀, continuous_const⟩ : C(X, Y))
      (show (⟨fun _ : X ↦ y₀, continuous_const⟩ : C(X, Y)) x₀ = y₀ from rfl) =
      1 := by
  ext γ
  rw [FundamentalGroup.mapOfEq_apply]
  change (Path.Homotopic.Quotient.map γ
      (⟨fun _ : X ↦ y₀, continuous_const⟩ : C(X, Y))).cast _ _ = _
  induction γ using Path.Homotopic.Quotient.ind with
  | mk p =>
    change Path.Homotopic.Quotient.mk _ = Path.Homotopic.Quotient.refl y₀
    apply Quotient.sound
    exact Path.Homotopic.refl _

end HolomorphicAnosov
