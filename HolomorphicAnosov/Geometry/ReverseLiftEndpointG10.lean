import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
import Mathlib.Topology.Covering.Deck

namespace HolomorphicAnosov.Ghys

open Set _root_.Topology

universe u v

/-- The lift of a reversed loop ends at the image of the marked point under the deck transformation
corresponding to the original loop, when endpoints are indexed by inverse deck transformations. -/
theorem reverse_lift_endpoint_g10
    {M : Type u} {E : Type v} [TopologicalSpace M] [TopologicalSpace E]
    (p : E → M) (e0 : E) (δ : FundamentalGroup M (p e0) ≃* deck p)
    (hendpoint : ∀ (α : Path (p e0) (p e0)),
      ∃ β : Path e0
          ((δ (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk α)))⁻¹ • e0),
        ∀ t : unitInterval, p (β t) = α t) :
    ∀ (γ : FundamentalGroup M (p e0)) (α : Path (p e0) (p e0)),
      FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk α) = γ →
      ∃ β : Path e0 ((δ γ : E ≃ₜ E) e0),
        ∀ t : unitInterval, p (β t) = α.symm t := by
  intro γ α hα
  have hsymm : FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk α.symm) =
      γ⁻¹ := by
    subst γ
    rfl
  have h := hendpoint α.symm
  rw [hsymm, map_inv, inv_inv] at h
  exact h

end HolomorphicAnosov.Ghys
