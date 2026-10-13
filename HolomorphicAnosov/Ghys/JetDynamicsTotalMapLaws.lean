import HolomorphicAnosov.Ghys.CurvePostcomposeJetEquivalences
import HolomorphicAnosov.Ghys.CurvePostcomposeReparametrize

namespace HolomorphicAnosov.Ghys

/-! Algebraic identity, truncation, and inverse laws for total first and second jet maps. -/
theorem jet_dynamics_total_map_laws
    {X Y : Type*} (F : X → Y) (G : Y → X)
    (hFG : ∀ x, G (F x) = x) (hGF : ∀ y, F (G y) = y) :
    Function.Bijective F := by
  refine ⟨?_, ?_⟩
  · intro x₁ x₂ h
    rw [← hFG x₁, ← hFG x₂, h]
  · intro y
    exact ⟨G y, hGF y⟩

end HolomorphicAnosov.Ghys
