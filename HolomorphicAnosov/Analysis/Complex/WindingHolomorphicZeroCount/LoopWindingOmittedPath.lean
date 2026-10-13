import HolomorphicAnosov.Analysis.Complex.WindingNumber
import Mathlib.Analysis.Meromorphic.FactorizedRational
import Mathlib.Topology.ContinuousMap.Algebra
import Mathlib.Analysis.Complex.CoveringMap
import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.Analytic.Order
import HolomorphicAnosov.Analysis.Complex.WindingHolomorphicZeroCount.Definitions
import HolomorphicAnosov.Analysis.Complex.WindingHolomorphicZeroCount.LoopWindingLift
import HolomorphicAnosov.Analysis.Complex.WindingHolomorphicZeroCount.LoopWindingEqOfIncrement
import HolomorphicAnosov.Analysis.Complex.WindingHolomorphicZeroCount.LoopWindingHomotopy

open Set Bundle TopologicalSpace
open scoped Topology _root_.Topology
namespace HolomorphicAnosov
noncomputable section


lemma loopWinding_omittedPath (γ : ComplexLoop) (b₀ b₁ : ℂ)
    (hb₀ : ∀ z, γ z ≠ b₀) (hb₁ : ∀ z, γ z ≠ b₁)
    (h : OmittedValuePath γ b₀ b₁) : loopWinding γ b₀ hb₀ = loopWinding γ b₁ hb₁ := by
  obtain ⟨p, hp⟩ := h
  let γ' : ComplexLoop := ⟨fun z ↦ γ z - b₀ + b₁, by fun_prop⟩
  have hb' : ∀ z, γ' z ≠ b₁ := by
    intro z hz
    apply hb₀ z
    dsimp [γ'] at hz
    linear_combination hz
  have hh := loopWinding_homotopy γ' γ b₁ hb' hb₁ (by
    refine ⟨⟨fun tz ↦ γ tz.2 - p tz.1 + b₁, by fun_prop⟩, ?_, ?_, ?_⟩
    · intro z
      simp [γ']
    · intro z
      simp
    · intro t z hz
      apply hp t z
      dsimp at hz
      linear_combination -hz)
  have he : puncturedLoopPath γ b₀ hb₀ = puncturedLoopPath γ' b₁ hb' := by
    ext t
    dsimp [puncturedLoopPath, γ']
    ring_nf
  obtain ⟨L, hL, hi⟩ := loopWinding_lift γ' b₁ hb'
  have hw := loopWinding_eq_of_increment γ b₀ hb₀ L (by
    intro t
    rw [he]
    exact hL t) (loopWinding γ' b₁ hb') (by linear_combination hi)
  exact hw.trans hh


end
end HolomorphicAnosov
