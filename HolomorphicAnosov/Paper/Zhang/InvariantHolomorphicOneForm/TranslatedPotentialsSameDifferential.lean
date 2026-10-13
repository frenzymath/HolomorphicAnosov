import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Complex.Basic

open Set

open scoped _root_.Topology

noncomputable section
namespace HolomorphicAnosov.Paper.Zhang


universe u

/-- Scalar potentials differing by a constant near a point have equal complex differentials at that
point. (Zhang, Lemma 4.2) -/
theorem translated_potentials_same_differential
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (g h : E → ℂ) (x : E) (c : ℂ)
    (heq : h =ᶠ[𝓝 x] fun y ↦ g y + c) :
    fderiv ℂ h x = fderiv ℂ g x := by
  rw [heq.fderiv_eq, fderiv_add_const]


end HolomorphicAnosov.Paper.Zhang
