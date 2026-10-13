import Mathlib.LinearAlgebra.Projection
import Mathlib.Analysis.Complex.Basic

open Set

open scoped _root_.Topology

noncomputable section
namespace HolomorphicAnosov.Paper.Zhang


universe u

/-- A deck map acting by translation in conjugacy coordinates preserves the fibres of the stable
projection. (Zhang, Lemma 4.2) -/
theorem stable_projection_deck_preserves_fibres
    {V Y : Type*} [AddCommGroup V] [Module ℝ V]
    (U : Submodule ℝ V) (H : Y → V) (q : Y → ℂ)
    (hfibre : ∀ y z, q y = q z ↔ H y - H z ∈ U)
    (D : Y → Y) (gamma : V) (hD : ∀ y, H (D y) = H y + gamma) :
    ∀ y z, q y = q z → q (D y) = q (D z) := by
  intro y z h
  apply (hfibre _ _).mpr
  rw [hD y, hD z, add_sub_add_right_eq_sub]
  exact (hfibre y z).mp h


end HolomorphicAnosov.Paper.Zhang
