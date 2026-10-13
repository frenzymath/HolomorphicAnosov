import Mathlib.LinearAlgebra.Projection
import Mathlib.Analysis.Complex.Basic

open Set

open scoped _root_.Topology

noncomputable section
namespace HolomorphicAnosov.Paper.Zhang


universe u

/-- Two points have the same stable projection coordinate exactly when their conjugacy coordinates
differ by a vector in the complementary unstable subspace. (Zhang, Lemma 4.2, p.14) -/
theorem stable_projection_fibre_iff
    {V Y : Type*} [AddCommGroup V] [Module ℝ V]
    (S U : Submodule ℝ V) (hSU : IsCompl S U)
    (H : Y → V) (φ : S ≃ ℂ) (y z : Y) :
    φ (S.projectionOnto U hSU (H y)) = φ (S.projectionOnto U hSU (H z)) ↔
      H y - H z ∈ U := by
  constructor
  · intro h
    have hp := φ.injective h
    apply (S.projectionOnto_apply_eq_zero_iff hSU).mp
    rw [map_sub, hp, sub_self]
  · intro h
    have hp := (S.projectionOnto_apply_eq_zero_iff hSU).mpr h
    rw [map_sub] at hp
    exact congrArg φ (sub_eq_zero.mp hp)


end HolomorphicAnosov.Paper.Zhang
