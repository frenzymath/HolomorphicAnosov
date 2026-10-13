import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Tactic.Linarith

/-!
# Choosing a continuous extension with controlled image diameter

Source: Hatcher, *Algebraic Topology*, Theorem A.7, printed p.526, the choice
of cell extensions with image diameter within a factor of two of the infimum.
The constant-boundary case is handled separately, since its infimum can be zero.
-/

namespace HolomorphicAnosov

open Set

/-- A prescribed map on a nonempty subset of a compact space, if extendible,
has an extension whose image diameter is at most twice that of every extension.

Source: Hatcher, *Algebraic Topology*, Theorem A.7, printed p.526. This is an
agent-written expansion of the factor-two choice in the neighborhood-retraction
construction, including the zero-infimum case omitted in the printed argument.

Proof: If the prescribed map is constant, choose the constant extension; its
image has diameter zero. Otherwise choose two prescribed values at positive
distance b. Every extension image is compact and contains these values, so its
diameter is at least b. The nonempty set S of extension-image diameters is bounded
below by b>0. Therefore a=inf S is positive. Choose a member of S less than 2a;
since a is at most each member of S, its associated extension has the required
bound. Nonemptiness of the prescribed subset supplies a constant value in the
constant case. No separation hypothesis on the source space is required. -/
theorem exists_continuous_extension_diam_le_two_mul
    {X Y : Type*} [TopologicalSpace X] [CompactSpace X] [MetricSpace Y]
    (A : Set X) (hA : A.Nonempty) (f : C(A, Y))
    (hex : ∃ g : C(X, Y), ∀ a : A, g a = f a) :
    ∃ g : C(X, Y), (∀ a : A, g a = f a) ∧
      ∀ h : C(X, Y), (∀ a : A, h a = f a) →
        Metric.diam (range g) ≤ 2 * Metric.diam (range h) := by
  classical
  by_cases hf : ∃ y : Y, ∀ a : A, f a = y
  · obtain ⟨y, hy⟩ := hf
    refine ⟨ContinuousMap.const X y, fun a ↦ (hy a).symm, ?_⟩
    intro h hh
    have hg : (range (ContinuousMap.const X y)).Subsingleton := by
      rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
      rfl
    rw [Metric.diam_subsingleton hg]
    exact mul_nonneg (by norm_num) Metric.diam_nonneg
  · obtain ⟨a, ha⟩ := hA
    have hne : ∃ b : A, f b ≠ f ⟨a, ha⟩ := by
      by_contra h
      push Not at h
      exact hf ⟨f ⟨a, ha⟩, h⟩
    obtain ⟨b, hb⟩ := hne
    let S : Set ℝ := {d | ∃ g : C(X, Y), (∀ a : A, g a = f a) ∧
      d = Metric.diam (range g)}
    have hS : S.Nonempty := by
      obtain ⟨g, hg⟩ := hex
      exact ⟨_, g, hg, rfl⟩
    have hlower : ∀ d ∈ S, dist (f b) (f ⟨a, ha⟩) ≤ d := by
      rintro d ⟨g, hg, rfl⟩
      rw [← hg b, ← hg ⟨a, ha⟩]
      exact Metric.dist_le_diam_of_mem (isCompact_range g.continuous).isBounded
        (mem_range_self _) (mem_range_self _)
    have hpos : 0 < sInf S :=
      (dist_pos.mpr hb).trans_le (le_csInf hS hlower)
    obtain ⟨d, ⟨g, hg, rfl⟩, hd⟩ :=
      exists_lt_of_csInf_lt hS (show sInf S < 2 * sInf S by linarith)
    refine ⟨g, hg, ?_⟩
    intro h hh
    exact hd.le.trans (mul_le_mul_of_nonneg_left
      (csInf_le ⟨_, hlower⟩ (show Metric.diam (range h) ∈ S from ⟨h, hh, rfl⟩))
      (by norm_num))


end HolomorphicAnosov
