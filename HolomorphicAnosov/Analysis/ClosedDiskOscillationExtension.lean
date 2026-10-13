import HolomorphicAnosov.Topology.ContinuousExtensionOfLocalOscillation
import Mathlib.Analysis.Normed.Module.RCLike.Real
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Closed-disk extension from shrinking image caps

Source: Tao, 246C Notes 2 (12 April 2018), Theorem 20, continuous-extension
part of the proof. The target may be any complete metric space.
-/
open Set Filter Metric
open scoped Topology _root_.Topology
namespace HolomorphicAnosov.Analysis

/-- If a continuous map on the open unit disk has image caps with diameter
tending to zero at every circle point, it has a unique continuous extension
to the closed disk. Every cap radius is positive. No monotonicity or convergence
of the radii is needed: arbitrarily small image oscillation in a neighborhood
of each boundary point suffices.

Source: Tao 246C Notes 2, Theorem 20, first extension step, expanded using the
local-oscillation extension theorem. In the interior, continuity controls both
values by half the requested error. At a boundary point, choose a cap whose
extended diameter is smaller than that error. The open disk is dense in the
closed disk, so the generic extension theorem applies. Its uniqueness is
uniqueness of the literal function on the closed disk. -/
theorem exists_unique_closed_disk_extension_of_shrinking_caps
    {Y : Type*} [MetricSpace Y] [CompleteSpace Y]
    (f : ball (0 : ℂ) 1 → Y) (hf : Continuous f)
    (hcaps : ∀ ζ ∈ sphere (0 : ℂ) 1, ∃ r : ℕ → ℝ,
      (∀ n, 0 < r n) ∧
      Tendsto (fun n ↦ ediam (f '' {z : ball (0 : ℂ) 1 | dist (z : ℂ) ζ < r n}))
        atTop (𝓝 0)) :
    ∃! F : closedBall (0 : ℂ) 1 → Y,
      Continuous F ∧ ∀ a : ball (0 : ℂ) 1,
        F ⟨a, ball_subset_closedBall a.property⟩ = f a := by
  let S : Set (closedBall (0 : ℂ) 1) := {z | (z : ℂ) ∈ ball (0 : ℂ) 1}
  have hS : Dense S := by
    rw [Subtype.dense_iff]
    have he : (Subtype.val : closedBall (0 : ℂ) 1 → ℂ) '' S = ball (0 : ℂ) 1 := by
      ext z
      constructor
      · rintro ⟨a, ha, rfl⟩
        exact ha
      · intro hz
        exact ⟨⟨z, ball_subset_closedBall hz⟩, hz, rfl⟩
    rw [he, closure_ball (0 : ℂ) one_ne_zero]
  let g : S → Y := fun a ↦ f ⟨a.val.val, a.property⟩
  have hosc : ∀ x : closedBall (0 : ℂ) 1, ∀ ε > 0, ∃ δ > 0, ∀ a b : S,
      dist (a : closedBall (0 : ℂ) 1) x < δ →
      dist (b : closedBall (0 : ℂ) 1) x < δ → dist (g a) (g b) < ε := by
    intro x ε hε
    by_cases hx : (x : ℂ) ∈ ball (0 : ℂ) 1
    · obtain ⟨δ, hδ, hh⟩ := Metric.continuousAt_iff.mp (hf.continuousAt (x := ⟨x, hx⟩))
        (ε / 2) (half_pos hε)
      refine ⟨δ, hδ, ?_⟩
      intro a b ha hb
      have ha' := hh (x := ⟨a.val.val, a.property⟩) ha
      have hb' := hh (x := ⟨b.val.val, b.property⟩) hb
      calc
        dist (g a) (g b) ≤ dist (g a) (f ⟨x, hx⟩) + dist (f ⟨x, hx⟩) (g b) := dist_triangle _ _ _
        _ < ε / 2 + ε / 2 := add_lt_add ha' (by simpa [dist_comm] using hb')
        _ = ε := add_halves ε
    · have hxS : (x : ℂ) ∈ sphere (0 : ℂ) 1 :=
        le_antisymm x.property (not_lt.mp hx)
      obtain ⟨r, hr, hd⟩ := hcaps x hxS
      have he : 0 < ENNReal.ofReal ε := ENNReal.ofReal_pos.mpr hε
      obtain ⟨n, hn⟩ := (hd.eventually (gt_mem_nhds he)).exists
      refine ⟨r n, hr n, ?_⟩
      intro a b ha hb
      have hab : edist (g a) (g b) < ENNReal.ofReal ε :=
        (edist_le_ediam_of_mem
          (show g a ∈ f '' {z : ball (0 : ℂ) 1 | dist (z : ℂ) x < r n} from
            ⟨⟨a.val.val, a.property⟩, ha, rfl⟩)
          (show g b ∈ f '' {z : ball (0 : ℂ) 1 | dist (z : ℂ) x < r n} from
            ⟨⟨b.val.val, b.property⟩, hb, rfl⟩)).trans_lt hn
      simpa only [edist_dist, ENNReal.ofReal_lt_ofReal_iff hε] using hab
  obtain ⟨F, hF, huniq⟩ :=
    HolomorphicAnosov.Topology.exists_unique_continuous_extension_of_local_oscillation S hS g hosc
  refine ⟨F, ⟨hF.1, ?_⟩, ?_⟩
  · intro a
    exact hF.2 ⟨⟨a, ball_subset_closedBall a.property⟩, a.property⟩
  · intro G hG
    apply huniq G
    refine ⟨hG.1, ?_⟩
    intro a
    exact hG.2 ⟨a.val.val, a.property⟩

end HolomorphicAnosov.Analysis

