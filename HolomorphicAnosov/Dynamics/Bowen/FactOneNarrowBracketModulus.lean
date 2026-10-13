import HolomorphicAnosov.Dynamics.ProperRelativeMarkovPartitionG7
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Tactic

noncomputable section

namespace HolomorphicAnosov.BowenBasicSetCoding

open Set Filter
open scoped Topology _root_.Topology

variable {X : Type*} [MetricSpace X] [CompactSpace X]

/-- Compact-domain continuity and pair contraction give arbitrarily narrow
closed orbit intersections. Compare (x,y) with each of (x,x) and (y,y), then
use the contraction estimate with the diagonal point in the same full plaque.
Source: Bowen (1970), Lemma 5 and the scale choice preceding Lemma 6. -/
theorem factOne_narrow_bracket_modulus
    (F : X ≃ₜ X) (γ lam ε : ℝ) (hγ : 0 < γ) (hlam : 0 ≤ lam)
    (hlam1 : lam ≤ 1) (hε : 0 < ε) (b : X → X → X)
    (hmem : ∀ x y, dist x y ≤ ε →
      b x y ∈ Dynamics.relativeClosedStablePlaque F γ x ∩
        Dynamics.relativeClosedUnstablePlaque F γ y)
    (huniq : ∀ x y z, dist x y ≤ ε →
      z ∈ Dynamics.relativeClosedStablePlaque F γ x ∩
        Dynamics.relativeClosedUnstablePlaque F γ y → z = b x y)
    (hcont : ContinuousOn (fun p : X × X ↦ b p.1 p.2) {p | dist p.1 p.2 ≤ ε})
    (hs : ∀ x y z, y ∈ Dynamics.relativeClosedStablePlaque F γ x →
      z ∈ Dynamics.relativeClosedStablePlaque F γ x → ∀ n : ℕ,
      dist ((F : X → X)^[n] y) ((F : X → X)^[n] z) ≤ lam ^ n * dist y z)
    (hu : ∀ x y z, y ∈ Dynamics.relativeClosedUnstablePlaque F γ x →
      z ∈ Dynamics.relativeClosedUnstablePlaque F γ x → ∀ n : ℕ,
      dist ((F.symm : X → X)^[n] y) ((F.symm : X → X)^[n] z) ≤ lam ^ n * dist y z)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ η : ℝ, 0 < η ∧ η ≤ ε ∧ ∀ x y, dist x y ≤ η →
      b x y ∈ Dynamics.relativeClosedStablePlaque F δ x ∩
        Dynamics.relativeClosedUnstablePlaque F δ y := by
  have hselfs : ∀ x, x ∈ Dynamics.relativeClosedStablePlaque F γ x :=
    fun _ _ ↦ by simpa using hγ.le
  have hselfu : ∀ x, x ∈ Dynamics.relativeClosedUnstablePlaque F γ x :=
    fun _ _ ↦ by simpa using hγ.le
  have hdiag : ∀ x, b x x = x := fun x ↦
    (huniq x x x (by simpa using hε.le) ⟨hselfs x, hselfu x⟩).symm
  have hc : IsCompact {p : X × X | dist p.1 p.2 ≤ ε} :=
    (isClosed_le continuous_dist continuous_const).isCompact
  obtain ⟨η, hη, hclose⟩ := Metric.uniformContinuousOn_iff.mp
    (hc.uniformContinuousOn_of_continuous hcont) δ hδ
  refine ⟨min ε (η / 2), lt_min hε (half_pos hη), min_le_left _ _, ?_⟩
  intro x y hxy
  have hxyε := hxy.trans (min_le_left _ _)
  have hxyη : dist x y < η := (hxy.trans (min_le_right _ _)).trans_lt (by linarith)
  have hx : dist (b x y) x < δ := by
    have h := hclose (x, y) hxyε (x, x) (by simpa using hε.le)
      (by simpa [Prod.dist_eq, dist_comm] using hxyη)
    simpa only [hdiag] using h
  have hy : dist (b x y) y < δ := by
    have h := hclose (x, y) hxyε (y, y) (by simpa using hε.le)
      (by simpa [Prod.dist_eq] using hxyη)
    simpa only [hdiag] using h
  refine ⟨fun n ↦ ?_, fun n ↦ ?_⟩
  · exact (hs x (b x y) x (hmem x y hxyε).1 (hselfs x) n).trans
      (((mul_le_mul_of_nonneg_right (pow_le_one₀ hlam hlam1) dist_nonneg).trans
        (by simpa using hx.le)))
  · exact (hu y (b x y) y (hmem x y hxyε).2 (hselfu y) n).trans
      (((mul_le_mul_of_nonneg_right (pow_le_one₀ hlam hlam1) dist_nonneg).trans
        (by simpa using hy.le)))


end HolomorphicAnosov.BowenBasicSetCoding
