import Mathlib.Topology.CWComplex.Classical.Basic
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.UnitInterval

namespace HolomorphicAnosov

/-- Characteristic homotopies fixed on a set containing all cell frontiers
respect every characteristic identification. Source: Hatcher Theorem 4.8,
p.349, simultaneous deformation of source cells. If a common characteristic
image is in the fixed set, both values equal the initial map there. Otherwise
neither disk representative is on its sphere, so both are interior. Disjointness
of open cells identifies their cell indices, and injectivity of that cell's
characteristic map on its open ball identifies the disk representatives. -/
theorem cw_boundary_fixed_characteristic_compatibility
    {X : Type*} {Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (C : Set X) [Topology.CWComplex C] (F : Set X) (q : X → Y)
    (hfront : ∀ m (i : Topology.RelCWComplex.cell C m),
      Topology.CWComplex.cellFrontier m i ⊆ F)
    (P : ∀ m (_ : Topology.RelCWComplex.cell C m),
      C(unitInterval × Metric.closedBall (0 : Fin m → ℝ) 1, Y))
    (hfix : ∀ m i t z, Topology.RelCWComplex.map m i z.val ∈ F →
      P m i (t, z) = q (Topology.RelCWComplex.map m i z.val)) :
    ∀ m i l j t (z : Metric.closedBall (0 : Fin m → ℝ) 1)
      (w : Metric.closedBall (0 : Fin l → ℝ) 1),
      Topology.RelCWComplex.map m i z.val = Topology.RelCWComplex.map l j w.val →
      P m i (t, z) = P l j (t, w) := by
  intro m i l j t z w heq
  by_cases hx : Topology.RelCWComplex.map m i z.val ∈ F
  · rw [hfix m i t z hx, hfix l j t w (heq ▸ hx), heq]
  have hz : z.val ∈ Metric.ball (0 : Fin m → ℝ) 1 := by
    have hzle := z.property
    rw [Metric.mem_closedBall, dist_zero_right] at hzle
    have hzne : ‖z.val‖ ≠ 1 := by
      intro h
      exact hx (hfront m i ⟨z.val, by simpa [Metric.mem_sphere, dist_zero_right] using h, rfl⟩)
    simpa only [Metric.mem_ball, dist_zero_right] using lt_of_le_of_ne hzle hzne
  have hw : w.val ∈ Metric.ball (0 : Fin l → ℝ) 1 := by
    have hwle := w.property
    rw [Metric.mem_closedBall, dist_zero_right] at hwle
    have hwne : ‖w.val‖ ≠ 1 := by
      intro h
      exact hx (heq ▸ hfront l j ⟨w.val, by simpa [Metric.mem_sphere, dist_zero_right] using h, rfl⟩)
    simpa only [Metric.mem_ball, dist_zero_right] using lt_of_le_of_ne hwle hwne
  have hij : (⟨m, i⟩ : Σ d, Topology.RelCWComplex.cell C d) = ⟨l, j⟩ :=
    Topology.RelCWComplex.eq_of_not_disjoint_openCell
      (Set.not_disjoint_iff.mpr ⟨Topology.RelCWComplex.map m i z.val,
        ⟨z.val, hz, rfl⟩, ⟨w.val, hw, heq.symm⟩⟩)
  have hml : m = l := congrArg Sigma.fst hij
  subst l
  have hij' : i = j := eq_of_heq (Sigma.mk.inj_iff.mp hij).2
  subst j
  have hzw : z = w := Subtype.ext ((Topology.RelCWComplex.map m i).injOn
    (by rwa [Topology.RelCWComplex.source_eq])
    (by rwa [Topology.RelCWComplex.source_eq]) heq)
  rw [hzw]

end HolomorphicAnosov
