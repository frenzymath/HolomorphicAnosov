import HolomorphicAnosov.Topology.ConwayDistanceCompactExhaustion
import HolomorphicAnosov.Topology.ConwayExhaustionNearComplement
import HolomorphicAnosov.Topology.OnePointClosedBallComplementConnected
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.PNat.Basic
import Mathlib.Topology.Compactification.OnePoint.Basic
import Mathlib.Topology.Connected.Basic

/-!
# Compact exhaustion of an open plane set

This file proves Conway’s compact exhaustion with control of complementary sphere components. (Conway, Prop. 1.2)
-/

open Set Metric
open scoped OnePoint

namespace HolomorphicAnosov

/-- Every open subset of the plane admits a compact exhaustion whose sphere-complementary components are contained in the corresponding complements. (Conway, Prop. 1.2) -/
theorem conway_open_plane_compact_exhaustion (U : Set ℂ) (hU : IsOpen U) :
    ∃ K : ℕ+ → Set ℂ,
      (∀ n, IsCompact (K n) ∧ K n ⊆ U) ∧
      (⋃ n, K n) = U ∧
      (∀ n, K n ⊆ interior (K (n + 1))) ∧
      (∀ C : Set ℂ, IsCompact C → C ⊆ U → ∃ n, C ⊆ K n) ∧
      ∀ n (x : OnePoint ℂ),
        x ∈ (OnePoint.some '' K n)ᶜ →
        ∃ y ∈ (OnePoint.some '' U)ᶜ,
          connectedComponentIn (OnePoint.some '' U)ᶜ y ⊆
            connectedComponentIn (OnePoint.some '' K n)ᶜ x := by
  classical
  by_cases hwhole : U = Set.univ
  · subst U
    refine ⟨fun n ↦ closedBall (0 : ℂ) (n : ℝ),
      fun n ↦ ⟨isCompact_closedBall _ _, subset_univ _⟩, ?_, ?_, ?_, ?_⟩
    · apply eq_univ_of_forall
      intro z
      obtain ⟨N, hN⟩ := exists_nat_gt ‖z‖
      refine mem_iUnion.mpr ⟨⟨N + 1, Nat.succ_pos _⟩, ?_⟩
      simp only [mem_closedBall, dist_zero_right]
      change ‖z‖ ≤ ((N + 1 : ℕ) : ℝ)
      exact hN.le.trans (by exact_mod_cast Nat.le_succ N)
    · intro n z hz
      apply ball_subset_interior_closedBall
      simp only [mem_closedBall, mem_ball, dist_zero_right] at hz ⊢
      exact hz.trans_lt (by exact_mod_cast Nat.lt_succ_self (n : ℕ))
    · intro C hC hCU
      obtain ⟨M, hM⟩ := hC.isBounded.exists_norm_le
      obtain ⟨N, hN⟩ := exists_nat_gt M
      refine ⟨⟨N + 1, Nat.succ_pos _⟩, ?_⟩
      intro z hz
      simp only [mem_closedBall, dist_zero_right]
      exact (hM z hz).trans (hN.le.trans (by exact_mod_cast Nat.le_succ N))
    · intro n x hx
      have hconn := onePoint_closedBall_complement_connected
        (R := (n : ℝ)) (by exact_mod_cast n.pos.le)
      refine ⟨(∞ : OnePoint ℂ), by simp, ?_⟩
      have hInf : (∞ : OnePoint ℂ) ∈
          connectedComponentIn (OnePoint.some '' closedBall (0 : ℂ) (n : ℝ))ᶜ x :=
        hconn.isPreconnected.subset_connectedComponentIn hx subset_rfl (by simp)
      rw [connectedComponentIn_eq hInf]
      exact connectedComponentIn_mono _
        (compl_subset_compl.mpr (image_mono (subset_univ _)))
  · have hUc : Uᶜ.Nonempty := Set.nonempty_compl.mpr hwhole
    let K : ℕ+ → Set ℂ := fun n ↦
      {z | ‖z‖ ≤ (n : ℝ) ∧ 1 / (n : ℝ) ≤ infDist z Uᶜ}
    obtain ⟨hK, hcover, hnest, hcofinal⟩ := conway_distance_compact_exhaustion U hU hUc
    refine ⟨K, hK, hcover, hnest, hcofinal, ?_⟩
    intro n x hx
    have hKball : K n ⊆ closedBall (0 : ℂ) (n : ℝ) := by
      intro z hz
      simpa only [mem_closedBall, dist_zero_right] using hz.1
    have houtside : (OnePoint.some '' closedBall (0 : ℂ) (n : ℝ))ᶜ ⊆
        (OnePoint.some '' K n)ᶜ := compl_subset_compl.mpr (image_mono hKball)
    by_cases hext : x ∈ (OnePoint.some '' closedBall (0 : ℂ) (n : ℝ))ᶜ
    · have hconn := onePoint_closedBall_complement_connected
        (R := (n : ℝ)) (by exact_mod_cast n.pos.le)
      have hInf : (∞ : OnePoint ℂ) ∈
          connectedComponentIn (OnePoint.some '' K n)ᶜ x :=
        hconn.isPreconnected.subset_connectedComponentIn hext houtside (by simp)
      refine ⟨∞, by simp, ?_⟩
      rw [connectedComponentIn_eq hInf]
      exact connectedComponentIn_mono _ (compl_subset_compl.mpr (image_mono (hK n).2))
    · have hxball : x ∈ OnePoint.some '' closedBall (0 : ℂ) (n : ℝ) := by simpa using hext
      obtain ⟨z, hzball, rfl⟩ := hxball
      have hzK : z ∉ K n := by simpa using hx
      have hnorm : ‖z‖ ≤ (n : ℝ) := by simpa only [mem_closedBall, dist_zero_right] using hzball
      have hdist : infDist z Uᶜ < 1 / (n : ℝ) :=
        lt_of_not_ge (fun h ↦ hzK ⟨hnorm, h⟩)
      obtain ⟨w, hw, hcomp⟩ := conway_exhaustion_near_complement (hK n).2 hUc
        (one_div_pos.mpr (by exact_mod_cast n.pos)) (fun _ h ↦ h.2) hdist
      exact ⟨OnePoint.some w, by simpa using hw, hcomp⟩

end HolomorphicAnosov
