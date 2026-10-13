import HolomorphicAnosov.Topology.GoodPairCollapse
import HolomorphicAnosov.Topology.GoodPairReducedHomologyExactSequence
import HolomorphicAnosov.Topology.Homology.IntegralReducedSingularHomology
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.Convex.Contractible
import HolomorphicAnosov.Topology.Homology.ReducedSphereHomology.AppendEuclidean_norm_sq
import HolomorphicAnosov.Topology.Homology.ReducedSphereHomology.PolarDiskMap
import HolomorphicAnosov.Topology.Homology.ReducedSphereHomology.AppendEuclidean

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace HolomorphicAnosov.Topology.Homology

/-- The printed radial quotient formula reaches every unit-sphere point.
Positive disk dimension supplies the boundary representative of the south pole. -/
theorem polarDiskMap_surjective (k : ℕ)
    (y : EuclideanSpace ℝ (Fin (k + 1 + 1))) (hy : ‖y‖ = 1) :
    ∃ x : EuclideanSpace ℝ (Fin (k + 1)), ‖x‖ ≤ 1 ∧ polarDiskMap (k + 1) x = y := by
  let v : EuclideanSpace ℝ (Fin (k + 1)) := WithLp.toLp 2 (fun i ↦ y i.castSucc)
  let t : ℝ := y (Fin.last (k + 1))
  have hsplit : appendEuclidean (k + 1) v t = y := by
    ext i
    refine Fin.lastCases ?_ (fun j ↦ ?_) i <;> simp [appendEuclidean, v, t]
  have heq : ‖v‖ ^ 2 + t ^ 2 = 1 := by
    rw [← appendEuclidean_norm_sq, hsplit, hy]
    norm_num
  have ht : t ∈ Set.Icc (-1 : ℝ) 1 := by
    have h := PiLp.norm_apply_le y (Fin.last (k + 1))
    simpa [t, hy, Real.norm_eq_abs, abs_le] using h
  obtain ⟨θ, hθ, hc⟩ := Real.surjOn_cos ht
  have hs := Real.sin_sq_add_cos_sq θ
  rw [hc] at hs
  by_cases h0 : θ = 0
  · have htone : t = 1 := by simpa [h0] using hc.symm
    have hv : v = 0 := by apply norm_eq_zero.mp; nlinarith [norm_nonneg v]
    refine ⟨0, by simp, ?_⟩
    rw [← hsplit, hv, htone]
    simp [polarDiskMap, appendEuclidean]
  by_cases hp : θ = Real.pi
  · have htneg : t = -1 := by simpa [hp] using hc.symm
    have hv : v = 0 := by apply norm_eq_zero.mp; nlinarith [norm_nonneg v]
    let x : EuclideanSpace ℝ (Fin (k + 1)) := PiLp.single 2 0 1
    have hx : ‖x‖ = 1 := by simp [x]
    refine ⟨x, hx.le, ?_⟩
    rw [← hsplit, hv, htneg]
    simp [polarDiskMap, hx, appendEuclidean, Real.sinc_of_ne_zero Real.pi_ne_zero]
  have hθpos : 0 < θ := lt_of_le_of_ne hθ.1 (Ne.symm h0)
  have hθlt : θ < Real.pi := lt_of_le_of_ne hθ.2 hp
  have hsin : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθpos hθlt
  have hv : ‖v‖ = Real.sin θ := by nlinarith [norm_nonneg v]
  let r : ℝ := θ / Real.pi
  have hr : 0 < r := div_pos hθpos Real.pi_pos
  have hrle : r ≤ 1 := (div_le_one Real.pi_pos).mpr hθ.2
  let x : EuclideanSpace ℝ (Fin (k + 1)) := (r / Real.sin θ) • v
  have hx : ‖x‖ = r := by
    change ‖(r / Real.sin θ) • v‖ = r
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos hr hsin), hv]
    field_simp
  have hangle : Real.pi * r = θ := by dsimp [r]; field_simp
  have hfactor : (Real.pi * Real.sinc θ) * (r / Real.sin θ) = 1 := by
    rw [Real.sinc_of_ne_zero h0]
    dsimp [r]
    field_simp
  refine ⟨x, hx.trans_le hrle, ?_⟩
  rw [polarDiskMap, hx, hangle, hc, ← hsplit]
  congr 1
  change (Real.pi * Real.sinc θ) • ((r / Real.sin θ) • v) = v
  rw [smul_smul, hfactor, one_smul]

end HolomorphicAnosov.Topology.Homology
