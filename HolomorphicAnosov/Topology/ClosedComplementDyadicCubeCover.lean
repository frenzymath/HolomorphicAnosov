import HolomorphicAnosov.Topology.DyadicCoordinateBoxDiameter
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Archimedean.Basic

namespace HolomorphicAnosov
open Set Metric

theorem dyadic_cube_in_ball {N : ℕ} (x : EuclideanSpace ℝ (Fin N))
    (r : ℝ) (hr : 0 < r) :
    ∃ k : ℕ, ∃ m : Fin N → ℤ,
      (∀ j, (m j : ℝ) / (2 : ℝ)^k ≤ x j ∧ x j ≤ ((m j : ℝ)+1)/(2:ℝ)^k) ∧
      {y : EuclideanSpace ℝ (Fin N) | ∀ j,
        (m j : ℝ) / (2 : ℝ)^k ≤ y j ∧ y j ≤ ((m j : ℝ)+1)/(2:ℝ)^k} ⊆ ball x r := by
  have hden : 0 < Real.sqrt N + 1 := by positivity
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (div_pos hr hden)
    (by norm_num : (1/2 : ℝ) < 1)
  have hpow : 0 < (2 : ℝ)^k := by positivity
  have hsize : Real.sqrt N * (1 / (2 : ℝ)^k) < r := by
    have hk' : 1 / (2 : ℝ)^k < r / (Real.sqrt N + 1) := by simpa [div_pow] using hk
    have hh := (lt_div_iff₀ hden).mp hk'
    have hpos : 0 < 1 / (2 : ℝ)^k := by positivity
    nlinarith
  let m : Fin N → ℤ := fun j ↦ ⌊(2 : ℝ)^k * x j⌋
  have hx : ∀ j, (m j : ℝ) / (2 : ℝ)^k ≤ x j ∧
      x j ≤ ((m j : ℝ)+1)/(2:ℝ)^k := by
    intro j
    constructor
    · apply (div_le_iff₀ hpow).mpr
      simpa only [mul_comm] using Int.floor_le ((2:ℝ)^k * x j)
    · apply (le_div_iff₀ hpow).mpr
      simpa only [mul_comm] using (Int.lt_floor_add_one ((2:ℝ)^k * x j)).le
  refine ⟨k, m, hx, ?_⟩
  intro y hy
  apply lt_of_le_of_lt (euclidean_coordinate_box_diameter_le
    (1 / (2 : ℝ)^k) (by positivity) ?_) hsize
  intro j
  rw [Real.dist_eq, abs_le]
  have hinterval : ((m j : ℝ)+1)/(2:ℝ)^k - (m j : ℝ)/(2:ℝ)^k = 1/(2:ℝ)^k := by ring
  constructor <;> linarith [hx j, hy j]

/-- Closed dyadic cubes disjoint from a closed Euclidean set cover its complement;
one can choose a cube that is not contained in any earlier-level disjoint cube.

Source: Hatcher, *Algebraic Topology*, proof of Theorem A.7, pp.525–526.
For x outside the closed set, choose an open ball around x disjoint from the set.
At a sufficiently fine dyadic scale, round each scaled coordinate down to an
integer. The resulting cube contains x and has Euclidean diameter at most the
square root of the dimension times its side, so it lies in that ball. Choose
the least level with any such disjoint cube containing x. If this cube lay in
a disjoint earlier-level cube, that earlier cube would also contain x, contrary
to minimality. Empty removed sets and ambient dimension zero are allowed. -/
theorem closed_complement_dyadic_cube_cover {N : ℕ}
    (C : Set (EuclideanSpace ℝ (Fin N))) (hC : IsClosed C)
    (x : EuclideanSpace ℝ (Fin N)) (hx : x ∉ C) :
    let Q := fun (k : ℕ) (m : Fin N → ℤ) ↦
      {y : EuclideanSpace ℝ (Fin N) | ∀ j,
        (m j : ℝ)/(2:ℝ)^k ≤ y j ∧ y j ≤ ((m j : ℝ)+1)/(2:ℝ)^k}
    ∃ k : ℕ, ∃ m : Fin N → ℤ,
      x ∈ Q k m ∧ Disjoint (Q k m) C ∧
        ∀ l : ℕ, l < k → ∀ n : Fin N → ℤ,
          Q k m ⊆ Q l n → ¬ Disjoint (Q l n) C := by
  classical
  intro Q
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hC.isOpen_compl x hx
  obtain ⟨k, m, hxm, hsmall⟩ := dyadic_cube_in_ball x r hr
  have hex : ∃ k : ℕ, ∃ m : Fin N → ℤ, x ∈ Q k m ∧ Disjoint (Q k m) C := by
    refine ⟨k, m, hxm, disjoint_left.mpr ?_⟩
    intro y hyQ hyC
    exact hball (hsmall hyQ) hyC
  obtain ⟨m, hxm, hdisj⟩ := Nat.find_spec hex
  refine ⟨Nat.find hex, m, hxm, hdisj, ?_⟩
  intro l hl n hsub hd
  exact Nat.find_min hex hl ⟨n, hsub hxm, hd⟩

end HolomorphicAnosov
