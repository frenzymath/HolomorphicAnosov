import HolomorphicAnosov.Analysis.Complex.ComplexGridSquare
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Data.Int.Interval
import Mathlib.Algebra.Order.Floor.Ring

/-!
# A finite grid cover inside an open complex set

Source: Conway, Functions of One Complex Variable, second edition (1978),
VIII Proposition 1.1, pp.195–196, selection of all small closed grid rectangles
meeting the compact set. Uniform squares give the stated special case.
DAG node: `analysis.finite_complex_grid_cover_g19`.
-/

open Set
namespace HolomorphicAnosov.Analysis.Complex

/-- A sufficiently fine square grid has only finitely many closed cells meeting
K; those cells cover K and are all contained in U.

Source: Conway VIII.1.1, pp.195–196. Compact/open separation gives a positive
closed thickening of K inside U. Take the mesh to be half that radius. Compact
boundedness confines the integer indices of cells meeting K to a finite integer
rectangle. The cell with indices floor(Re z/δ), floor(Im z/δ) contains z, so the
selected cells cover K, including grid lines and vertices. Two points of a cell
have both coordinate differences at most δ, hence distance at most 2δ. A cell
meeting K therefore lies in the chosen closed thickening and in U.

The bound 2δ uses the triangle inequality instead of Conway's sharper √2δ;
choosing a correspondingly finer mesh preserves the argument. No connectedness
or boundedness of U is used. If K is empty, exactly the empty family is selected.
The selected cells themselves can meet K; only their surviving exterior edges
will avoid K in the later contour construction. -/
theorem exists_finite_complex_grid_cover
    (U K : Set ℂ) (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ (δ : ℝ) (S : Finset (ℤ × ℤ)), 0 < δ ∧
      (∀ q, q ∈ S ↔ ∃ z ∈ K, z ∈ complexGridSquare δ q) ∧
      (∀ z ∈ K, ∃ q ∈ S, z ∈ complexGridSquare δ q) ∧
      (∀ q ∈ S, complexGridSquare δ q ⊆ U) := by
  classical
  obtain ⟨ε, hε, hsub⟩ := hK.exists_cthickening_subset_open hU hKU
  let δ := ε / 2
  have hδ : 0 < δ := half_pos hε
  have hfin : {q : ℤ × ℤ | ∃ z ∈ K, z ∈ complexGridSquare δ q}.Finite := by
    obtain ⟨R, hR⟩ := hK.isBounded.exists_norm_le
    let M : ℤ := ⌊R / δ⌋ + 2
    have hbounds (r : ℝ) (i : ℤ) (hr : |r| ≤ R)
        (hl : δ * (i : ℝ) ≤ r) (hu : r ≤ δ * ((i : ℝ) + 1)) : -M ≤ i ∧ i ≤ M := by
      have hceil := Int.lt_floor_add_one (R / δ)
      have hp : (i : ℝ) ≤ R / δ := (le_div_iff₀ hδ).2 (by
        have := (abs_le.mp hr).2
        nlinarith)
      have hm : -(R / δ) - 1 ≤ (i : ℝ) := by
        have he : δ * (R / δ) = R := mul_div_cancel₀ R (ne_of_gt hδ)
        have := (abs_le.mp hr).1
        nlinarith
      have hlow : -(((⌊R / δ⌋ : ℤ) : ℝ) + 2) ≤ (i : ℝ) := by linarith
      have hupp : (i : ℝ) ≤ ((⌊R / δ⌋ : ℤ) : ℝ) + 2 := by linarith
      dsimp [M]
      constructor
      · exact_mod_cast hlow
      · exact_mod_cast hupp
    apply (Set.finite_Icc (-M, -M) (M, M)).subset
    intro q hq
    obtain ⟨z, hzK, hzq⟩ := hq
    obtain ⟨h1, h2, h3, h4⟩ := hzq
    have hx := hbounds z.re q.1 ((Complex.abs_re_le_norm z).trans (hR z hzK)) h1 h2
    have hy := hbounds z.im q.2 ((Complex.abs_im_le_norm z).trans (hR z hzK)) h3 h4
    exact ⟨⟨hx.1, hy.1⟩, ⟨hx.2, hy.2⟩⟩
  have hfloor (z : ℂ) : z ∈ complexGridSquare δ (⌊z.re / δ⌋, ⌊z.im / δ⌋) := by
    have hp (r : ℝ) : δ * (⌊r / δ⌋ : ℝ) ≤ r ∧ r ≤ δ * ((⌊r / δ⌋ : ℝ) + 1) := by
      have hl := Int.floor_le (r / δ)
      have hu := Int.lt_floor_add_one (r / δ)
      have he : δ * (r / δ) = r := mul_div_cancel₀ r (ne_of_gt hδ)
      constructor <;> nlinarith
    exact ⟨(hp z.re).1, (hp z.re).2, (hp z.im).1, (hp z.im).2⟩
  refine ⟨δ, hfin.toFinset, hδ, ?_, ?_, ?_⟩
  · intro q
    exact hfin.mem_toFinset
  · intro z hz
    refine ⟨(⌊z.re / δ⌋, ⌊z.im / δ⌋), ?_, hfloor z⟩
    exact hfin.mem_toFinset.mpr ⟨z, hz, hfloor z⟩
  · intro q hq z hz
    obtain ⟨w, hwK, hw⟩ := hfin.mem_toFinset.mp hq
    apply hsub
    apply Metric.mem_cthickening_of_dist_le z w ε K hwK
    have hd : dist z w ≤ 2 * δ := by
      obtain ⟨hz1, hz2, hz3, hz4⟩ := hz
      obtain ⟨hw1, hw2, hw3, hw4⟩ := hw
      have hre : |z.re - w.re| ≤ δ := by apply abs_le.mpr; constructor <;> linarith
      have him : |z.im - w.im| ≤ δ := by apply abs_le.mpr; constructor <;> linarith
      rw [dist_eq_norm]
      have h := Complex.norm_le_abs_re_add_abs_im (z - w)
      simp only [Complex.sub_re, Complex.sub_im] at h
      linarith
    dsimp [δ] at hd
    linarith

end HolomorphicAnosov.Analysis.Complex
