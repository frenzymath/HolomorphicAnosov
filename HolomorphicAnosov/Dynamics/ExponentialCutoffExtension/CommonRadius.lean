import Mathlib.Basic.Real.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

noncomputable section
namespace HolomorphicAnosov.ExponentialCutoff

/-- A finite family of positive coordinate radii and comparison constants admits
one positive metric radius below any prescribed positive R. Source: the finite
minimum step in HPS (1977), proof of Theorem 5.5, p. 62. Take half the minimum
of R and the finite positive ratios dᵢ/cᵢ. Every scaled radius cᵢδ is at most dᵢ.
The finite index set is explicitly nonempty before its minimum is taken. -/
theorem finite_common_radius
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (hs : s.Nonempty)
    (d c : ι → ℝ)
    (hd : ∀ i ∈ s, 0 < d i)
    (hc : ∀ i ∈ s, 0 < c i)
    {R : ℝ} (hR : 0 < R) :
    ∃ δ : ℝ, 0 < δ ∧ δ < R ∧ ∀ i ∈ s, c i * δ ≤ d i := by
  classical
  let ratios : Finset ℝ := s.image (fun i ↦ d i / c i)
  have hratios : ratios.Nonempty := Finset.image_nonempty.mpr hs
  let rmin : ℝ := ratios.min' hratios
  have hrmin_pos : 0 < rmin := by
    have hrmem : rmin ∈ ratios := Finset.min'_mem ratios hratios
    obtain ⟨i, hi, hri⟩ := Finset.mem_image.mp hrmem
    rw [← hri]
    exact div_pos (hd i hi) (hc i hi)
  let δ : ℝ := min R rmin / 2
  have hδ_pos : 0 < δ := by
    dsimp [δ]
    positivity
  have hδ_R : δ < R := by
    have hminR : min R rmin ≤ R := min_le_left _ _
    dsimp [δ]
    nlinarith
  refine ⟨δ, hδ_pos, hδ_R, ?_⟩
  intro i hi
  have hrat : rmin ≤ d i / c i := by
    exact Finset.min'_le ratios (d i / c i)
      (Finset.mem_image.mpr ⟨i, hi, rfl⟩)
  have hδrat : δ ≤ d i / c i := by
    have hmin : min R rmin ≤ rmin := min_le_right _ _
    dsimp [δ]
    nlinarith
  calc
    c i * δ ≤ c i * (d i / c i) :=
      mul_le_mul_of_nonneg_left hδrat (le_of_lt (hc i hi))
    _ = d i := by field_simp [ne_of_gt (hc i hi)]

end HolomorphicAnosov.ExponentialCutoff
