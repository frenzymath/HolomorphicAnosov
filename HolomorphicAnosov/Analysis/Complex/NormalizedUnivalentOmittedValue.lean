import HolomorphicAnosov.Analysis.Complex.HolomorphicEmbeddingInverse
import HolomorphicAnosov.Analysis.Complex.HolomorphicBijOnInverse
import HolomorphicAnosov.Analysis.Complex.WindingHolomorphicZeroCount
import HolomorphicAnosov.Analysis.Complex.NormalizedInverseLargerDisk
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.OpenMapping
import Mathlib.Topology.MetricSpace.Thickening

/-!
# An omitted unit-circle value for a normalized univalent map

Source: Mikhail Lyubich, *Conformal Geometry and Dynamics of Quadratic Polynomials*,
§4.4 Lemma 4.13, printed p.113; its rotation application in Theorem 4.12, pp.113–114.
DAG node: `analysis.lyubich_normalized_univalent_omitted_value_g1`.

The function is defined on the ambient complex plane only to use Mathlib's derivative API.
Holomorphy and injectivity are required solely on the open unit disk. The derivative at zero
is local to that disk, so the values assigned outside it impose no extra condition.
-/

open Set Metric

namespace HolomorphicAnosov

/-- A holomorphic injection of the open unit disk fixing zero, with derivative of modulus one
at zero, omits some point of the unit circle.

Source: Lyubich, *Conformal Geometry and Dynamics of Quadratic Polynomials*, §4.4 Lemma 4.13,
printed p.113, in `literature/lyubich-conformal-dynamics-acquired-20261007.pdf`; the supplied
text states that the image cannot contain the whole unit circle. The existential formulation
here is precisely that assertion. Only the derivative modulus, not its argument, is fixed.

Natural-language proof: by holomorphy and injectivity, the restriction to the unit disk D is
nonconstant and open, and is a homeomorphism onto its open image V. Its inverse g is
holomorphic. Suppose that V contains the unit circle. If b with |b| < 1 were outside V, pull
that circle back through g, contract it to zero by straight segments in D, and compose the
contraction with f. The resulting homotopy contracts the unit circle to the constant zero
loop while avoiding b. Winding is invariant under this homotopy, but the unit circle has
winding one about b and the constant loop has winding zero. (The point b is nonzero since
f(0) = 0.) Thus the entire closed unit disk lies in V. This winding argument expands the
image-filling step suppressed in Lyubich's printed proof.

Compactness of the closed unit disk inside the open V gives a positive collar, hence a
radius R > 1 with ball(0,R) contained in V. Extend g arbitrarily outside V; it remains
holomorphic on this larger disk and maps it into D. The identity g(f(z)) = z on D and the
chain rule give |g'(0)| = 1. The Schwarz derivative estimate on the radius-R disk instead
gives |g'(0)| ≤ 1/R < 1, a contradiction. This last step is the exact existing theorem
`normalized_inverse_larger_disk_contradiction`. Consequently some unit-circle value a is
outside V, which means f(z) ≠ a for every z in D. No boundary continuity or extension of f
beyond D is used, and rotations of the identity satisfy the hypotheses and conclusion.
-/
theorem normalized_univalent_omits_unit_value
    (f : ℂ → ℂ)
    (hf : DifferentiableOn ℂ f (ball 0 1))
    (hinj : InjOn f (ball 0 1))
    (hf0 : f 0 = 0) (hderiv : ‖deriv f 0‖ = 1) :
    ∃ a : ℂ, ‖a‖ = 1 ∧ ∀ z ∈ ball (0 : ℂ) 1, f z ≠ a := by
  by_contra hno
  push Not at hno
  let D : Set ℂ := ball 0 1
  let V : Set ℂ := f '' D
  have hbij : BijOn f D V := by
    refine ⟨?_, hinj, ?_⟩
    · intro z hz
      exact ⟨z, hz, rfl⟩
    · intro w hw
      rcases hw with ⟨z, hz, rfl⟩
      exact ⟨z, hz, rfl⟩
  obtain ⟨g, hg, hgmaps, hleft, hright⟩ := holomorphic_bijOn_inverse isOpen_ball hf hbij
  have hcircle : ∀ a : ℂ, ‖a‖ = 1 → a ∈ V := by
    intro a ha
    rcases hno a ha with ⟨z, hz, hzf⟩
    exact ⟨z, hz, hzf⟩
  have hclosed : closedBall (0 : ℂ) 1 ⊆ V := by
    intro b hb
    rcases lt_or_eq_of_le (mem_closedBall_zero_iff.mp hb) with hb' | hb'
    · by_contra hbin
      have hgb : ∀ z : Circle, g (z : ℂ) ∈ D := by
        intro z
        exact hgmaps (hcircle (z : ℂ) (by simp))
      let γ₀ : ComplexLoop := unitCircleLoop
      let γ₁ : ComplexLoop := constantLoop 0
      have hγ₀ : ∀ z, γ₀ z ≠ b := by
        intro z hz
        have hz' := congrArg norm hz
        have := Circle.norm_coe z
        rw [show γ₀ z = (z : ℂ) by rfl] at hz'
        linarith
      have hb0 : b ≠ 0 := by
        intro hb0
        apply hbin
        have hz : (0 : ℂ) ∈ V := ⟨0, mem_ball_self zero_lt_one, hf0⟩
        simpa [hb0] using hz
      have hγ₁ : ∀ z, γ₁ z ≠ b := by
        intro z
        change (0 : ℂ) ≠ b
        exact hb0.symm
      have hgc : Continuous (fun z : Circle ↦ g (z : ℂ)) := by
        apply hg.continuousOn.comp_continuous continuous_subtype_val
        intro z
        exact hcircle (z : ℂ) (by simpa using Circle.norm_coe z)
      have harg : ∀ p : (unitInterval × Circle),
          ((1 - (p.1.val : ℝ) : ℝ) : ℂ) * g (p.2 : ℂ) ∈ D := by
        intro p
        rw [mem_ball_zero_iff]
        simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (sub_nonneg.mpr p.1.property.2)]
        have hz' := mem_ball_zero_iff.mp (hgb p.2)
        have ht1 : 1 - (p.1 : ℝ) ≤ 1 := by linarith [p.1.property.1]
        calc
          (1 - (p.1 : ℝ)) * ‖g (p.2 : ℂ)‖ ≤ 1 * ‖g (p.2 : ℂ)‖ :=
            mul_le_mul_of_nonneg_right ht1 (norm_nonneg _)
          _ = ‖g (p.2 : ℂ)‖ := one_mul _
          _ < 1 := hz'
      have hcontarg : Continuous (fun p : (unitInterval × Circle) ↦
          ((1 - (p.1.val : ℝ) : ℝ) : ℂ) * g (p.2 : ℂ)) := by
        have htR : Continuous (fun p : (unitInterval × Circle) ↦
            (1 : ℝ) - (p.1.val : ℝ)) :=
          continuous_const.sub (continuous_subtype_val.comp continuous_fst)
        have ht : Continuous (fun p : (unitInterval × Circle) ↦
            ((1 - (p.1.val : ℝ) : ℝ) : ℂ)) := Complex.continuous_ofReal.comp htR
        convert ht.mul (hgc.comp continuous_snd) using 1; ext p; rfl
      have hFcomp : Continuous (fun p : (unitInterval × Circle) ↦
          f (((1 - (p.1.val : ℝ) : ℝ) : ℂ) * g (p.2 : ℂ))) :=
        hf.continuousOn.comp_continuous hcontarg harg
      let H : C(↑unitInterval × Circle, ℂ) :=
        ⟨fun p ↦ f (((1 - (p.1.val : ℝ) : ℝ) : ℂ) * g (p.2 : ℂ)), hFcomp⟩
      have hhom : LoopHomotopyAvoids γ₀ γ₁ b := by
        refine ⟨H, ?_, ?_, ?_⟩
        · intro z
          change f (((1 - (0 : ℝ) : ℝ) : ℂ) * g (z : ℂ)) = (z : ℂ)
          simpa using hright (z : ℂ)
            (hcircle (z : ℂ) (by simp))
        · intro z
          change f (((1 - (1 : ℝ) : ℝ) : ℂ) * g (z : ℂ)) = 0
          simp [hf0]
        · intro t z heq
          apply hbin
          exact ⟨((1 - (t.val : ℝ) : ℝ) : ℂ) * g (z : ℂ), harg (t, z), heq⟩
      have hw := winding_holomorphic_zero_count.1 γ₀ γ₁ b hγ₀ hγ₁ hhom
      have hu := winding_holomorphic_zero_count.2.2.1 b hγ₀ hb'
      have hc := winding_holomorphic_zero_count.2.2.2.1 0 b hb0.symm
      have hEq : (1 : ℤ) = 0 := by
        calc
          (1 : ℤ) = loopWinding γ₀ b hγ₀ := hu.symm
          _ = loopWinding γ₁ b hγ₁ := hw
          _ = 0 := hc
      exact one_ne_zero hEq
    · have hb1 : ‖b‖ = 1 := by simp [hb']
      exact hcircle b hb1
  have hVopen : IsOpen V := lebl_scalar_open_image isOpen_ball hf hinj isOpen_ball Subset.rfl
  obtain ⟨δ, hδ, hct⟩ :=
    (isCompact_closedBall (0 : ℂ) 1).exists_cthickening_subset_open hVopen
      (by intro z hz; exact hclosed hz)
  let R : ℝ := 1 + δ / 2
  have hR : 1 < R := by dsimp [R]; linarith
  have hball : ball (0 : ℂ) R ⊆ V := by
    intro z hz
    have hzR : ‖z‖ < R := mem_ball_zero_iff.mp hz
    by_cases hle : ‖z‖ ≤ 1
    · apply hct
      apply Metric.self_subset_cthickening
      exact mem_closedBall_zero_iff.mpr hle
    · have hz1 : 1 < ‖z‖ := lt_of_not_ge hle
      have hz0 : ‖z‖ ≠ 0 := by linarith
      let y : ℂ := z / (‖z‖ : ℂ)
      have hy : y ∈ closedBall (0 : ℂ) 1 := by
        rw [mem_closedBall_zero_iff]
        dsimp [y]
        rw [norm_div, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (norm_nonneg z)]
        field_simp
        norm_num
      have hdist : dist z y = ‖z‖ - 1 := by
        dsimp [y]
        have hr : (‖z‖ : ℂ) ≠ 0 := by exact_mod_cast hz0
        rw [dist_eq_norm]
        have hzsub : z - z / (‖z‖ : ℂ) =
            ((‖z‖ - 1 : ℝ) : ℂ) / (‖z‖ : ℂ) * z := by
          field_simp
          push_cast
          ring
        rw [hzsub, norm_mul, norm_div, Complex.norm_real,
          Real.norm_of_nonneg (by linarith)]
        rw [Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (norm_nonneg z)]
        ring_nf
        field_simp [hz0]
      apply hct
      apply Metric.thickening_subset_cthickening δ (closedBall (0 : ℂ) 1)
      rw [Metric.mem_thickening_iff]
      refine ⟨y, hy, ?_⟩
      have hzR' : ‖z‖ < 1 + δ / 2 := by simpa [R] using hzR
      linarith [hdist, hzR', hδ]
  have hgR : DifferentiableOn ℂ g (ball 0 R) := hg.mono hball
  have hmapR : MapsTo g (ball 0 R) (ball 0 1) := hgmaps.comp hball
  exact normalized_inverse_larger_disk_contradiction f g R hR hf hgR hf0 hderiv hleft hmapR

end HolomorphicAnosov

