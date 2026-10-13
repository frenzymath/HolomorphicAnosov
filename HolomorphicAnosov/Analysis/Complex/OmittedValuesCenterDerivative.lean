import HolomorphicAnosov.Analysis.Complex.ConwayMontelCaratheodoryOmittedValues
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push

/-!
# Uniform spherical derivative at the center of the disk

Source: Ahlfors, *Complex Analysis*, third edition (1979), Chapter 5 §5.5,
Theorem 17, pp.226–227 (the necessity proof of Marty's criterion), applied
at the compact singleton `{0}`; Conway II XVI §4 Theorem 4.2, pp.124–125,
supplies the independent normal-family subsequence.
-/

namespace HolomorphicAnosov

open Filter Metric Set
open scoped _root_.Topology

/-- The spherical derivatives at the center of the unit disk of all holomorphic functions
omitting zero and one have one finite positive bound.

Source: Ahlfors, *Complex Analysis*, third edition, Chapter 5 §5.5,
Theorem 17, pp.226–227, necessity proof; Conway, *Functions of One Complex
Variable II*, Chapter XVI §4 Theorem 4.2, pp.124–125. Ahlfors takes a sequence
whose spherical derivatives are unbounded, extracts a convergent subsequence,
and uses a finite analytic chart or its reciprocal to obtain derivative bounds
on a smaller disk. Here the compact set is just the center. The finite branch
uses the Cauchy bound underlying the cited Weierstrass derivative-convergence
argument; the infinite branch applies that bound to the reciprocal. Ahlfors's
spherical derivative has an extra factor two, which does not affect boundedness.
This also proves the center case of Lyubich §4.3 Exercise 4.6, p.112.

If no bound exists, choose functions whose spherical center derivatives exceed n.
Montel gives a subsequence converging uniformly on compact subsets to a holomorphic
function, or uniformly diverging to infinity. In the finite case, compactness bounds
the limit on the closed half disk, and uniform convergence bounds a tail by this
bound plus one. Cauchy's estimate on the half disk bounds the center derivatives,
contradicting their growth. In the infinite case the reciprocals are holomorphic
and bounded by one on that half disk in a tail. Their derivatives at zero are
bounded by two. The reciprocal has exactly the same spherical derivative, again
contradicting growth. Strict increase of the extracted indices implies φ(n) ≥ n.
-/
theorem omittedValues_center_sphericalDerivative_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ h : ℂ → ℂ,
      DifferentiableOn ℂ h (ball 0 1) →
      (∀ z ∈ ball (0 : ℂ) 1, h z ≠ 0 ∧ h z ≠ 1) →
      ‖deriv h 0‖ / (1 + ‖h 0‖ ^ 2) ≤ C := by
  classical
  by_contra hn
  push Not at hn
  have hex : ∀ n : ℕ, ∃ h : ℂ → ℂ,
      DifferentiableOn ℂ h (ball 0 1) ∧
      (∀ z ∈ ball (0 : ℂ) 1, h z ≠ 0 ∧ h z ≠ 1) ∧
      (n : ℝ) + 1 < ‖deriv h 0‖ / (1 + ‖h 0‖ ^ 2) := by
    intro n
    obtain ⟨h, hd, ho, hb⟩ := hn (n + 1) (by positivity)
    exact ⟨h, hd, ho, hb⟩
  choose f hf ho hb using hex
  have hsub : closedBall (0 : ℂ) (1 / 2) ⊆ ball 0 1 :=
    closedBall_subset_ball (by norm_num)
  have hzero : (0 : ℂ) ∈ ball (0 : ℂ) 1 := mem_ball_self (by norm_num)
  obtain ⟨φ, hφ, hlim | hinfty⟩ :=
    conway_montel_caratheodory_omitted_values_g2 isOpen_ball
      (convex_ball (0 : ℂ) 1).isPreconnected f hf ho
  · obtain ⟨h, hh, hlim⟩ := hlim
    obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : ℂ) (1 / 2)).exists_bound_of_continuousOn
      (hh.continuousOn.mono hsub)
    have hu := (Metric.tendstoUniformlyOn_iff.mp
      (hlim _ (isCompact_closedBall _ _) hsub)) 1 (by norm_num)
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hu
    obtain ⟨n, hn⟩ := exists_nat_gt (2 * (M + 1))
    let k := max n N
    have hbound : ‖deriv (f (φ k)) 0‖ ≤ (M + 1) / (1 / 2) := by
      apply Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (by norm_num)
        ((hf _).diffContOnCl_ball hsub)
      intro z hz
      have hz' := sphere_subset_closedBall hz
      have hd := hN k (le_max_right _ _) z hz'
      rw [dist_comm] at hd
      calc
        ‖f (φ k) z‖ ≤ dist (f (φ k) z) (h z) + ‖h z‖ := by
          simpa only [dist_zero_right] using dist_triangle (f (φ k) z) (h z) 0
        _ ≤ M + 1 := by linarith [hM z hz']
    have hden : 1 ≤ 1 + ‖f (φ k) 0‖ ^ 2 := by nlinarith [sq_nonneg ‖f (φ k) 0‖]
    have hfrac := div_le_self (norm_nonneg (deriv (f (φ k)) 0)) hden
    have hind : (n : ℝ) ≤ φ k := by
      exact_mod_cast (le_max_left n N).trans (hφ.id_le k)
    have hbad := hb (φ k)
    norm_num at hbound
    linarith
  · obtain ⟨N, hN⟩ := hinfty _ (isCompact_closedBall (0 : ℂ) (1 / 2)) hsub 1
      (by norm_num)
    let k := max 3 N
    let g : ℂ → ℂ := fun z ↦ (f (φ k) z)⁻¹
    have hg : DifferentiableOn ℂ g (ball 0 1) :=
      (hf _).inv (fun z hz ↦ (ho _ z hz).1)
    have hbound : ‖deriv g 0‖ ≤ 2 := by
      have h := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le
        (f := g) (R := 1 / 2) (C := 1) (by norm_num)
        (hg.diffContOnCl_ball hsub) (fun z hz ↦ ?_)
      · norm_num at h
        exact h
      · dsimp [g]
        rw [norm_inv]
        exact (inv_le_one₀ (norm_pos_iff.mpr (ho _ z (hsub
          (sphere_subset_closedBall hz))).1)).mpr
          (le_of_lt (hN k (le_max_right _ _) z (sphere_subset_closedBall hz)))
    have hder : deriv g 0 = -(deriv (f (φ k)) 0) / f (φ k) 0 ^ 2 := by
      exact ((hf _).differentiableAt (isOpen_ball.mem_nhds hzero)).hasDerivAt.inv
        (ho _ 0 hzero).1 |>.deriv
    have hnorm : 0 < ‖f (φ k) 0‖ := norm_pos_iff.mpr (ho _ 0 hzero).1
    have hfrac : ‖deriv (f (φ k)) 0‖ / (1 + ‖f (φ k) 0‖ ^ 2) ≤ ‖deriv g 0‖ := by
      rw [hder, norm_div, norm_neg, norm_pow]
      apply div_le_div_of_nonneg_left (norm_nonneg _) (sq_pos_of_pos hnorm)
      linarith
    have hind : (3 : ℝ) ≤ φ k := by
      exact_mod_cast (le_max_left 3 N).trans (hφ.id_le k)
    have hbad := hb (φ k)
    linarith


end HolomorphicAnosov
