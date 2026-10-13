import HolomorphicAnosov.Analysis.HolomorphicSliceTwoDerivativesContinuous
import HolomorphicAnosov.Ghys.AffineSchwarzianQuadraticForm
import HolomorphicAnosov.Analysis.Complex.SchwarzianChainRule

/-! # Joint continuity of the Schwarzian of holomorphic slices

Demailly, Complex Analytic and Differential Geometry, Chapter I §3.B,
pp.22–23 (continuity of holomorphic derivatives); Ghys §4 p.594.
-/
noncomputable section
open Set
namespace HolomorphicAnosov

/-- The Schwarzian of a jointly continuous family of holomorphic local
immersions is jointly continuous on its original open domain. Differentiate
slices three times using compact-uniform holomorphic derivative convergence.
The defining rational expression is continuous because the first derivative
never vanishes. No derivative in the parameter is taken. -/
theorem holomorphic_slice_schwarzian_continuousOn
    {T : Type*} [TopologicalSpace T] (Ω : Set (ℂ × T)) (hΩ : IsOpen Ω)
    (H : ℂ × T → ℂ) (hH : ContinuousOn H Ω)
    (hd : ∀ t, DifferentiableOn ℂ (fun z ↦ H (z, t)) {z | (z, t) ∈ Ω})
    (hnz : ∀ p ∈ Ω, deriv (fun z ↦ H (z, p.2)) p.1 ≠ 0) :
    ContinuousOn (fun p : ℂ × T ↦ Ghys.schwarzian (fun z ↦ H (z, p.2)) p.1) Ω := by
  have hopen (t : T) : IsOpen {z | (z, t) ∈ Ω} :=
    hΩ.preimage (continuous_id.prodMk continuous_const)
  have h1 := SliceDerivativePreparation.joint_deriv_continuousOn_open Ω hΩ H hH hd
  have hd1 (t : T) := (hd t).deriv (hopen t)
  have h2 := SliceDerivativePreparation.joint_deriv_continuousOn_open Ω hΩ
    (fun p : ℂ × T ↦ deriv (fun z ↦ H (z, p.2)) p.1) h1 hd1
  have hd2 (t : T) := (hd1 t).deriv (hopen t)
  have h3 := SliceDerivativePreparation.joint_deriv_continuousOn_open Ω hΩ
    (fun p : ℂ × T ↦ deriv (deriv (fun z ↦ H (z, p.2))) p.1) h2 hd2
  exact (h3.div h1 hnz).sub (continuousOn_const.mul ((h2.div h1 hnz).pow 2))

/-- On every compact subset of that domain a single nonnegative constant
bounds all pairwise differences of Schwarzian values. Bound the norm by
compactness, enlarge the bound to be nonnegative, and use the triangle
inequality. Thus the local-cover budget can use constant source weights;
continuity of a diameter-valued function is unnecessary. -/
theorem holomorphic_slice_schwarzian_compact_variation_bound
    {T : Type*} [TopologicalSpace T] (Ω : Set (ℂ × T)) (hΩ : IsOpen Ω)
    (H : ℂ × T → ℂ) (hH : ContinuousOn H Ω)
    (hd : ∀ t, DifferentiableOn ℂ (fun z ↦ H (z, t)) {z | (z, t) ∈ Ω})
    (hnz : ∀ p ∈ Ω, deriv (fun z ↦ H (z, p.2)) p.1 ≠ 0)
    (K : Set (ℂ × T)) (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p ∈ K, ∀ q ∈ K,
      dist (Ghys.schwarzian (fun z ↦ H (z, p.2)) p.1)
        (Ghys.schwarzian (fun z ↦ H (z, q.2)) q.1) ≤ C := by
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn
    ((holomorphic_slice_schwarzian_continuousOn Ω hΩ H hH hd hnz).mono hKΩ)
  refine ⟨2 * max B 0, mul_nonneg (by norm_num) (le_max_right _ _), ?_⟩
  intro p hp q hq
  calc
    _ ≤ ‖Ghys.schwarzian (fun z ↦ H (z, p.2)) p.1‖ +
      ‖Ghys.schwarzian (fun z ↦ H (z, q.2)) q.1‖ := dist_le_norm_add_norm _ _
    _ ≤ B + B := add_le_add (hB p hp) (hB q hq)
    _ ≤ 2 * max B 0 := by linarith [le_max_left B 0]


/-- Subtracting the Schwarzian chain rules cancels the common change-of-source
term. Thus a bound for the two pulled-back values becomes a receiving bound
divided by the squared norm of the source derivative. This is exactly the
inverse-Jacobian weight of the local root-cover argument. -/
theorem schwarzian_pullback_variation_le
    {S T : Set ℂ} {g H₀ H₁ : ℂ → ℂ}
    (hS : IsOpen S) (hT : IsOpen T)
    (hg : DifferentiableOn ℂ g S)
    (hH₀ : DifferentiableOn ℂ H₀ T) (hH₁ : DifferentiableOn ℂ H₁ T)
    (hmap : MapsTo g S T) {z : ℂ} (hz : z ∈ S)
    (hg' : deriv g z ≠ 0) (h₀ : deriv H₀ (g z) ≠ 0) (h₁ : deriv H₁ (g z) ≠ 0)
    (C : ℝ)
    (hbound : dist (Ghys.schwarzian (H₀ ∘ g) z) (Ghys.schwarzian (H₁ ∘ g) z) ≤ C) :
    dist (Ghys.schwarzian H₀ (g z)) (Ghys.schwarzian H₁ (g z)) ≤
      C / ‖deriv g z‖ ^ 2 := by
  have heq : Ghys.schwarzian (H₀ ∘ g) z - Ghys.schwarzian (H₁ ∘ g) z =
      (Ghys.schwarzian H₀ (g z) - Ghys.schwarzian H₁ (g z)) * deriv g z ^ 2 := by
    rw [Analysis.Complex.schwarzian_chain_rule hS hT hg hH₀ hmap hz hg' h₀,
      Analysis.Complex.schwarzian_chain_rule hS hT hg hH₁ hmap hz hg' h₁]
    ring
  rw [dist_eq_norm,heq,norm_mul,norm_pow] at hbound
  rw [dist_eq_norm]
  exact (le_div_iff₀ (sq_pos_of_pos (norm_pos_iff.mpr hg'))).mpr hbound

end HolomorphicAnosov
