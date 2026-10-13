import HolomorphicAnosov.Analysis.HolomorphicSliceTwoDerivativesContinuous
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Complex.Basic

/-! # Continuity of holomorphic slice frames and their scalar coordinates

Source: Demailly, Chapter I §3.B pp.22–23, continuity of holomorphic derivatives;
Ghys (1995), §3 pp.591–592, tangent frames in flowbox coordinates.
-/
noncomputable section
namespace HolomorphicAnosov
open Set Filter _root_.Topology

/-- The first derivative of a continuous family of holomorphic maps into a finite
complex coordinate space is jointly continuous on its actual open domain.

Source: Demailly I §3.B pp.22–23. Apply the scalar joint derivative theorem to each
coordinate. The coordinatewise derivative formula and continuity into a finite
product give the vector assertion. Empty coordinate spaces pose no problem. -/
theorem holomorphic_slice_vector_derivative_continuousOn
    {T κ : Type*} [TopologicalSpace T] [Fintype κ]
    (Ω : Set (ℂ × T)) (hΩ : IsOpen Ω) (F : ℂ × T → κ → ℂ)
    (hF : ContinuousOn F Ω)
    (hd : ∀ t, DifferentiableOn ℂ (fun z ↦ F (z, t)) {z | (z, t) ∈ Ω}) :
    ContinuousOn (fun p : ℂ × T ↦ deriv (fun z ↦ F (z, p.2)) p.1) Ω := by
  have hcoord (k : κ) := SliceDerivativePreparation.joint_deriv_continuousOn_open
    Ω hΩ (fun p ↦ F p k) ((continuous_apply k).comp_continuousOn hF)
    (fun t ↦ (differentiableOn_pi.mp (hd t)) k)
  have hpi : ContinuousOn (fun p k ↦ deriv (fun z ↦ F (z, p.2) k) p.1) Ω :=
    continuousOn_pi.mpr hcoord
  apply hpi.congr
  intro p hp
  exact (deriv_pi (fun k ↦ ((differentiableOn_pi.mp (hd p.2)) k).differentiableAt
    ((hΩ.preimage (continuous_id.prodMk continuous_const)).mem_nhds hp)))

/-- Scalar coordinates relative to a continuous nowhere-zero complex frame are
continuous whenever the represented vector is continuous.

Source: Ghys §3 pp.591–592, inverse tangent coefficient chart. At a given point,
choose a nonzero coordinate of the frame. That coordinate stays nonzero nearby,
and the scalar coefficient is the represented coordinate divided by the frame
coordinate. The quotient is continuous and agrees with the coefficient locally.
No assumption of finite dimensionality is needed for this product-space fact. -/
theorem continuous_scalar_of_continuous_nonzero_frame
    {X κ : Type*} [TopologicalSpace X] (a : X → ℂ) (e v : X → κ → ℂ)
    (he : Continuous e) (hv : Continuous v) (hne : ∀ x, e x ≠ 0)
    (h : ∀ x, v x = a x • e x) : Continuous a := by
  classical
  rw [continuous_iff_continuousAt]
  intro x
  obtain ⟨k, hk⟩ : ∃ k, e x k ≠ 0 := by
    by_contra hn
    push Not at hn
    exact hne x (funext hn)
  have hek : ContinuousAt (fun y ↦ e y k) x := (continuous_apply k).comp he |>.continuousAt
  have hvk : ContinuousAt (fun y ↦ v y k) x := (continuous_apply k).comp hv |>.continuousAt
  apply (hvk.div hek hk).congr
  filter_upwards [hek.eventually_ne hk] with y hy
  have hyv := congrFun (h y) k
  change v y k = a y * e y k at hyv
  change v y k / e y k = a y
  rw [hyv, mul_div_cancel_right₀ _ hy]

end HolomorphicAnosov
