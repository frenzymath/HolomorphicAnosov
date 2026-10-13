import Mathlib.Analysis.Complex.CauchyIntegral
import HolomorphicAnosov.Analysis.Complex.WindingHolomorphicZeroCount
import Mathlib.Analysis.Calculus.DSlope
/-! # Winding of a holomorphic closed disk extension

Source: Lyubich, Conformal Geometry, §3.3 pp.107–108, the topological
argument principle and homotopy invariance. The radial and divided-difference
arguments below are agent-written expansions for the Carathéodory application.

For the boundary winding, choose a radius r strictly between |x| and one.
Injectivity makes x the sole zero of φ−φ(x) in that disk, with order one by
φ′(x)≠0. The argument principle gives winding one. Interpolating the radius
from r to one avoids φ(x), since injectivity would force a point of radius
at least r to equal x. Homotopy invariance gives the boundary result.

For transport of arbitrary circle loops, write F(z)−F(0)=z G(z), where
G is the continuous divided difference, with G(0)=F′(0). It has no zero:
at zero use the derivative premise, elsewhere use injectivity. The loop
G∘σ contracts radially inside the zero-free disk image of G, hence has
winding zero. Product additivity now gives w(F∘σ,F(0))=w(σ,0).
-/
open Set Metric
open scoped Topology
namespace HolomorphicAnosov
noncomputable section
/-- The argument principle for an injective holomorphic disk map: the sole zero
of f-f(x) is x, and a nonzero derivative makes its analytic order one. -/
theorem inner_winding_one {φ : ℂ → ℂ} {r : ℝ}
    (hr : 0 < r) (ha : AnalyticOnNhd ℂ φ (closedBall (0 : ℂ) r))
    (hi : InjOn φ (closedBall (0 : ℂ) r)) {x : ℂ}
    (hx : x ∈ ball (0 : ℂ) r) (hd : deriv φ x ≠ 0)
    (hb : ∀ ζ, diskBoundaryLoop 0 r φ hr ha.continuousOn ζ ≠ φ x) :
    loopWinding (diskBoundaryLoop 0 r φ hr ha.continuousOn) (φ x) hb = 1 := by
  have hboundary : ∀ z ∈ sphere (0 : ℂ) r, φ z ≠ φ x := by
    intro z hz he
    have heq := hi (sphere_subset_closedBall hz) (ball_subset_closedBall hx) he
    subst z
    exact (ne_of_lt hx) hz
  obtain ⟨s, hs, _, hw, _⟩ := winding_holomorphic_zero_count.2.2.2.2
    0 (φ x) r φ hr ha hboundary
  have hsx : s = {x} := by
    ext z
    rw [hs, Finset.mem_singleton]
    constructor
    · intro hz
      exact hi (ball_subset_closedBall hz.1) (ball_subset_closedBall hx) hz.2
    · rintro rfl
      exact ⟨hx, rfl⟩
  have hord : analyticOrderAt (fun z ↦ φ z - φ x) x = 1 :=
    (ha x (ball_subset_closedBall hx)).analyticOrderAt_sub_eq_one_of_deriv_ne_zero hd
  rw [hsx] at hw
  simpa [analyticOrderNatAt, hord] using hw
end
end HolomorphicAnosov
namespace HolomorphicAnosov
noncomputable section
/-- Radial deformation carries the winding of an interior circle to the boundary
of a continuous injective closed-disk extension. All radii stay strictly outside x. -/
theorem closed_disk_winding_one
    {φ : ℂ → ℂ} (hh : DifferentiableOn ℂ φ (ball (0 : ℂ) 1))
    (F : closedBall (0 : ℂ) 1 → ℂ) (hF : Continuous F) (hi : Function.Injective F)
    (he : ∀ z (hz : z ∈ ball (0 : ℂ) 1), F ⟨z, ball_subset_closedBall hz⟩ = φ z)
    {x : ℂ} (hx : x ∈ ball (0 : ℂ) 1) (hd : deriv φ x ≠ 0) :
    let γ : ComplexLoop := ⟨fun z : Circle ↦ F ⟨z, sphere_subset_closedBall z.property⟩,
      hF.comp (continuous_subtype_val.subtype_mk _)⟩
    ∀ hb : ∀ ζ, γ ζ ≠ φ x, loopWinding γ (φ x) hb = 1 := by
  classical
  dsimp only
  let γ : ComplexLoop := ⟨fun z : Circle ↦ F ⟨z, sphere_subset_closedBall z.property⟩,
    hF.comp (continuous_subtype_val.subtype_mk _)⟩
  intro hb
  have hxn : ‖x‖ < 1 := by simpa using hx
  obtain ⟨r, hxr, hr1⟩ := exists_between hxn
  have hr : 0 < r := lt_of_le_of_lt (norm_nonneg x) hxr
  have hsub : closedBall (0 : ℂ) r ⊆ ball (0 : ℂ) 1 := by
    intro z hz
    exact lt_of_le_of_lt hz hr1
  have ha : AnalyticOnNhd ℂ φ (closedBall (0 : ℂ) r) :=
    (hh.analyticOnNhd isOpen_ball).mono hsub
  have hφi : InjOn φ (closedBall (0 : ℂ) r) := by
    intro z hz w hw heq
    apply Subtype.mk.inj
    apply hi
    rw [he z (hsub hz), he w (hsub hw)]
    exact heq
  let σ := diskBoundaryLoop 0 r φ hr ha.continuousOn
  have hsphere (z : Circle) : ‖(r : ℂ) * (z : ℂ)‖ = r := by
    simp [abs_of_pos hr]
  have hσ : ∀ z, σ z ≠ φ x := by
    intro z heq
    have heqx : (r : ℂ) * (z : ℂ) = x := hφi
      (by simp [mem_closedBall, abs_of_pos hr])
      (ball_subset_closedBall (by simpa using hxr)) (by simpa [σ, diskBoundaryLoop] using heq)
    have hn := congrArg norm heqx
    rw [hsphere] at hn
    linarith
  have hw : loopWinding σ (φ x) hσ = 1 := inner_winding_one hr ha hφi
    (by simpa using hxr) hd hσ
  have hnorm (s : unitInterval) : r ≤ (1 - (s : ℝ)) * r + (s : ℝ) ∧
      (1 - (s : ℝ)) * r + (s : ℝ) ≤ 1 := by
    constructor <;> nlinarith [s.property.1, s.property.2]
  have hmem (s : unitInterval) (z : Circle) :
      (((1 - (s : ℝ)) * r + (s : ℝ) : ℝ) : ℂ) * (z : ℂ) ∈ closedBall (0 : ℂ) 1 := by
    simp only [mem_closedBall, dist_zero_right, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, Circle.norm_coe, mul_one]
    rw [abs_of_nonneg (hr.le.trans (hnorm s).1)]
    exact (hnorm s).2
  have hhom : LoopHomotopyAvoids σ γ (φ x) := by
    refine ⟨⟨fun p ↦ F ⟨(((1 - (p.1 : ℝ)) * r + (p.1 : ℝ) : ℝ) : ℂ) *
      (p.2 : ℂ), hmem p.1 p.2⟩, hF.comp (by fun_prop)⟩, ?_, ?_, ?_⟩
    · intro z
      change F _ = σ z
      simp only [Set.Icc.coe_zero, sub_zero, one_mul, add_zero]
      rw [he _ (by simpa [abs_of_pos hr] using hr1 : (r : ℂ) * (z : ℂ) ∈ ball (0 : ℂ) 1)]
      simp [σ, diskBoundaryLoop]
    · intro z
      simp [γ]
    · intro s z heq
      have hf : F ⟨(((1 - (s : ℝ)) * r + (s : ℝ) : ℝ) : ℂ) * (z : ℂ),
        hmem s z⟩ = F ⟨x, ball_subset_closedBall hx⟩ := heq.trans (he x hx).symm
      have heqx := congrArg Subtype.val (hi hf)
      have hn := congrArg norm heqx
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, Circle.norm_coe,
        mul_one, abs_of_nonneg (hr.le.trans (hnorm s).1)] at hn
      linarith [(hnorm s).1]
  exact (loopWinding_homotopy σ γ (φ x) hσ hb hhom).symm.trans hw
end
end HolomorphicAnosov
open Set Metric
open scoped Topology
namespace HolomorphicAnosov
noncomputable section
/-- Divided differences provide a zero-free factor on the disk. Contracting this
factor proves that composing any circle loop with the extension preserves its winding. -/
theorem winding_transport_closed_disk {F : ℂ → ℂ}
    (hc : ContinuousOn F (closedBall (0 : ℂ) 1))
    (hd : DifferentiableAt ℂ F 0) (hne : deriv F 0 ≠ 0)
    (hi : InjOn F (closedBall (0 : ℂ) 1))
    (σ : C(Circle, Circle)) :
    let γ : ComplexLoop := ⟨fun z ↦ F (σ z),
      hc.comp_continuous (by fun_prop) (fun z ↦ by simp)⟩
    let δ : ComplexLoop := ⟨fun z ↦ (σ z : ℂ), by fun_prop⟩
    ∀ hb : ∀ z, γ z ≠ F 0, loopWinding γ (F 0) hb =
      loopWinding δ 0 (fun z ↦ Circle.coe_ne_zero _) := by
  dsimp only
  let γ : ComplexLoop := ⟨fun z ↦ F (σ z),
    hc.comp_continuous (by fun_prop) (fun z ↦ by simp)⟩
  let δ : ComplexLoop := ⟨fun z ↦ (σ z : ℂ), by fun_prop⟩
  let G := dslope F 0
  have hG : ContinuousOn G (closedBall (0 : ℂ) 1) :=
    (continuousOn_dslope (closedBall_mem_nhds (0 : ℂ) (by norm_num))).mpr ⟨hc, hd⟩
  have hGn : ∀ z ∈ closedBall (0 : ℂ) 1, G z ≠ 0 := by
    intro z hz
    by_cases hz0 : z = 0
    · simpa [G, hz0] using hne
    · intro hzero
      have hsub := sub_smul_dslope F 0 z
      have heq : F z = F 0 := by apply sub_eq_zero.mp; simpa [G, hzero] using hsub.symm
      exact hz0 (hi hz (by simp) heq)
  let η : ComplexLoop := ⟨fun z ↦ G (σ z),
    hG.comp_continuous (by fun_prop) (fun z ↦ by simp)⟩
  have hη : ∀ z, η z ≠ 0 := fun z ↦ hGn (σ z) (by simp)
  have hδ : ∀ z, δ z ≠ 0 := fun z ↦ Circle.coe_ne_zero _
  have hhom : LoopHomotopyAvoids η (constantLoop (G 0)) 0 := by
    have hmem (t : unitInterval) (z : Circle) :
        ((1 - (t : ℝ) : ℝ) : ℂ) * (σ z : ℂ) ∈ closedBall (0 : ℂ) 1 := by
      simp only [mem_closedBall, dist_zero_right, norm_mul, Complex.norm_real,
        Real.norm_eq_abs, Circle.norm_coe, mul_one,
        abs_of_nonneg (sub_nonneg.mpr t.property.2)]
      linarith [t.property.1]
    refine ⟨⟨fun p ↦ G (((1 - (p.1 : ℝ) : ℝ) : ℂ) * (σ p.2 : ℂ)),
      hG.comp_continuous (by fun_prop) (fun p ↦ hmem p.1 p.2)⟩, ?_, ?_, ?_⟩
    · intro z; simp [η]
    · intro z; simp [constantLoop]
    · intro t z; exact hGn _ (hmem t z)
  have hwindη : loopWinding η 0 hη = 0 :=
    (loopWinding_homotopy η (constantLoop (G 0)) 0 hη (fun _ ↦ hGn 0 (by simp))
      hhom).trans (loopWinding_constant (G 0) 0 (hGn 0 (by simp)))
  intro hb
  have hmul : ∀ z, δ z * η z ≠ 0 := fun z ↦ mul_ne_zero (hδ z) (hη z)
  have hw := loopWinding_congr_sub γ (δ * η) (F 0) 0 hb hmul (by
    intro z
    simpa [γ, δ, η, G, smul_eq_mul] using (sub_smul_dslope F 0 (σ z : ℂ)).symm)
  exact hw.trans ((loopWinding_mul δ η hδ hη).trans (by rw [hwindη, add_zero]))
end
end HolomorphicAnosov
