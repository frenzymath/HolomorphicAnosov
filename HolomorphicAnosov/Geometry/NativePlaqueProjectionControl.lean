import HolomorphicAnosov.Geometry.HPSNativePlaqueFamilyData
import HolomorphicAnosov.Analysis.CommonProjectionControl

open HolomorphicAnosov HolomorphicAnosov.Analysis Set Topology
open scoped Manifold ContDiff

set_option backward.isDefEq.respectTransparency false in
/-- The normalized fixed projection of a native plaque family has common closed-ball control near
its marked center. (HPS, (5.5), pp. 61–62; Fisher–Hasselblatt, Prop. 12.1.3 and Remark 12.1.4) -/
theorem HolomorphicAnosov.NativePlaqueFamily.projection_control {E V M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    {D : ∀ x : M, Submodule ℝ (TangentSpace 𝓘(ℝ, E) x)} {x : M}
    (Φ : NativePlaqueFamily 𝓘(ℝ, E) (V := V) D x) (A : E →L[ℝ] V)
    (hA : A.comp (fderiv ℝ (fun v ↦ extChartAt 𝓘(ℝ, E) Φ.receivingAnchor
      ((Φ.plaque ⟨x, Φ.center_mem⟩).param v)) 0) = ContinuousLinearMap.id ℝ V) :
    let F := fun p : Φ.centerDomain ↦ fun v : V ↦
      extChartAt 𝓘(ℝ, E) Φ.receivingAnchor ((Φ.plaque p).param v)
    let H := fun p v ↦ A (F p v - F ⟨x, Φ.center_mem⟩ 0)
    ∃ N : TopologicalSpace.Opens Φ.centerDomain, ⟨x, Φ.center_mem⟩ ∈ N ∧
      ∃ r : ℝ, 0 < r ∧ r < Φ.radius ∧
        (∀ p ∈ N, ‖H p 0‖ < r / 8) ∧
        (∀ p ∈ N, ∀ v ∈ Metric.closedBall (0 : V) r,
          ∀ w ∈ Metric.closedBall (0 : V) r,
          ‖H p v - H p w - (v - w)‖ ≤ (1 / 2 : ℝ) * ‖v - w‖) := by
  dsimp only
  let p₀ : Φ.centerDomain := ⟨x, Φ.center_mem⟩
  let F := fun p : Φ.centerDomain ↦ fun v : V ↦
    extChartAt 𝓘(ℝ, E) Φ.receivingAnchor ((Φ.plaque p).param v)
  let H := fun p v ↦ A (F p v - F p₀ 0)
  let B := Metric.ball (0 : V) Φ.radius
  have h0 : (0 : V) ∈ B := Metric.mem_ball_self Φ.radius_pos
  have hFdiff (p : Φ.centerDomain) (v : V) (hv : v ∈ B) :
      DifferentiableAt ℝ (F p) v :=
    ((Φ.coordinate_smooth p).contDiffAt (Metric.isOpen_ball.mem_nhds hv)).differentiableAt (by simp)
  have hD (p : Φ.centerDomain) (v : V) (hv : v ∈ B) :
      HasFDerivAt (H p) (A.comp (fderiv ℝ (F p) v)) v :=
    A.hasFDerivAt.comp v ((hFdiff p v hv).hasFDerivAt.sub_const (F p₀ 0))
  have hFjet : ContinuousOn (fun z : Φ.centerDomain × V ↦ fderiv ℝ (F z.1) z.2)
      (univ ×ˢ B) := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    exact Φ.jointly_continuous_derivative.comp
      ((continuous_fst.comp continuous_subtype_val).prodMk
        ((continuous_snd.comp continuous_subtype_val).subtype_mk (fun z ↦ z.property.2)))
  have hjet : ContinuousAt (fun z : Φ.centerDomain × V ↦ fderiv ℝ (H z.1) z.2)
      (p₀, 0) := by
    have hcont := ((ContinuousLinearMap.compL ℝ V E V A).continuous.comp_continuousOn hFjet)
    have heq : EqOn (fun z : Φ.centerDomain × V ↦ A.comp (fderiv ℝ (F z.1) z.2))
        (fun z ↦ fderiv ℝ (H z.1) z.2) (univ ×ˢ B) :=
      fun z hz ↦ (hD z.1 z.2 hz.2).fderiv.symm
    exact (hcont.congr heq.symm).continuousAt
      ((isOpen_univ.prod Metric.isOpen_ball).mem_nhds ⟨mem_univ _, h0⟩)
  have hcenter : ContinuousAt (fun p ↦ H p 0) p₀ := by
    have hc : Continuous (fun p : Φ.centerDomain ↦ F p 0) :=
      ((continuousOn_extChartAt (I := 𝓘(ℝ, E)) Φ.receivingAnchor).comp_continuous
        (Φ.jointly_continuous.comp (continuous_id.prodMk
          (continuous_const (y := (⟨0, h0⟩ : B)))))
        (fun p ↦ Φ.receiving_domain p 0 h0))
    exact (A.continuous.comp (hc.sub continuous_const)).continuousAt
  obtain ⟨N, hpN, r, hr, hrR, hc, _, he⟩ :=
    common_projection_control H p₀ Φ.radius Φ.radius_pos hcenter
      (by simp [H]) (fun p v hv ↦ (hD p v hv).differentiableAt) hjet
      (by rw [(hD p₀ 0 h0).fderiv]; exact hA)
  exact ⟨N, hpN, r, hr, hrR, hc, he⟩

