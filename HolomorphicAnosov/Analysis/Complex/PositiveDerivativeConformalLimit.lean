import HolomorphicAnosov.Analysis.Complex.QCLimitWinding
import HolomorphicAnosov.Analysis.Complex.HolonomyBoundaryBuffer
import HolomorphicAnosov.Analysis.Complex.AsymptoticallyConformalLimit
import HolomorphicAnosov.Topology.DerivativeStraightLineAvoidance

namespace HolomorphicAnosov.Ghys
open Set Filter
open scoped _root_.Topology

/-- A positive real automorphism of the complex plane can be joined to the identity
through injective real linear maps. Source: Hatcher, Vector Bundles and K-Theory,
pp.23–24. Conjugate through the real orthonormal basis (1,i), use the positive
component path in two real coordinates, and conjugate the entire path back. -/
theorem complex_positive_linear_path (A : ℂ ≃L[ℝ] ℂ)
    (hdet : 0 < LinearMap.det A.toLinearMap) :
    ∃ D : unitInterval → ℂ →L[ℝ] ℂ, Continuous D ∧
      (∀ t, Function.Injective (D t)) ∧ D 0 = A.toContinuousLinearMap ∧
      D 1 = ContinuousLinearMap.id ℝ ℂ := by
  let e := Complex.orthonormalBasisOneI.repr.toContinuousLinearEquiv
  let B := e.symm.trans (A.trans e)
  have hB : 0 < LinearMap.det B.toLinearMap := by
    have heq := LinearMap.det_conj A.toLinearMap e.toLinearEquiv
    change LinearMap.det B.toLinearMap = LinearMap.det A.toLinearMap at heq
    rw [heq]
    exact hdet
  obtain ⟨D, hD, hDi, hD0, hD1⟩ :=
    exists_positive_linear_equiv_injective_path 2 B.toLinearEquiv hB
  refine ⟨fun t ↦ e.symm.toContinuousLinearMap.comp ((D t).comp e.toContinuousLinearMap),
    ?_, ?_, ?_, ?_⟩
  · fun_prop
  · intro t
    exact e.symm.injective.comp ((hDi t).comp e.injective)
  · dsimp only
    rw [hD0]
    ext z
    change e.symm (B (e z)) = A z
    simp [B]
  · dsimp only
    rw [hD1]
    ext z
    simp

/-- A positive real linear image of a counterclockwise circle has winding one.
Source: Lyubich §3.3 pp.107–108 and Hatcher pp.23–24. Apply the preceding
invertible linear path pointwise on the circle; it never meets zero. Homotopy
invariance reduces to the positive affine-circle normalization. -/
theorem positive_linear_circle_winding (A : ℂ ≃L[ℝ] ℂ)
    (hdet : 0 < LinearMap.det A.toLinearMap) (r : ℝ) (hr : 0 < r) :
    let γ : ComplexLoop := ⟨fun z ↦ A ((r : ℂ) * z), by fun_prop⟩
    ∀ hb : ∀ z, γ z ≠ 0, loopWinding γ 0 hb = 1 := by
  intro γ hb
  let σ : ComplexLoop := ⟨fun z ↦ (r : ℂ) * z, by fun_prop⟩
  have hσ (z : Circle) : σ z ≠ 0 :=
    mul_ne_zero (by exact_mod_cast hr.ne') (Circle.coe_ne_zero z)
  obtain ⟨D, hD, hDi, hD0, hD1⟩ := complex_positive_linear_path A hdet
  have hh : LoopHomotopyAvoids γ σ 0 := by
    refine ⟨⟨fun p ↦ D p.1 ((r : ℂ) * (p.2 : Circle)), by fun_prop⟩, ?_, ?_, ?_⟩
    · intro z
      change D 0 _ = _
      rw [hD0]
      rfl
    · intro z
      change D 1 _ = _
      rw [hD1]
      rfl
    · intro t z hz
      exact hσ z ((hDi t) (hz.trans (map_zero (D t)).symm))
  have hw := loopWinding_affine_circle 0 0 r hr (Metric.mem_ball_self hr)
  have hw' : loopWinding σ 0 hσ = 1 := by
    simpa [σ] using hw (by simpa [σ] using hσ)
  exact (loopWinding_homotopy γ σ 0 hb hσ hh).trans hw'

/-- An injective map with positive invertible derivative at the disk center has
boundary winding one around the center image. Source: Ghys p.590 and Lyubich
§3.3. Differentiability bounds the remainder on a small circle by less than
the minimum linear stretch. Straight interpolation with the derivative is
nonvanishing there. Then expand the radius to the specified boundary;
injectivity prevents every intermediate image circle from meeting the center. -/
theorem positive_derivative_disk_winding
    {f : ℂ → ℂ} {a : ℂ} {r : ℝ} (hr : 0 < r)
    (hf : ContinuousOn f (Metric.closedBall a r))
    (hi : InjOn f (Metric.closedBall a r))
    (A : ℂ ≃L[ℝ] ℂ) (hA : HasFDerivAt f A.toContinuousLinearMap a)
    (hdet : 0 < LinearMap.det A.toLinearMap)
    (hb : ∀ z : Circle, f (a + (r : ℂ) * z) ≠ f a) :
    loopWinding (diskBoundaryLoop a r f hr hf) (f a) hb = 1 := by
  obtain ⟨δ, hδ, hlinear⟩ :=
    HolomorphicAnosov.Topology.exists_radius_derivative_straightLine_ne_zero A hA
  let ρ := min r δ / 2
  have hρ : 0 < ρ := div_pos (lt_min hr hδ) (by norm_num)
  have hρr : ρ ≤ r := by dsimp [ρ]; linarith [min_le_left r δ]
  have hρδ : ρ < δ := by dsimp [ρ]; linarith [min_le_right r δ]
  have hcircle (s : ℝ) (hs : 0 ≤ s) (z : Circle) :
      dist (a + (s : ℂ) * (z : ℂ)) a = s := by
    simp [dist_eq_norm, Complex.norm_real, abs_of_nonneg hs]
  have hin (s : ℝ) (hs : 0 ≤ s) (hsr : s ≤ r) (z : Circle) :
      a + (s : ℂ) * (z : ℂ) ∈ Metric.closedBall a r := by
    rw [Metric.mem_closedBall, hcircle s hs z]
    exact hsr
  have hne (s : ℝ) (hs : 0 < s) (hsr : s ≤ r) (z : Circle) :
      f (a + (s : ℂ) * (z : ℂ)) - f a ≠ 0 := by
    intro hz
    have he := hi (hin s hs.le hsr z) (Metric.mem_closedBall_self hr.le)
      (sub_eq_zero.mp hz)
    have hd := hcircle s hs.le z
    rw [he, dist_self] at hd
    exact hs.ne hd
  have hsmall : Continuous (fun z : Circle ↦ f (a + (ρ : ℂ) * z)) :=
    hf.comp_continuous (by fun_prop) (hin ρ hρ.le hρr)
  let γ : ComplexLoop := ⟨fun z ↦ A ((ρ : ℂ) * z), by fun_prop⟩
  let σ : ComplexLoop := ⟨fun z ↦ f (a + (ρ : ℂ) * z) - f a,
    hsmall.sub continuous_const⟩
  let τ : ComplexLoop := ⟨fun z ↦ f (a + (r : ℂ) * z) - f a,
    (hf.comp_continuous (by fun_prop) (hin r hr.le le_rfl)).sub continuous_const⟩
  have hγ (z : Circle) : γ z ≠ 0 := by
    change A ((ρ : ℂ) * z) ≠ 0
    simpa using (mul_ne_zero (by exact_mod_cast hρ.ne' : (ρ : ℂ) ≠ 0)
      (Circle.coe_ne_zero z))
  have hσ : ∀ z, σ z ≠ 0 := hne ρ hρ hρr
  have hτ : ∀ z, τ z ≠ 0 := hne r hr le_rfl
  have hlin : LoopHomotopyAvoids γ σ 0 := by
    refine ⟨⟨fun p ↦ A ((ρ : ℂ) * (p.2 : Circle)) + (p.1 : ℝ) •
      (σ p.2 - A ((ρ : ℂ) * (p.2 : Circle))), by fun_prop⟩, ?_, ?_, ?_⟩
    · intro z
      simp [γ]
    · intro z
      simp
    · intro t z
      exact hlinear _ (by simpa [norm_mul, Complex.norm_real, abs_of_pos hρ] using hρδ)
        (mul_ne_zero (by exact_mod_cast hρ.ne') (Circle.coe_ne_zero z)) t
  have hσwind : loopWinding σ 0 hσ = 1 :=
    (loopWinding_homotopy γ σ 0 hγ hσ hlin).symm.trans
      (positive_linear_circle_winding A hdet ρ hρ hγ)
  let rad : unitInterval → ℝ := fun t ↦ ρ + (r - ρ) * t
  have hrad (t : unitInterval) : 0 < rad t ∧ rad t ≤ r := by
    have hlo := mul_nonneg (sub_nonneg.mpr hρr) t.property.1
    have hhi := mul_le_of_le_one_right (sub_nonneg.mpr hρr) t.property.2
    dsimp [rad]
    constructor <;> linarith
  have hradial : LoopHomotopyAvoids σ τ 0 := by
    refine ⟨⟨fun p ↦ f (a + (rad p.1 : ℂ) * (p.2 : Circle)) - f a, ?_⟩,
      ?_, ?_, ?_⟩
    · apply Continuous.sub _ continuous_const
      apply hf.comp_continuous (by dsimp [rad]; fun_prop)
      intro p
      exact hin _ (hrad p.1).1.le (hrad p.1).2 p.2
    · intro z
      simp [rad, σ]
    · intro z
      simp [rad, τ]
    · intro t z
      exact hne _ (hrad t).1 (hrad t).2 z
  have hτwind : loopWinding τ 0 hτ = 1 :=
    (loopWinding_homotopy σ τ 0 hσ hτ hradial).symm.trans hσwind
  exact (loopWinding_congr_sub (diskBoundaryLoop a r f hr hf) τ (f a) 0 hb hτ
    (by intro z; change f _ - f a = (f _ - f a) - 0; simp)).trans hτwind

/-- The boundary buffer controls simultaneous changes of the loop and its marked point.
Source: Ghys Proposition 2.2, p.590, with the omitted orientation step expanded by
Lyubich §3.3 homotopy invariance. Translate the second loop so the two marked points
agree. Its displacement is at most the sum of the two errors, hence the straight
homotopy misses the common marked point. Translation preserves winding. -/
theorem loopWinding_eq_of_close (γ₀ γ₁ : ComplexLoop) (b₀ b₁ : ℂ)
    (hb₀ : ∀ z, γ₀ z ≠ b₀) (hb₁ : ∀ z, γ₁ z ≠ b₁)
    (hclose : ∀ z, ‖γ₁ z - γ₀ z‖ + ‖b₁ - b₀‖ < ‖γ₀ z - b₀‖) :
    loopWinding γ₀ b₀ hb₀ = loopWinding γ₁ b₁ hb₁ := by
  let γ' : ComplexLoop := ⟨fun z ↦ γ₁ z - b₁ + b₀, by fun_prop⟩
  have hb' : ∀ z, γ' z ≠ b₀ := by
    intro z hz
    apply hb₁ z
    dsimp [γ'] at hz
    linear_combination hz
  have hnorm (z : Circle) : ‖γ' z - γ₀ z‖ < ‖γ₀ z - b₀‖ := by
    calc
      ‖γ' z - γ₀ z‖ = ‖(γ₁ z - γ₀ z) - (b₁ - b₀)‖ := by
        congr 1
        dsimp [γ']
        ring
      _ ≤ ‖γ₁ z - γ₀ z‖ + ‖b₁ - b₀‖ := norm_sub_le _ _
      _ < ‖γ₀ z - b₀‖ := hclose z
  exact (loopWinding_homotopy γ₀ γ' b₀ hb₀ hb'
    (loopHomotopyAvoids_of_norm_sub_lt γ₀ γ' b₀ hnorm)).trans
      (loopWinding_congr_sub γ' γ₁ b₀ b₁ hb' hb₁ (by intro z; dsimp [γ']; ring))

/-- Local uniform limits retain the positive circle orientation of injective approximants.
Source: Ghys Proposition 2.2, p.590; Lyubich §3.3, pp.107–108. The compact image
of the boundary avoids the image of its center, so it has a positive distance buffer.
Uniform convergence on the closed disk controls both the boundary and center errors
by one fourth of that buffer. The preceding simultaneous homotopy preserves winding,
and the logarithmic lift then gives the analytic limit theorem's exact angle condition. -/
theorem disk_angle_lift_of_locallyUniform
    {U : Set ℂ} {g : ℂ → ℂ} {F : ℕ → ℂ → ℂ}
    (hg : ContinuousOn g U) (hgi : InjOn g U)
    (hF : ∀ n, ContinuousOn (F n) U) (hFi : ∀ n, InjOn (F n) U)
    (hconv : TendstoLocallyUniformlyOn F g atTop U)
    (a : ℂ) (r : ℝ) (hr : 0 < r) (hBU : Metric.closedBall a r ⊆ U)
    (hwind : ∀ n, ∀ hb : ∀ z : Circle, F n (a + (r : ℂ) * z) ≠ F n a,
      loopWinding (diskBoundaryLoop a r (F n) hr ((hF n).mono hBU)) (F n a) hb = 1) :
    ∃ θ : ℝ → ℝ, ContinuousOn θ (Icc 0 1) ∧
      (∀ t ∈ Icc (0 : ℝ) 1,
        let c := a + (r : ℂ) * Complex.exp (((2 * Real.pi * t : ℝ) : ℂ) * Complex.I)
        Complex.exp ((θ t : ℂ) * Complex.I) = (g c - g a) / (‖g c - g a‖ : ℂ)) ∧
      θ 1 = θ 0 + 2 * Real.pi := by
  have ha : a ∈ Metric.closedBall a r := Metric.mem_closedBall_self hr.le
  have hcircle (z : Circle) : a + (r : ℂ) * (z : ℂ) ∈ Metric.sphere a r := by
    simp [Complex.norm_real, abs_of_pos hr]
  have hb : ∀ z : Circle, g (a + (r : ℂ) * z) ≠ g a := by
    intro z he
    have heq := hgi (hBU (Metric.sphere_subset_closedBall (hcircle z))) (hBU ha) he
    have hz := hcircle z
    rw [heq] at hz
    simp [hr.ne] at hz
  have hbf (n : ℕ) : ∀ z : Circle, F n (a + (r : ℂ) * z) ≠ F n a := by
    intro z he
    have heq := hFi n (hBU (Metric.sphere_subset_closedBall (hcircle z))) (hBU ha) he
    have hz := hcircle z
    rw [heq] at hz
    simp [hr.ne] at hz
  obtain ⟨m, hm, hmin, htail⟩ := holonomy_boundary_buffer
    (isCompact_closedBall a r) hBU ha (isCompact_sphere a r)
    Metric.sphere_subset_closedBall (by simpa [Metric.mem_sphere] using hr.ne)
    (hg.mono hBU) (hgi.mono hBU) hconv
  obtain ⟨n, hn⟩ := htail.exists
  have heq := loopWinding_eq_of_close
    (diskBoundaryLoop a r g hr (hg.mono hBU))
    (diskBoundaryLoop a r (F n) hr ((hF n).mono hBU))
    (g a) (F n a) hb (hbf n) (by
      intro z
      have h := hn _ (hcircle z)
      have h' := hmin _ (hcircle z)
      change ‖F n (a + (r : ℂ) * z) - g (a + (r : ℂ) * z)‖ + ‖F n a - g a‖ < ‖g (a + (r : ℂ) * z) - g a‖
      linarith [h.1, h.2.1])
  obtain ⟨θ, hθ, hphase, hend⟩ := winding_one_angle_lift
    (diskBoundaryLoop a r g hr (hg.mono hBU)) (g a) hb (heq.trans (hwind n (hbf n)))
  refine ⟨θ, hθ, ?_, hend⟩
  intro t ht
  have h := hphase t ht
  change Complex.exp ((θ t : ℂ) * Complex.I) =
    (g (a + (r : ℂ) * (Circle.exp (2 * Real.pi * t) : ℂ)) - g a) /
      (‖g (a + (r : ℂ) * (Circle.exp (2 * Real.pi * t) : ℂ)) - g a‖ : ℂ) at h
  simpa only [Circle.coe_exp] using h

/-- The positive orientation hypothesis of the analytic closure theorem follows from
the approximants. Source: Ghys Proposition 2.2, p.590. For each retained closed disk,
the derivative at its center and injectivity give winding one of every approximant.
Compact uniform convergence preserves that winding, and the angle-lift construction
is exactly the orientation predicate in the asymptotically conformal limit theorem. -/
theorem asymptotically_conformal_limit_of_positive_derivatives
    (U : Set ℂ) (hU : IsOpen U) (hne : U.Nonempty) (hc : IsConnected U)
    (F : ℕ → OpenPartialHomeomorph ℂ ℂ) (g : OpenPartialHomeomorph ℂ ℂ)
    (hFs : ∀ n, (F n).source = U) (hgs : g.source = U)
    (hF : ∀ n, ContDiffOn ℝ 1 (F n) U)
    (hFi : ∀ n, ContDiffOn ℝ 1 (F n).symm (F n).target)
    (hd : ∀ n z, z ∈ U → ∃ A : ℂ ≃L[ℝ] ℂ,
      HasFDerivAt (F n) A.toContinuousLinearMap z ∧ 0 < A.toContinuousLinearMap.det)
    (K : ℕ → ℝ) (hK : ∀ n, 1 ≤ K n) (hKt : Tendsto K atTop (𝓝 1))
    (hDist : ∀ n z, z ∈ U → ∀ v w : ℂ, ‖v‖ = 1 → ‖w‖ = 1 →
      ‖fderiv ℝ (F n) z v‖ ≤ K n * ‖fderiv ℝ (F n) z w‖)
    (hconv : TendstoLocallyUniformlyOn (fun n z ↦ F n z) g atTop U) :
    DifferentiableOn ℂ g U := by
  apply asymptotically_conformal_c1_homeomorphism_limit U hU hne hc F g hFs hgs
    hF hFi hd K hK hKt hDist hconv
  intro a r hr hBU
  refine disk_angle_lift_of_locallyUniform (by simpa [hgs] using g.continuousOn)
    (by simpa [hgs] using g.injOn) (fun n ↦ (hF n).continuousOn)
    (fun n ↦ by simpa [hFs n] using (F n).injOn) hconv a r hr hBU ?_
  intro n hb
  obtain ⟨A, hA, hdet⟩ := hd n a (hBU (Metric.mem_closedBall_self hr.le))
  exact positive_derivative_disk_winding hr ((hF n).continuousOn.mono hBU)
    ((by simpa [hFs n] using (F n).injOn : InjOn (F n) U).mono hBU) A hA hdet hb

end HolomorphicAnosov.Ghys

