import HolomorphicAnosov.Analysis.MarkedRectangleG3CaratheodorySameMap
import HolomorphicAnosov.Analysis.Complex.WindingHolomorphicZeroCount.LoopWindingEqOfIncrement
import HolomorphicAnosov.Analysis.Complex.WindingHolomorphicZeroCount.LoopWindingOmittedPath
import HolomorphicAnosov.Analysis.Complex.WindingHolomorphicZeroCount.LoopWindingLift
import HolomorphicAnosov.Analysis.Complex.PositiveLoopCircleHomotopy
import HolomorphicAnosov.Analysis.Complex.QCJordanConfinement
import HolomorphicAnosov.Analysis.Complex.MarkedConformalModulus
import Mathlib.Analysis.Convex.GaugeRescale
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.OpenPartialHomeomorph.Basic

/-! # Positive orientation of a disk image

Source: Lehto–Virtanen (1973), Chapter I §3.1, pp.16–17, sense preservation;
Lyubich, Conformal Geometry, §3.3, pp.107–108, invariance of winding under
motion of the omitted point. This statement isolates the image-disk case.
-/

namespace HolomorphicAnosov
open Set Analysis.MarkedRectangle
open scoped _root_.Topology Pointwise

/-- Convert the real phase lift of a normalized nonzero loop to winding one.
The complex logarithm lift is `log ‖γ(t)-b‖ + iθ(t)`. Its real part is periodic
and its imaginary increment is `2π`, so its winding is one. This is the
logarithm-lift calculation in the positive disk boundary theorem below. -/
lemma loopWinding_eq_one_of_normalized_phase (γ : ComplexLoop) (b : ℂ)
    (hb : ∀ z, γ z ≠ b)
    (hpositive : ∃ θ : ℝ → ℝ, ContinuousOn θ (Icc 0 1) ∧
      (∀ t ∈ Icc (0 : ℝ) 1,
        Complex.exp (((θ t : ℝ) : ℂ) * Complex.I) =
          (γ (circlePhase t) - b) / (‖γ (circlePhase t) - b‖ : ℂ)) ∧
      θ 1 = θ 0 + 2 * Real.pi) : loopWinding γ b hb = 1 := by
  obtain ⟨θ, hθ, hphase, hend⟩ := hpositive
  let c : C(↑unitInterval, ℂ) :=
    ⟨fun t ↦ γ (circlePhase t) - b, by
      apply Continuous.sub _ continuous_const
      exact γ.continuous.comp (Circle.exp.continuous.comp
        (continuous_const.mul continuous_subtype_val))⟩
  have hcne (t : unitInterval) : c t ≠ 0 := sub_ne_zero.mpr (hb _)
  let L : C(↑unitInterval, ℂ) :=
    ⟨fun t ↦ (Real.log ‖c t‖ : ℂ) + (θ t : ℂ) * Complex.I, by
      have hlog := c.continuous.norm.log (fun t ↦ norm_ne_zero_iff.mpr (hcne t))
      have ht := hθ.comp_continuous continuous_subtype_val (fun t ↦ t.property)
      exact (Complex.continuous_ofReal.comp hlog).add
        ((Complex.continuous_ofReal.comp ht).mul continuous_const)⟩
  have hL (t : unitInterval) :
      Complex.exp (L t) = (puncturedLoopPath γ b hb t : ℂ) := by
    have hphase' : Complex.exp ((θ t : ℂ) * Complex.I) = c t / (‖c t‖ : ℂ) :=
      hphase t t.property
    change Complex.exp ((Real.log ‖c t‖ : ℂ) + (θ t : ℂ) * Complex.I) = c t
    rw [Complex.exp_add, ← Complex.ofReal_exp, Real.exp_log (norm_pos_iff.mpr (hcne t)),
      hphase']
    exact mul_div_cancel₀ _ (by exact_mod_cast norm_ne_zero_iff.mpr (hcne t))
  have hcperiod : c 1 = c 0 := by
    dsimp [c]
    rw [show circlePhase (1 : ℝ) = circlePhase 0 by simpa using circlePhase_add_one 0]
  have hinc : L 1 - L 0 = (1 : ℤ) * (2 * Real.pi * Complex.I : ℂ) := by
    dsimp [L]
    rw [hcperiod, hend]
    push_cast
    ring
  exact loopWinding_eq_of_increment γ b hb L hL 1 hinc

/-- The positive-boundary logarithm-lift convention is equivalent to winding
one for a continuous loop avoiding the marked point. -/
lemma windsOncePositively_iff_loopWinding_eq_one (γ : ComplexLoop) (b : ℂ)
    (hb : ∀ z, γ z ≠ b) :
    WindsOncePositively (fun t ↦ γ (circlePhase t)) b ↔ loopWinding γ b hb = 1 := by
  constructor
  · rintro ⟨_, _, L, hL, hinc⟩
    apply loopWinding_eq_of_increment γ b hb L hL 1
    simpa using hinc
  · intro hwind
    obtain ⟨K, hK, hKinc⟩ := loopWinding_lift γ b hb
    refine ⟨?_, ?_, K, ?_, ?_⟩
    · exact (γ.continuous.comp (Circle.exp.continuous.comp
        (continuous_const.mul continuous_id))).continuousOn
    · change γ (circlePhase 0) = γ (circlePhase 1)
      rw [show circlePhase (1 : ℝ) = circlePhase 0 by simpa using circlePhase_add_one 0]
    · exact hK
    · rw [hwind] at hKinc
      simpa using sub_eq_iff_eq_add.mpr (by simpa [add_comm] using hKinc)

/-- A positively wound image circle is a positive parametrization of the image
disk boundary. The boundary homeomorphism has the literal circle trace of `g`.

Source: Lehto–Virtanen I §3.1, pp.16–17; Lyubich §3.3, pp.107–108.
Proof: The argument lift in the hypothesis, plus the real logarithm of the
nonzero distance to the image center, is a continuous complex logarithm lift.
Its increment is `2πi`, so the image loop has winding one about the image center.
For any other point of the image disk, take its unique preimage and join it to
the center by a straight segment inside the source disk. Its image under `g`
avoids the image boundary by injectivity. Winding is constant along this omitted
point path. A logarithm lift with this winding gives exactly the required
positive boundary parametrization at every point of the image disk.
The positive radius excludes a collapsed boundary; no differentiability of `g`
or regularity of the image boundary is assumed. -/
theorem qc_positive_disk_boundary
    (g : OpenPartialHomeomorph ℂ ℂ) (a : ℂ) (r : ℝ) (hr : 0 < r)
    (hinside : Metric.closedBall a r ⊆ g.source)
    (β : Circle ≃ₜ frontier (g '' Metric.ball a r))
    (hβ : ∀ z : Circle, (β z : ℂ) = g (a + (r : ℂ) * (z : ℂ)))
    (hpositive : ∃ θ : ℝ → ℝ, ContinuousOn θ (Icc 0 1) ∧
      (∀ t ∈ Icc (0 : ℝ) 1,
        let c := a + (r : ℂ) * Complex.exp (((2 * Real.pi * t : ℝ) : ℂ) * Complex.I)
        Complex.exp (((θ t : ℝ) : ℂ) * Complex.I) =
          (g c - g a) / (‖g c - g a‖ : ℂ)) ∧
      θ 1 = θ 0 + 2 * Real.pi) :
    PositiveBoundaryParametrization (g '' Metric.ball a r) β := by
  classical
  let γ : ComplexLoop := ⟨fun z ↦ (β z : ℂ), continuous_subtype_val.comp β.continuous⟩
  have hcircle (z : Circle) : dist (a + (r : ℂ) * (z : ℂ)) a = r := by
    simp [dist_eq_norm, Complex.norm_real, abs_of_pos hr]
  have havoid (x : ℂ) (hx : x ∈ Metric.ball a r) (z : Circle) : γ z ≠ g x := by
    intro he
    have hz : a + (r : ℂ) * (z : ℂ) ∈ g.source :=
      hinside (by rw [Metric.mem_closedBall, hcircle])
    have heq := g.injOn hz (hinside (Metric.ball_subset_closedBall hx))
      ((hβ z).symm.trans he)
    have hx' := Metric.mem_ball.mp hx
    rw [← heq, hcircle] at hx'
    exact (lt_irrefl r) hx'
  have hac : a ∈ Metric.ball a r := Metric.mem_ball_self hr
  have ha := havoid a hac
  have hwind : loopWinding γ (g a) ha = 1 := by
    apply loopWinding_eq_one_of_normalized_phase γ (g a) ha
    obtain ⟨θ, hθ, hphase, hend⟩ := hpositive
    refine ⟨θ, hθ, ?_, hend⟩
    intro t ht
    simpa [γ, circlePhase, Circle.coe_exp, hβ] using hphase t ht
  rintro q ⟨x, hx, rfl⟩
  have hpathin (t : unitInterval) :
      (1 - (t : ℝ)) • a + (t : ℝ) • x ∈ Metric.ball a r :=
    (convex_ball a r) hac hx (sub_nonneg.mpr t.property.2) t.property.1 (by ring)
  let p : Path (g a) (g x) :=
    { toFun := fun t ↦ g ((1 - (t : ℝ)) • a + (t : ℝ) • x)
      continuous_toFun := g.continuousOn.comp_continuous (by fun_prop)
        (fun t ↦ hinside (Metric.ball_subset_closedBall (hpathin t)))
      source' := by simp
      target' := by simp }
  have hwindx : loopWinding γ (g x) (havoid x hx) = 1 := by
    rw [← loopWinding_omittedPath γ (g a) (g x) ha (havoid x hx)
      ⟨p, fun t z ↦ (havoid _ (hpathin t) z).symm⟩]
    exact hwind
  exact (windsOncePositively_iff_loopWinding_eq_one γ (g x) (havoid x hx)).mpr hwindx


/-- Positivity on all small disks transports a positive Jordan boundary through
a continuous map injective on the closure. The supplied Schoenflies chart confines the
punctured homotopy from the boundary to a small circle inside its source.
After composition, injectivity preserves avoidance, and the small image circle
has winding one by the given phase lift. Homotopy invariance gives winding one
about every point of the image region, exactly the positive-boundary convention.
Source: Lehto--Virtanen I.§3.1 pp.16--17 (sense preservation), together with
Cairns (1951) pp.860--867 (Jordan--Schoenflies confinement). -/
theorem qc_positive_jordan_boundary
    (g : ℂ → ℂ) (Q : Set ℂ) (hQopen : IsOpen Q)
    (hgc : ContinuousOn g (closure Q)) (hgi : InjOn g (closure Q))
    (β : Circle ≃ₜ frontier Q) (hβ : PositiveBoundaryParametrization Q β)
    (E : ℂ ≃ₜ ℂ) (hE : E '' Q = Metric.ball 0 1)
    (hEclosure : E '' closure Q = Metric.closedBall 0 1)
    (β' : Circle ≃ₜ frontier (g '' Q))
    (hβ' : ∀ z : Circle, (β' z : ℂ) = g (β z))
    (hpositive : ∀ a : ℂ, ∀ r : ℝ, 0 < r → Metric.closedBall a r ⊆ Q →
      ∃ θ : ℝ → ℝ, ContinuousOn θ (Icc 0 1) ∧
        (∀ t ∈ Icc (0 : ℝ) 1,
          let c := a + (r : ℂ) * Complex.exp (((2 * Real.pi * t : ℝ) : ℂ) * Complex.I)
          Complex.exp (((θ t : ℝ) : ℂ) * Complex.I) =
            (g c - g a) / (‖g c - g a‖ : ℂ)) ∧
        θ 1 = θ 0 + 2 * Real.pi) :
    PositiveBoundaryParametrization (g '' Q) β' := by
  rintro q ⟨a, ha, rfl⟩
  obtain ⟨ε, hε, hεQ⟩ := Metric.isOpen_iff.mp hQopen a ha
  let r := ε / 2
  have hr : 0 < r := half_pos hε
  have hrQ : Metric.closedBall a r ⊆ Q := by
    intro z hz
    exact hεQ ((Metric.mem_closedBall.mp hz).trans_lt (by dsimp [r]; linarith))
  let γ : ComplexLoop := ⟨fun z ↦ (β z : ℂ), continuous_subtype_val.comp β.continuous⟩
  let c : ComplexLoop := ⟨fun z ↦ a + (r : ℂ) * (z : ℂ), by fun_prop⟩
  obtain ⟨H, hH0, hH1, hHavoid⟩ := positive_loop_circle_homotopy γ a (hβ a ha) r hr
  have hcQ (z : Circle) : c z ∈ closure Q := by
    apply subset_closure
    apply hrQ
    rw [Metric.mem_closedBall]
    simp [c, dist_eq_norm, Complex.norm_real, abs_of_pos hr]
  have hstart (z : Circle) : H (0, z) ∈ closure Q := by
    rw [hH0]
    exact frontier_subset_closure (β z).property
  have hend (z : Circle) : H (1, z) ∈ closure Q := by
    rw [hH1]
    exact hcQ z
  obtain ⟨K, hK0, hK1, hKin, hKavoid⟩ :=
    qc_confine_punctured_homotopy Q E hE hEclosure a ha H hstart hend hHavoid
  let Γ : ComplexLoop := ⟨fun z ↦ (β' z : ℂ), continuous_subtype_val.comp β'.continuous⟩
  let C : ComplexLoop := ⟨fun z ↦ g (c z),
    hgc.comp_continuous c.continuous hcQ⟩
  have hΓ (z : Circle) : Γ z ≠ g a := by
    intro heq
    have heq' : (β z : ℂ) = a := hgi
      (frontier_subset_closure (β z).property) (subset_closure ha)
      ((hβ' z).symm.trans heq)
    have hnot : (β z : ℂ) ∉ Q := by
      have hz := (β z).property
      exact (show (β z : ℂ) ∈ closure Q \ Q by
        simpa only [hQopen.frontier_eq] using hz).2
    exact hnot (heq'.symm ▸ ha)
  have hC (z : Circle) : C z ≠ g a := by
    intro heq
    have heq' : c z = a := hgi (hcQ z) (subset_closure ha) heq
    have hnorm : ‖c z - a‖ = r := by
      simp [c, Complex.norm_real, abs_of_pos hr]
    rw [heq', sub_self, norm_zero] at hnorm
    exact hr.ne' hnorm.symm
  have hhom : LoopHomotopyAvoids Γ C (g a) := by
    let L : C(↑unitInterval × Circle, ℂ) := ⟨fun tz ↦ g (K tz),
      hgc.comp_continuous K.continuous (fun tz ↦ hKin tz.1 tz.2)⟩
    refine ⟨L, ?_, ?_, ?_⟩
    · intro z
      change g (K (0,z)) = (β' z : ℂ)
      rw [hK0, hH0]
      exact (hβ' z).symm
    · intro z
      change g (K (1,z)) = g (c z)
      rw [hK1, hH1]
    · intro t z heq
      exact hKavoid t z (hgi (hKin t z)
        (subset_closure ha) heq)
  have hwindC : loopWinding C (g a) hC = 1 := by
    apply loopWinding_eq_one_of_normalized_phase C (g a) hC
    obtain ⟨θ, hθ, hphase, hθend⟩ := hpositive a r hr hrQ
    refine ⟨θ, hθ, ?_, hθend⟩
    intro t ht
    simpa [C, c, circlePhase, Circle.coe_exp] using hphase t ht
  apply (windsOncePositively_iff_loopWinding_eq_one Γ (g a) hΓ).mpr
  exact (loopWinding_homotopy Γ C (g a) hΓ hC hhom).trans hwindC



/-- On a path-connected open region, positivity of a boundary parametrization
at one interior point implies positivity at every interior point. -/
lemma positive_boundary_of_one_point (Q : Set ℂ) (hQ : IsOpen Q)
    (hpath : IsPathConnected Q) (β : Circle ≃ₜ frontier Q)
    (a : ℂ) (ha : a ∈ Q)
    (hpositive : WindsOncePositively (fun t ↦ (β (circlePhase t) : ℂ)) a) :
    PositiveBoundaryParametrization Q β := by
  let γ : ComplexLoop := ⟨fun z ↦ (β z : ℂ), continuous_subtype_val.comp β.continuous⟩
  have havoid (q : ℂ) (hq : q ∈ Q) (z : Circle) : γ z ≠ q := by
    intro heq
    have hz := (β z).property
    have hz' : (β z : ℂ) ∈ closure Q \ Q := by simpa only [hQ.frontier_eq] using hz
    exact hz'.2 (by change (β z : ℂ) = q at heq; rwa [heq])
  have hw := (windsOncePositively_iff_loopWinding_eq_one γ a (havoid a ha)).mp hpositive
  intro q hq
  obtain ⟨p, hp⟩ := hpath.joinedIn a ha q hq
  apply (windsOncePositively_iff_loopWinding_eq_one γ q (havoid q hq)).mpr
  rw [← loopWinding_omittedPath γ a q (havoid a ha) (havoid q hq)
    ⟨p, fun t z ↦ (havoid _ (hp t) z).symm⟩]
  exact hw

/-- Four unit-circle points in the successive open quadrants starting in the
lower left have the required positive cyclic order. Their principal arguments
lie successively in `(-π,-π/2),(-π/2,0),(0,π/2),(π/2,π)`. -/
lemma positiveCircleFour_of_quadrants (u : Fin 4 → Circle)
    (h0 : (u 0 : ℂ).re < 0 ∧ (u 0 : ℂ).im < 0)
    (h1 : 0 < (u 1 : ℂ).re ∧ (u 1 : ℂ).im < 0)
    (h2 : 0 < (u 2 : ℂ).re ∧ 0 < (u 2 : ℂ).im)
    (h3 : (u 3 : ℂ).re < 0 ∧ 0 < (u 3 : ℂ).im) : PositiveCircleFour u := by
  let t : Fin 4 → ℝ := fun i ↦ Complex.arg (u i) / (2 * Real.pi)
  have hpi : 0 < 2 * Real.pi := by positivity
  have harg0 : Complex.arg (u 0) < -(Real.pi / 2) := by
    apply lt_of_not_ge
    simpa only [Complex.neg_pi_div_two_le_arg_iff, not_or, not_le] using ⟨h0.1, h0.2⟩
  have harg1l := Complex.neg_pi_div_two_lt_arg_iff.mpr (Or.inl h1.1)
  have harg1r := Complex.arg_neg_iff.mpr h1.2
  have harg2l : 0 < Complex.arg (u 2) := by
    have hn := Complex.arg_nonneg_iff.mpr h2.2.le
    have hne : Complex.arg (u 2) ≠ 0 := by
      intro h
      exact h2.2.ne' (Complex.arg_eq_zero_iff.mp h).2
    exact lt_of_le_of_ne hn (Ne.symm hne)
  have harg2r := Complex.arg_lt_pi_div_two_iff.mpr (Or.inl h2.1)
  have harg3 : Real.pi / 2 < Complex.arg (u 3) := by
    apply lt_of_not_ge
    simpa only [Complex.arg_le_pi_div_two_iff, not_or, not_le, not_lt] using
      ⟨h3.1, h3.2.le⟩
  refine ⟨t, ?_, ?_, ?_⟩
  · apply Fin.strictMono_iff_lt_succ.mpr
    intro i
    fin_cases i <;> dsimp [t] <;> apply (div_lt_div_iff_of_pos_right hpi).mpr <;> linarith
  · dsimp [t]
    rw [div_add_one hpi.ne', div_lt_div_iff_of_pos_right hpi]
    exact Complex.arg_lt_arg_add_two_pi _ _
  · intro i
    apply Subtype.ext
    change (u i : ℂ) = Complex.exp (((2 * Real.pi * t i : ℝ) : ℂ) * Complex.I)
    have ht : 2 * Real.pi * t i = Complex.arg (u i) := by
      dsimp [t]
      field_simp
    rw [ht]
    simpa only [Circle.norm_coe, Complex.ofReal_one, one_mul] using
      (Complex.norm_mul_exp_arg_mul_I (u i)).symm


/-- A radial disk chart of a convex region gives its positive boundary
parametrization. Positivity at the radial center is the identity normalized
phase; convexity joins any other interior point to the center while avoiding
the boundary, so omitted-point homotopy preserves winding one. -/
lemma positive_boundary_of_radial_chart (Q : Set ℂ) (hQ : IsOpen Q)
    (hconv : Convex ℝ Q) (a : ℂ) (ha : a ∈ Q)
    (H : ℂ ≃ₜ ℂ) (hH : H '' Q = Metric.ball 0 1) (_hHa : H a = 0)
    (hrad : ∀ x : ℂ, x ≠ a → ∃ s : ℝ, 0 < s ∧ H x = s • (x - a)) :
    ∃ β : Circle ≃ₜ frontier Q,
      (∀ z : Circle, H (β z) = (z : ℂ)) ∧ PositiveBoundaryParametrization Q β := by
  have hfront : H '' frontier Q = Metric.sphere (0 : ℂ) 1 := by
    rw [H.image_frontier, hH, _root_.frontier_ball (0 : ℂ) one_ne_zero]
  let e : frontier Q ≃ₜ Circle :=
    (H.image (frontier Q)).trans (Homeomorph.setCongr (by simpa [Metric.sphere, dist_zero_right] using hfront))
  let β : Circle ≃ₜ frontier Q := e.symm
  have hβ (z : Circle) : H (β z) = (z : ℂ) := congrArg Subtype.val (e.apply_symm_apply z)
  let γ : ComplexLoop := ⟨fun z ↦ (β z : ℂ), continuous_subtype_val.comp β.continuous⟩
  have havoid (q : ℂ) (hq : q ∈ Q) (z : Circle) : γ z ≠ q := by
    intro heq
    have hz := (β z).property
    have hz' : (β z : ℂ) ∈ closure Q \ Q := by simpa only [hQ.frontier_eq] using hz
    exact hz'.2 (by change (β z : ℂ) = q at heq; rwa [heq])
  have hnormphase (z : Circle) : (γ z - a) / (‖γ z - a‖ : ℂ) = (z : ℂ) := by
    obtain ⟨s, hs, heq⟩ := hrad (β z) (havoid a ha z)
    rw [hβ] at heq
    have hn : 1 = s * ‖γ z - a‖ := by
      have hn := congrArg norm heq
      simpa only [Circle.norm_coe, norm_smul, Real.norm_eq_abs, abs_of_pos hs, γ, ContinuousMap.coe_mk] using hn
    have hns : s * ‖γ z - a‖ = 1 := hn.symm
    have hnC : (s : ℂ) * (‖γ z - a‖ : ℂ) = 1 := by exact_mod_cast hns
    have hne : (‖γ z - a‖ : ℂ) ≠ 0 := by
      exact_mod_cast norm_ne_zero_iff.mpr (sub_ne_zero.mpr (havoid a ha z))
    apply (div_eq_iff hne).mpr
    rw [heq]
    change γ z - a = ((s : ℂ) * (γ z - a)) * (‖γ z - a‖ : ℂ)
    calc
      γ z - a = ((s : ℂ) * (‖γ z - a‖ : ℂ)) * (γ z - a) := by rw [hnC, one_mul]
      _ = _ := by ring
  have hwind : loopWinding γ a (havoid a ha) = 1 := by
    apply loopWinding_eq_one_of_normalized_phase γ a (havoid a ha)
    refine ⟨fun t ↦ 2 * Real.pi * t, by fun_prop, ?_, by ring⟩
    intro t ht
    rw [hnormphase]
    rfl
  refine ⟨β, hβ, ?_⟩
  intro q hq
  have hin (t : unitInterval) : (1 - (t : ℝ)) • a + (t : ℝ) • q ∈ Q :=
    hconv ha hq (sub_nonneg.mpr t.property.2) t.property.1 (by ring)
  let p : Path a q :=
    { toFun := fun t ↦ (1 - (t : ℝ)) • a + (t : ℝ) • q
      continuous_toFun := by fun_prop
      source' := by simp
      target' := by simp }
  apply (windsOncePositively_iff_loopWinding_eq_one γ q (havoid q hq)).mpr
  rw [← loopWinding_omittedPath γ a q (havoid a ha) (havoid q hq)
    ⟨p, fun t z ↦ (havoid _ (hin t) z).symm⟩]
  exact hwind


/-- The four usual rectangle corners have positive boundary order. Use the
radial gauge chart about the center. Its positive radial factors put the four
corner images into the four successive open quadrants, and its boundary
parametrization winds once positively by `positive_boundary_of_radial_chart`.
This supplies the concrete orientation convention for centered inner models. -/
theorem qc_positive_rectangle_marks {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    PositiveBoundaryFour (OpenRectangle a b) (RectangleCorner a b) := by
  let Q := OpenRectangle a b
  let c : ℂ := (a / 2 : ℝ) + (b / 2 : ℝ) * Complex.I
  have hQopen : IsOpen Q := RectangleModelPreparation.isOpen_openRectangle a b
  have hQconv : Convex ℝ Q := by
    change Convex ℝ (Complex.equivRealProdLm.toLinearMap ⁻¹' (Ioo 0 a ×ˢ Ioo 0 b))
    exact ((convex_Ioo (0 : ℝ) a).prod (convex_Ioo (0 : ℝ) b)).linear_preimage
      Complex.equivRealProdLm.toLinearMap
  have hc : c ∈ Q := by
    change c.re ∈ Ioo 0 a ∧ c.im ∈ Ioo 0 b
    simp only [c, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, sub_zero, add_zero,
      Complex.add_im, Complex.mul_im, mul_one, zero_add]
    exact ⟨⟨half_pos ha, half_lt_self ha⟩, ⟨half_pos hb, half_lt_self hb⟩⟩
  let T : ℂ ≃ₜ ℂ := Homeomorph.addLeft (-c)
  let S : Set ℂ := T '' Q
  have hSconv : Convex ℝ S := by
    change Convex ℝ ((-c) +ᵥ Q)
    exact hQconv.vadd (-c)
  have hSopen : IsOpen S := T.isOpenMap _ hQopen
  have hS0 : S ∈ 𝓝 (0 : ℂ) := hSopen.mem_nhds ⟨c, hc, neg_add_cancel c⟩
  have hSb : Bornology.IsBounded S := by
    change Bornology.IsBounded ((-c) +ᵥ Q)
    apply Bornology.IsBounded.vadd
    apply (isCompact_Icc.reProdIm isCompact_Icc).isBounded.subset
    intro z hz
    exact ⟨⟨hz.1.1.le, hz.1.2.le⟩, ⟨hz.2.1.le, hz.2.2.le⟩⟩
  have hSV : Bornology.IsVonNBounded ℝ S := NormedSpace.isVonNBounded_of_isBounded ℝ hSb
  have hD0 : Metric.ball (0 : ℂ) 1 ∈ 𝓝 0 := Metric.isOpen_ball.mem_nhds (by simp)
  have hDV := NormedSpace.isVonNBounded_ball ℝ ℂ (1 : ℝ)
  let e := gaugeRescaleHomeomorph S (Metric.ball (0 : ℂ) 1)
    hSconv hS0 hSV (convex_ball 0 1) hD0 hDV
  let H : ℂ ≃ₜ ℂ := T.trans e
  have hH : H '' Q = Metric.ball 0 1 := by
    change (fun x ↦ e (T x)) '' Q = _
    rw [← image_image e T]
    change e '' S = _
    rw [← hSopen.interior_eq]
    exact (image_gaugeRescaleHomeomorph_interior hSconv hS0 hSV
      (convex_ball 0 1) hD0 hDV).trans Metric.isOpen_ball.interior_eq
  have hHc : H c = 0 := by simp [H, T, e, gaugeRescaleHomeomorph, gaugeRescaleEquiv]
  have hrad (x : ℂ) (hx : x ≠ c) : ∃ s : ℝ, 0 < s ∧ H x = s • (x - c) := by
    have hne : -c + x ≠ 0 := by simpa [neg_add_eq_sub] using sub_ne_zero.mpr hx
    refine ⟨gauge S (-c + x) / gauge (Metric.ball (0 : ℂ) 1) (-c + x),
      div_pos ((gauge_pos (absorbent_nhds_zero hS0) hSV).mpr hne)
        ((gauge_pos (absorbent_nhds_zero hD0) hDV).mpr hne), ?_⟩
    change gaugeRescale S (Metric.ball (0 : ℂ) 1) (-c + x) = _
    simp only [gaugeRescale, neg_add_eq_sub]
  obtain ⟨β, hβ, hβpos⟩ := positive_boundary_of_radial_chart Q hQopen hQconv c hc H hH hHc hrad
  have hcornerfront (i : Fin 4) : RectangleCorner a b i ∈ frontier Q := by
    rw [hQopen.frontier_eq]
    constructor
    · change RectangleCorner a b i ∈ closure (OpenRectangle a b)
      rw [RectangleModelPreparation.closure_openRectangle ha hb]
      exact RectangleModelPreparation.corner_mem ha hb i
    · fin_cases i <;> simp [Q, OpenRectangle, RectangleCorner, Complex.reProdIm]
  have hfront : H '' frontier Q = Metric.sphere (0 : ℂ) 1 := by
    rw [H.image_frontier, hH, _root_.frontier_ball (0 : ℂ) one_ne_zero]
  let u : Fin 4 → Circle := fun i ↦ ⟨H (RectangleCorner a b i),
    by
      have hm : ‖H (RectangleCorner a b i)‖ = 1 := by
        have hm' : H (RectangleCorner a b i) ∈ Metric.sphere (0 : ℂ) 1 := by
          rw [← hfront]
          exact ⟨RectangleCorner a b i, hcornerfront i, rfl⟩
        simpa [Metric.mem_sphere, dist_zero_right] using hm'
      exact (show H (RectangleCorner a b i) ∈ Submonoid.unitSphere ℂ from
        by simpa [Submonoid.unitSphere] using hm)⟩
  have hneq (i : Fin 4) : RectangleCorner a b i ≠ c := by
    intro h
    have hnot := hcornerfront i
    rw [hQopen.frontier_eq] at hnot
    exact hnot.2 (h.symm ▸ hc)
  have hu (i : Fin 4) : ∃ s : ℝ, 0 < s ∧ (u i : ℂ) = s • (RectangleCorner a b i - c) :=
    hrad _ (hneq i)
  have hquadrants :
      ((u 0 : ℂ).re < 0 ∧ (u 0 : ℂ).im < 0) ∧
      (0 < (u 1 : ℂ).re ∧ (u 1 : ℂ).im < 0) ∧
      (0 < (u 2 : ℂ).re ∧ 0 < (u 2 : ℂ).im) ∧
      ((u 3 : ℂ).re < 0 ∧ 0 < (u 3 : ℂ).im) := by
    obtain ⟨s0, hs0, hu0⟩ := hu 0
    obtain ⟨s1, hs1, hu1⟩ := hu 1
    obtain ⟨s2, hs2, hu2⟩ := hu 2
    obtain ⟨s3, hs3, hu3⟩ := hu 3
    have hu0r : (u 0 : ℂ).re = -s0 * (a / 2) := by rw [hu0]; norm_num [RectangleCorner, c, Complex.mul_re, Complex.mul_im]
    have hu0i : (u 0 : ℂ).im = -s0 * (b / 2) := by rw [hu0]; norm_num [RectangleCorner, c, Complex.mul_re, Complex.mul_im]
    have hu1r : (u 1 : ℂ).re = s1 * (a / 2) := by rw [hu1]; norm_num [RectangleCorner, c, Complex.mul_re, Complex.mul_im]; ring_nf; simp
    have hu1i : (u 1 : ℂ).im = -s1 * (b / 2) := by rw [hu1]; norm_num [RectangleCorner, c, Complex.mul_re, Complex.mul_im]
    have hu2r : (u 2 : ℂ).re = s2 * (a / 2) := by rw [hu2]; norm_num [RectangleCorner, c, Complex.mul_re, Complex.mul_im]; ring_nf; simp
    have hu2i : (u 2 : ℂ).im = s2 * (b / 2) := by rw [hu2]; norm_num [RectangleCorner, c, Complex.mul_re, Complex.mul_im]; ring_nf; simp
    have hu3r : (u 3 : ℂ).re = -s3 * (a / 2) := by rw [hu3]; norm_num [RectangleCorner, c, Complex.mul_re, Complex.mul_im]
    have hu3i : (u 3 : ℂ).im = s3 * (b / 2) := by rw [hu3]; norm_num [RectangleCorner, c, Complex.mul_re, Complex.mul_im]; ring_nf; simp
    rw [hu0r, hu0i, hu1r, hu1i, hu2r, hu2i, hu3r, hu3i]
    constructor
    · constructor <;> nlinarith [mul_pos hs0 ha, mul_pos hs0 hb, hs0]

    constructor
    · constructor <;> nlinarith [mul_pos hs1 ha, mul_pos hs1 hb]
    constructor
    · constructor <;> nlinarith [mul_pos hs2 ha, mul_pos hs2 hb]
    · constructor <;> nlinarith [mul_pos hs3 ha, mul_pos hs3 hb]
  refine ⟨β, hβpos, u, positiveCircleFour_of_quadrants u hquadrants.1 hquadrants.2.1
    hquadrants.2.2.1 hquadrants.2.2.2, ?_⟩
  intro i
  exact H.injective (hβ (u i))

end HolomorphicAnosov


