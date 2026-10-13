import HolomorphicAnosov.Analysis.MarkedRectangleCircleShortArc
import HolomorphicAnosov.Analysis.MarkedRectangleG3CaratheodorySameMap
import Mathlib.Analysis.Convex.GaugeRescale
import Mathlib.Analysis.SpecialFunctions.Complex.CircleMap
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Topology.Homeomorph.Defs
import HolomorphicAnosov.Analysis.Complex.DiskMobiusNorm
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
import HolomorphicAnosov.Analysis.MarkedRectangleG3CanonicalPrevertices
import HolomorphicAnosov.Analysis.MarkedRectangleG3PrimitiveWithBoundary
import HolomorphicAnosov.Analysis.MarkedRectangleG3CentralBoundaryPhase
import HolomorphicAnosov.Analysis.MarkedRectangleG3BoundarySegmentClosure
import HolomorphicAnosov.Analysis.MarkedRectangleG3AdjacentBoundaryPhase
import HolomorphicAnosov.Analysis.MarkedRectangleG3HorizontalSideClosure
import HolomorphicAnosov.Analysis.MarkedRectangleG3OuterBoundaryAlignment
import HolomorphicAnosov.Analysis.MarkedRectangleG3OuterSideCoverage
import HolomorphicAnosov.Analysis.MarkedRectangleG3BijectionAdapters
import HolomorphicAnosov.Analysis.MarkedRectangleG3CayleyRealPrevertices
import HolomorphicAnosov.Analysis.MarkedRectangleG3RealQuadrupleNormalization

/-!
# Marked disk-to-rectangle Schwarz–Christoffel construction

Source: Stein–Shakarchi, Complex Analysis (2003), Chapter 8 §§4.1, 4.4–4.5;
Bak–Newman, Complex Analysis (3rd ed., 2010), pp.177, 183–191.

The canonical primitive has a continuous Cayley pullback to the closed disk.
Its straight-side boundary values and nonvanishing derivative give bijectivity
onto the open rectangle by the maximum-principle/covering adapters. The existing
Carathéodory theorem identifies this same continuous extension as a homeomorphism.
An explicit cancelled fractional expression transports the original four marks
without a boundary pole. Translation gives the prescribed rectangle; connected
boundary arcs avoiding the other corners cover precisely their marked sides.
All proofs in this module are complete. Imported providers may still carry
transitive admitted dependencies, tracked by their own DAG nodes.
-/

noncomputable section
namespace HolomorphicAnosov.Analysis.MarkedRectangle.Source
open Set HolomorphicAnosov.Analysis.MarkedRectangle
open MeasureTheory
open Metric

def PositiveCircleCyclicOrder (ζ : Fin 4 → ℂ) : Prop :=
  ∃ θ : Fin 4 → ℝ, StrictMono θ ∧ θ 3 < θ 0 + 2 * Real.pi ∧
    ∀ i, circleMap 0 1 (θ i) = ζ i

def PositiveClosedCircleArc (u v : ℂ) : Set ℂ :=
  {z | ∃ α β : ℝ, α < β ∧ β < α + 2 * Real.pi ∧
    circleMap 0 1 α = u ∧ circleMap 0 1 β = v ∧
    z ∈ circleMap 0 1 '' Icc α β}

def OpenRectangle (a b : ℝ) : Set ℂ :=
  Complex.reProdIm (Ioo 0 a) (Ioo 0 b)

def ClosedRectangle (a b : ℝ) : Set ℂ :=
  Complex.reProdIm (Icc 0 a) (Icc 0 b)

def RectangleCorner (a b : ℝ) (i : Fin 4) : ℂ :=
  match i.val with
  | 0 => 0
  | 1 => (a : ℂ)
  | 2 => (a : ℂ) + (b : ℂ) * Complex.I
  | _ => (b : ℂ) * Complex.I

def ClosedRectangleSide (a b : ℝ) (i : Fin 4) : Set ℂ :=
  match i.val with
  | 0 => Complex.reProdIm (Icc 0 a) {0}
  | 1 => Complex.reProdIm {a} (Icc 0 b)
  | 2 => Complex.reProdIm (Icc 0 a) {b}
  | _ => Complex.reProdIm {0} (Icc 0 b)

/-- Every directed adjacent arc in a positive four-point cyclic order is nonempty.
Source: the increasing angle lift convention for the four boundary arcs in
Stein--Shakarchi, *Complex Analysis*, Chapter 8, §§4.1 and 4.5. -/
theorem positiveClosedCircleArc_nonempty_of_cyclic
    {ζ : Fin 4 → ℂ} (hcyclic : PositiveCircleCyclicOrder ζ) :
    ∀ i, (PositiveClosedCircleArc (ζ i) (ζ (i + 1))).Nonempty := by
  rcases hcyclic with ⟨θ, hmono, hlast, hζ⟩
  intro i
  fin_cases i
  · refine ⟨circleMap 0 1 (θ 0), ?_⟩
    have h01 : θ 0 < θ 1 := hmono (by decide)
    have h13 : θ 1 < θ 3 := hmono (by decide)
    refine ⟨θ 0, θ 1, h01, lt_trans h13 hlast, hζ 0, hζ 1, ?_⟩
    exact mem_image_of_mem _ (mem_Icc.mpr ⟨le_rfl, h01.le⟩)
  · refine ⟨circleMap 0 1 (θ 1), ?_⟩
    have h12 : θ 1 < θ 2 := hmono (by decide)
    have h23 : θ 2 < θ 3 := hmono (by decide)
    have h03 : θ 0 < θ 1 := hmono (by decide)
    refine ⟨θ 1, θ 2, h12, by linarith [hlast, h03], hζ 1, hζ 2, ?_⟩
    exact mem_image_of_mem _ (mem_Icc.mpr ⟨le_rfl, h12.le⟩)
  · refine ⟨circleMap 0 1 (θ 2), ?_⟩
    have h23 : θ 2 < θ 3 := hmono (by decide)
    have h02 : θ 0 < θ 2 := hmono (by decide)
    refine ⟨θ 2, θ 3, h23, by linarith, hζ 2, hζ 3, ?_⟩
    exact mem_image_of_mem _ (mem_Icc.mpr ⟨le_rfl, h23.le⟩)
  · have hperiod : circleMap 0 1 (θ 0 + 2 * Real.pi) = ζ 0 := by
      calc
        circleMap 0 1 (θ 0 + 2 * Real.pi) = circleMap 0 1 (θ 0) :=
          periodic_circleMap 0 1 (θ 0)
        _ = ζ 0 := hζ 0
    refine ⟨circleMap 0 1 (θ 3), ?_⟩
    have h03 : θ 0 < θ 3 := hmono (by decide)
    refine ⟨θ 3, θ 0 + 2 * Real.pi, hlast, by linarith, hζ 3, hperiod, ?_⟩
    exact mem_image_of_mem _ (mem_Icc.mpr ⟨le_rfl, hlast.le⟩)

/-- Given an admissible pair of angle representatives, both represented
endpoints belong to the corresponding directed closed arc. -/
theorem positiveClosedCircleArc_mem_left
    {u v : ℂ} {α β : ℝ} (hab : α < β) (hperiod : β < α + 2 * Real.pi)
    (hu : circleMap 0 1 α = u) (hv : circleMap 0 1 β = v) :
    u ∈ PositiveClosedCircleArc u v := by
  refine ⟨α, β, hab, hperiod, hu, hv, ?_⟩
  rw [← hu]
  exact mem_image_of_mem (circleMap 0 1) (mem_Icc.mpr ⟨le_rfl, hab.le⟩)

theorem positiveClosedCircleArc_mem_right
    {u v : ℂ} {α β : ℝ} (hab : α < β) (hperiod : β < α + 2 * Real.pi)
    (hu : circleMap 0 1 α = u) (hv : circleMap 0 1 β = v) :
    v ∈ PositiveClosedCircleArc u v := by
  refine ⟨α, β, hab, hperiod, hu, hv, ?_⟩
  rw [← hv]
  exact mem_image_of_mem (circleMap 0 1) (mem_Icc.mpr ⟨hab.le, le_rfl⟩)

/-- A bounded convex open planar set has a Jordan boundary: a gauge rescaling
homeomorphism of the ambient plane sends its frontier to the unit circle. -/
lemma convex_open_jordan {Q : Set ℂ} (hc : Convex ℝ Q) (ho : IsOpen Q)
    (hne : Q.Nonempty) (hb : Bornology.IsBounded Q) :
    HolomorphicAnosov.Analysis.MarkedRectangle.HasJordanBoundary Q := by
  obtain ⟨e, _, _, hfront⟩ :=
    exists_homeomorph_image_interior_closure_frontier_eq_unitBall hc
      (by rwa [ho.interior_eq]) hb
  refine ⟨fun z : Circle ↦ e.symm (z : ℂ),
    e.symm.isEmbedding.comp (Topology.IsEmbedding.subtypeVal), ?_⟩
  ext z
  constructor
  · rintro ⟨w,rfl⟩
    have hw : (w : ℂ) ∈ e '' frontier Q := by
      rw [hfront]
      exact w.property
    obtain ⟨z,hz,hzw⟩ := hw
    simpa [← hzw] using hz
  · intro hz
    have hez : e z ∈ sphere (0 : ℂ) 1 := hfront ▸ mem_image_of_mem e hz
    exact ⟨⟨e z,hez⟩,e.symm_apply_apply z⟩

/-- The same continuous extension of a holomorphic disk bijection to a bounded
convex domain is the Carathéodory homeomorphism on the closed disk. -/
lemma convex_continuous_extension_homeomorph {Q : Set ℂ}
    (hc : Convex ℝ Q) (ho : IsOpen Q) (hne : Q.Nonempty) (hb : Bornology.IsBounded Q)
    (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f (ball (0 : ℂ) 1))
    (hbij : BijOn f (ball (0 : ℂ) 1) Q) (hcont : ContinuousOn f (closedBall (0 : ℂ) 1)) :
    ∃ e : closedBall (0 : ℂ) 1 ≃ₜ closure Q,
      ∀ z : closedBall (0 : ℂ) 1, (e z : ℂ) = f z := by
  let : ContractibleSpace Q := hc.contractibleSpace hne
  have hsimply : IsSimplyConnected Q := by
    change SimplyConnectedSpace Q
    infer_instance
  obtain ⟨Φ,hΦ,_,_,_⟩ := HolomorphicAnosov.Analysis.MarkedRectangle.caratheodory_same_map
    Q hne ho hb hsimply (convex_open_jordan hc ho hne hb) f
    (by simpa [HolomorphicAnosov.Analysis.MarkedRectangle.unitDisk,
      Metric.ball, dist_zero_right] using hf)
    (by simpa [HolomorphicAnosov.Analysis.MarkedRectangle.unitDisk,
      Metric.ball, dist_zero_right] using hbij)
  let e₀ : closedBall (0 : ℂ) 1 ≃ₜ HolomorphicAnosov.Analysis.MarkedRectangle.closedUnitDisk :=
    Homeomorph.setCongr (by ext z; simp [Metric.mem_closedBall,
      HolomorphicAnosov.Analysis.MarkedRectangle.closedUnitDisk])
  let e := e₀.trans Φ
  refine ⟨e, ?_⟩
  have hdense : DenseRange (Set.inclusion
      (ball_subset_closedBall : ball (0 : ℂ) 1 ⊆ closedBall 0 1)) := by
    rw [denseRange_inclusion_iff, closure_ball (0 : ℂ) (by norm_num : (1 : ℝ) ≠ 0)]
  have heq : (fun z : closedBall (0 : ℂ) 1 ↦ (e z : ℂ)) =
      (fun z : closedBall (0 : ℂ) 1 ↦ f (z : ℂ)) := by
    apply hdense.equalizer (continuous_subtype_val.comp e.continuous) hcont.domRestrict
    funext z
    exact hΦ (z : ℂ) (by
      change ‖(z : ℂ)‖ < 1
      exact mem_ball_zero_iff.mp z.property)
  exact fun z ↦ congrFun heq z


/-- The primitive derivative square rewrites to the canonical four-prevertex
polynomial. Source: Bak--Newman, *Complex Analysis* (3rd ed., 2010),
pp. 184--186, together with the primitive identity supplied by the preceding
Schwarz--Christoffel source theorem. -/
theorem canonical_primitive_derivative_square
    {k : ℝ} (W : ℂ → ℂ)
    (hW : ∀ z : ℂ, 0 < z.im →
      (deriv W z) ^ 2 = -(∏ j : Fin 4, (z -
        (HolomorphicAnosov.Analysis.MarkedRectangle.canonicalPrevertex k j : ℂ)))⁻¹) :
    ∀ z : ℂ, 0 < z.im →
      (deriv W z) ^ 2 = -((z + (1 / k : ℂ)) * (z + 1) *
        (z - 1) * (z - (1 / k : ℂ)))⁻¹ := by
  intro z hz
  rw [hW z hz, HolomorphicAnosov.Analysis.MarkedRectangle.canonicalPrevertex_product]

/-- Vertical path variation for a holomorphic function whose derivative has the
quadratic decay supplied by the Schwarz--Christoffel square-root kernel.  The
estimate is stated away from the real axis endpoint so that the existing
interval-integral displacement theorem applies directly. -/
theorem norm_vertical_sub_le_of_deriv_decay
    (F : ℂ → ℂ) (C : ℝ)
    (hF : DifferentiableOn ℂ F {z : ℂ | 0 < z.im})
    (hdecay : ∀ z : ℂ, 0 < z.im →
      ‖deriv F z‖ ≤ C / ‖z‖ ^ 2)
    (hC : 0 ≤ C)
    {x : ℝ} (hx : x ≠ 0) {u v : ℝ} (hu : 0 < u) (huv : u ≤ v) :
    ‖F ((x : ℂ) + (v : ℂ) * Complex.I) -
        F ((x : ℂ) + (u : ℂ) * Complex.I)‖ ≤
      (C / |x| ^ 2) * (v - u) := by
  have hax : 0 < |x| := abs_pos.mpr hx
  let f : ℝ → ℂ := fun t ↦ F ((x : ℂ) + (t : ℂ) * Complex.I)
  have hpath (t : ℝ) : HasDerivAt
      (fun s : ℝ ↦ (x : ℂ) + (s : ℂ) * Complex.I) Complex.I t := by
    simpa using ((hasDerivAt_id (t : ℂ)).mul_const Complex.I).comp_ofReal
  have hinside (t : ℝ) (ht : t ∈ Icc u v) :
      0 < (((x : ℂ) + (t : ℂ) * Complex.I).im) := by
    simpa using (hu.trans_le ht.1)
  have hd (t : ℝ) (ht : t ∈ Icc u v) : HasDerivAt f
      (Complex.I * deriv F ((x : ℂ) + (t : ℂ) * Complex.I)) t := by
    have hf := (hF.differentiableAt
      ((isOpen_lt continuous_const Complex.continuous_im).mem_nhds (hinside t ht))).hasDerivAt
    simpa only [f, Function.comp_def, smul_eq_mul] using hf.scomp t (hpath t)
  have hnorm_lower (t : ℝ) : |x| ≤
      ‖(x : ℂ) + (t : ℂ) * Complex.I‖ := by
    convert Complex.abs_re_le_norm ((x : ℂ) + (t : ℂ) * Complex.I) using 1 ;
      simp
  have hbound (t : ℝ) (ht : t ∈ Icc u v) :
      ‖deriv f t‖ ≤ C / |x| ^ 2 := by
    rw [(hd t ht).deriv, norm_mul, Complex.norm_I, one_mul]
    have hdec := hdecay _ (hinside t ht)
    have hnormpos : 0 < ‖(x : ℂ) + (t : ℂ) * Complex.I‖ :=
      lt_of_lt_of_le hax (hnorm_lower t)
    have hpow : |x| ^ 2 ≤ ‖(x : ℂ) + (t : ℂ) * Complex.I‖ ^ 2 := by
      exact (sq_le_sq₀ (abs_nonneg x) (norm_nonneg _)).mpr (hnorm_lower t)
    have hinv : 1 / ‖(x : ℂ) + (t : ℂ) * Complex.I‖ ^ 2 ≤
        1 / |x| ^ 2 := by
      exact one_div_le_one_div_of_le (sq_pos_of_pos hax) hpow
    calc
      ‖deriv F ((x : ℂ) + (t : ℂ) * Complex.I)‖ ≤
          C / ‖(x : ℂ) + (t : ℂ) * Complex.I‖ ^ 2 := hdec
      _ = C * (1 / ‖(x : ℂ) + (t : ℂ) * Complex.I‖ ^ 2) := by ring
      _ ≤ C * (1 / |x| ^ 2) := mul_le_mul_of_nonneg_left hinv hC
      _ = C / |x| ^ 2 := by ring
  have hcont : ContinuousOn f (Icc u v) := by
    intro t ht
    exact (hd t ht).continuousAt.continuousWithinAt
  have hdiff : DifferentiableOn ℝ f (Ioo u v) := by
    intro t ht
    exact (hd t ⟨ht.1.le, ht.2.le⟩).differentiableAt.differentiableWithinAt
  have hBi : IntervalIntegrable (fun _ : ℝ ↦ C / |x| ^ 2) MeasureTheory.volume u v :=
    intervalIntegrable_const
  have h := norm_sub_le_integral_of_norm_deriv_le_of_le huv hcont hdiff
    (Filter.Eventually.of_forall (fun t ht ↦ hbound t ⟨ht.1.le, ht.2.le⟩)) hBi
  convert h using 1; simp [intervalIntegral.integral_const]; ring

/-- The canonical four-factor square-root derivative has the required
quadratic decay outside a disk containing the four real prevertices. -/
theorem canonical_deriv_decay
    {W : ℂ → ℂ} {x : Fin 4 → ℝ} {M : ℝ}
    (hW : ∀ z : ℂ, 0 < z.im →
      (deriv W z) ^ 2 = -(∏ j : Fin 4, (z - (x j : ℂ)))⁻¹)
    (hM : ∀ j : Fin 4, ‖(x j : ℂ)‖ ≤ M)
    (_hM0 : 0 ≤ M) :
    ∀ z : ℂ, 0 < z.im → 2 * M ≤ ‖z‖ →
      ‖deriv W z‖ ≤ 4 / ‖z‖ ^ 2 := by
  intro z hz hzR
  have hz0 : 0 < ‖z‖ := lt_of_lt_of_le hz (Complex.im_le_norm z)
  have hdist (j : Fin 4) : ‖z‖ / 2 ≤ ‖z - (x j : ℂ)‖ := by
    have htri := norm_sub_norm_le z (x j : ℂ)
    have hj := hM j
    nlinarith
  have hprod : ‖z‖ ^ 4 / 16 ≤
      ‖∏ j : Fin 4, (z - (x j : ℂ))‖ := by
    have hprod' : ∏ j : Fin 4, (‖z‖ / 2) ≤
        ∏ j : Fin 4, ‖z - (x j : ℂ)‖ := by
      simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one]
      gcongr
      all_goals apply hdist
    rw [norm_prod]
    calc
      ‖z‖ ^ 4 / 16 = ∏ j : Fin 4, (‖z‖ / 2) := by
        simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one]
        ring
      _ ≤ ∏ j : Fin 4, ‖z - (x j : ℂ)‖ := hprod'
  have hprod0 : 0 < ‖∏ j : Fin 4, (z - (x j : ℂ))‖ := by
    apply norm_pos_iff.mpr
    intro hzero
    rw [Finset.prod_eq_zero_iff] at hzero
    obtain ⟨j, -, hj⟩ := hzero
    have : z = (x j : ℂ) := sub_eq_zero.mp hj
    rw [this] at hz
    simp at hz
  have hsquare : ‖deriv W z‖ ^ 2 =
      1 / ‖∏ j : Fin 4, (z - (x j : ℂ))‖ := by
    calc
      ‖deriv W z‖ ^ 2 = ‖(deriv W z) ^ 2‖ := by rw [norm_pow]
      _ = ‖(∏ j : Fin 4, (z - (x j : ℂ)))⁻¹‖ := by rw [hW z hz, norm_neg]
      _ = 1 / ‖∏ j : Fin 4, (z - (x j : ℂ))‖ := by
        rw [norm_inv, inv_eq_one_div]
  have hsq : ‖deriv W z‖ ^ 2 ≤ (4 / ‖z‖ ^ 2) ^ 2 := by
    rw [hsquare]
    have hinv : 1 / ‖∏ j : Fin 4, (z - (x j : ℂ))‖ ≤
        1 / (‖z‖ ^ 4 / 16) := by
      exact one_div_le_one_div_of_le (by positivity) hprod
    calc
      1 / ‖∏ j : Fin 4, (z - (x j : ℂ))‖ ≤ 1 / (‖z‖ ^ 4 / 16) := hinv
      _ = (4 / ‖z‖ ^ 2) ^ 2 := by field_simp; ring
  exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp hsq

/-- Horizontal path variation under the same quadratic derivative decay. -/
theorem norm_horizontal_sub_le_of_deriv_decay
    (F : ℂ → ℂ) (C : ℝ)
    (hF : DifferentiableOn ℂ F {z : ℂ | 0 < z.im})
    (hdecay : ∀ z : ℂ, 0 < z.im →
      ‖deriv F z‖ ≤ C / ‖z‖ ^ 2)
    (hC : 0 ≤ C)
    {y : ℝ} (hy : 0 < y) {u v : ℝ} (huv : u ≤ v) :
    ‖F ((v : ℂ) + (y : ℂ) * Complex.I) -
        F ((u : ℂ) + (y : ℂ) * Complex.I)‖ ≤
      (C / y ^ 2) * (v - u) := by
  let f : ℝ → ℂ := fun t ↦ F ((t : ℂ) + (y : ℂ) * Complex.I)
  have hpath (t : ℝ) : HasDerivAt
      (fun s : ℝ ↦ (s : ℂ) + (y : ℂ) * Complex.I) 1 t := by
    simpa using (hasDerivAt_id (t : ℂ)).comp_ofReal
  have hinside (t : ℝ) :
      0 < (((t : ℂ) + (y : ℂ) * Complex.I).im) := by
    simpa using hy
  have hd (t : ℝ) (ht : t ∈ Icc u v) : HasDerivAt f
      (deriv F ((t : ℂ) + (y : ℂ) * Complex.I)) t := by
    have hf := (hF.differentiableAt
      ((isOpen_lt continuous_const Complex.continuous_im).mem_nhds (hinside t))).hasDerivAt
    simpa only [f, Function.comp_def, one_mul, one_smul] using hf.scomp t (hpath t)
  have hnorm_lower (t : ℝ) : y ≤
      ‖(t : ℂ) + (y : ℂ) * Complex.I‖ := by
    convert Complex.abs_im_le_norm ((t : ℂ) + (y : ℂ) * Complex.I) using 1 ;
      simp [abs_of_pos hy]
  have hbound (t : ℝ) (ht : t ∈ Icc u v) :
      ‖deriv f t‖ ≤ C / y ^ 2 := by
    rw [(hd t ht).deriv]
    have hdec := hdecay _ (hinside t)
    have hpow : y ^ 2 ≤ ‖(t : ℂ) + (y : ℂ) * Complex.I‖ ^ 2 := by
      exact (sq_le_sq₀ (le_of_lt hy) (norm_nonneg _)).mpr (hnorm_lower t)
    have hinv : 1 / ‖(t : ℂ) + (y : ℂ) * Complex.I‖ ^ 2 ≤ 1 / y ^ 2 := by
      exact one_div_le_one_div_of_le (sq_pos_of_pos hy) hpow
    calc
      ‖deriv F ((t : ℂ) + (y : ℂ) * Complex.I)‖ ≤
          C / ‖(t : ℂ) + (y : ℂ) * Complex.I‖ ^ 2 := hdec
      _ = C * (1 / ‖(t : ℂ) + (y : ℂ) * Complex.I‖ ^ 2) := by ring
      _ ≤ C * (1 / y ^ 2) := mul_le_mul_of_nonneg_left hinv hC
      _ = C / y ^ 2 := by ring
  have hcont : ContinuousOn f (Icc u v) := by
    intro t ht
    exact (hd t ht).continuousAt.continuousWithinAt
  have hdiff : DifferentiableOn ℝ f (Ioo u v) := by
    intro t ht
    exact (hd t ⟨ht.1.le, ht.2.le⟩).differentiableAt.differentiableWithinAt
  have hBi : IntervalIntegrable (fun _ : ℝ ↦ C / y ^ 2) MeasureTheory.volume u v :=
    intervalIntegrable_const
  have h := norm_sub_le_integral_of_norm_deriv_le_of_le huv hcont hdiff
    (Filter.Eventually.of_forall (fun t ht ↦ hbound t ⟨ht.1.le, ht.2.le⟩)) hBi
  convert h using 1; simp [intervalIntegral.integral_const]; ring

open scoped ComplexConjugate

/-- The standard disk involution exchanging the origin and `a`. -/
def diskInvolution (a z : ℂ) : ℂ := (a - z) / (1 - conj a * z)

lemma diskInvolution_den {a z : ℂ} (ha : ‖a‖ < 1) (hz : ‖z‖ ≤ 1) :
    1 - conj a * z ≠ 0 := by
  have hn : ‖conj a * z‖ < 1 := by
    rw [norm_mul, Complex.norm_conj]
    exact lt_of_le_of_lt (mul_le_of_le_one_right (norm_nonneg a) hz) ha
  intro he
  have he' : conj a * z = 1 := (sub_eq_zero.mp he).symm
  simp [he'] at hn

lemma diskInvolution_norm_le {a z : ℂ} (ha : ‖a‖ < 1) (hz : ‖z‖ ≤ 1) :
    ‖diskInvolution a z‖ ≤ 1 := by
  have hi := HolomorphicAnosov.diskMobius_norm_identity a z (diskInvolution_den ha hz)
  have hnon : 0 ≤ ((1 - ‖a‖ ^ 2) * (1 - ‖z‖ ^ 2)) / ‖1 - conj a * z‖ ^ 2 := by
    apply div_nonneg _ (sq_nonneg _)
    apply mul_nonneg <;> nlinarith [norm_nonneg a, norm_nonneg z]
  have hn : ‖diskInvolution a z‖ = ‖(z - a) / (1 - conj a * z)‖ := by
    simp only [diskInvolution, norm_div, norm_sub_rev]
  rw [← hn] at hi
  nlinarith [norm_nonneg (diskInvolution a z)]

lemma diskInvolution_involutive {a z : ℂ} (ha : ‖a‖ < 1) (hz : ‖z‖ ≤ 1) :
    diskInvolution a (diskInvolution a z) = z := by
  have hd := diskInvolution_den ha hz
  have hd' := diskInvolution_den ha (diskInvolution_norm_le ha hz)
  unfold diskInvolution at hd' ⊢
  apply (div_eq_iff hd').mpr
  linear_combination -(div_mul_cancel₀ (a - z) hd)

/-- The explicit fractional disk involution is a homeomorphism of the closed disk.
The norm identity gives preservation, the denominator is separated from zero, and
applying the same formula twice gives the inverse. -/
def diskInvolutionHomeomorph (a : ℂ) (ha : ‖a‖ < 1) :
    {z : ℂ | ‖z‖ ≤ 1} ≃ₜ {z : ℂ | ‖z‖ ≤ 1} where
  toFun z := ⟨diskInvolution a z, diskInvolution_norm_le ha z.property⟩
  invFun z := ⟨diskInvolution a z, diskInvolution_norm_le ha z.property⟩
  left_inv z := Subtype.ext (diskInvolution_involutive ha z.property)
  right_inv z := Subtype.ext (diskInvolution_involutive ha z.property)
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.div
    · exact continuous_const.sub continuous_subtype_val
    · exact continuous_const.sub (continuous_const.mul continuous_subtype_val)
    · intro z
      exact diskInvolution_den ha z.property
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply Continuous.div
    · exact continuous_const.sub continuous_subtype_val
    · exact continuous_const.sub (continuous_const.mul continuous_subtype_val)
    · intro z
      exact diskInvolution_den ha z.property




/-- Rotation by a unit complex number on the actual closed disk. -/
def diskRotationHomeomorph (c : ℂ) (hc : ‖c‖ = 1) :
    {z : ℂ | ‖z‖ ≤ 1} ≃ₜ {z : ℂ | ‖z‖ ≤ 1} where
  toFun z := ⟨c * z, by simpa only [Set.mem_ofPred_eq, norm_mul, hc, one_mul] using z.property⟩
  invFun z := ⟨c⁻¹ * z, by simpa only [Set.mem_ofPred_eq, norm_mul, norm_inv, hc, inv_one, one_mul] using z.property⟩
  left_inv z := by
    apply Subtype.ext
    have hc0 : c ≠ 0 := norm_ne_zero_iff.mp (by rw [hc]; norm_num)
    simp [hc0]
  right_inv z := by
    apply Subtype.ext
    have hc0 : c ≠ 0 := norm_ne_zero_iff.mp (by rw [hc]; norm_num)
    simp [hc0]
  continuous_toFun := (continuous_const.mul continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_const.mul continuous_subtype_val).subtype_mk _

/-- The cancelled real-Möbius/Cayley expression, factored into two rotations
and a disk involution, is a homeomorphism of the closed disk. -/
def compactifiedMobius (q d e : ℂ) (hq : ‖q‖ = 1) (hde : ‖e‖ < ‖d‖) :
    {z : ℂ | ‖z‖ ≤ 1} ≃ₜ {z : ℂ | ‖z‖ ≤ 1} :=
  ((diskRotationHomeomorph q⁻¹ (by simp [hq])).trans
    (diskInvolutionHomeomorph (-conj e / conj d) (by
      simpa [norm_div, Complex.norm_conj] using
        (div_lt_one (lt_of_le_of_lt (norm_nonneg e) hde)).mpr hde))).trans
    (diskRotationHomeomorph (conj d / d) (by
      rw [norm_div, Complex.norm_conj, div_self]
      exact ne_of_gt (lt_of_le_of_lt (norm_nonneg e) hde)))

lemma compactifiedMobius_den (q d e : ℂ) (hq : ‖q‖ = 1)
    (hde : ‖e‖ < ‖d‖) {z : ℂ} (hz : ‖z‖ ≤ 1) : d*q+e*z ≠ 0 := by
  have hnorm : ‖e*z‖ < ‖d*q‖ := by
    rw [norm_mul, norm_mul, hq, mul_one]
    exact lt_of_le_of_lt (mul_le_of_le_one_right (norm_nonneg e) hz) hde
  intro h
  have heq : e*z = -(d*q) := eq_neg_of_add_eq_zero_right h
  rw [heq, norm_neg] at hnorm
  exact lt_irrefl _ hnorm

lemma compactifiedMobius_formula (q d e : ℂ) (hq : ‖q‖ = 1)
    (hde : ‖e‖ < ‖d‖) (z : {z : ℂ | ‖z‖ ≤ 1}) :
    (compactifiedMobius q d e hq hde z : ℂ) =
      (-conj e * q - conj d * z) / (d * q + e * z) := by
  have hd : d ≠ 0 := norm_ne_zero_iff.mp (ne_of_gt (lt_of_le_of_lt (norm_nonneg e) hde))
  have hq0 : q ≠ 0 := norm_ne_zero_iff.mp (by rw [hq]; norm_num)
  have hdc : conj d ≠ 0 := by simpa using hd
  change conj d / d *
    ((-conj e / conj d - q⁻¹ * z) / (1 - conj (-conj e / conj d) * (q⁻¹ * z))) = _
  simp only [map_div₀, map_neg, Complex.conj_conj]
  have hnorm : ‖e * (z : ℂ)‖ < ‖d * q‖ := by
    rw [norm_mul, norm_mul, hq, mul_one]
    exact lt_of_le_of_lt (mul_le_of_le_one_right (norm_nonneg e) z.property) hde
  have hden : d * q + e * (z : ℂ) ≠ 0 := by
    intro h
    have heq : e * (z : ℂ) = -(d*q) := eq_neg_of_add_eq_zero_right h
    rw [heq, norm_neg] at hnorm
    exact lt_irrefl _ hnorm
  have hden' : 1 - -e / d * (q⁻¹ * (z : ℂ)) ≠ 0 := by
    intro he
    apply hden
    have he' := congrArg (fun w : ℂ ↦ w * d * q) he
    field_simp [hd, hq0] at he'
    linear_combination he'
  simp only [neg_div, neg_mul, sub_neg_eq_add]
  field_simp [hd, hdc, hq0, hden]


/-- Positivity of the real Möbius determinant is precisely the coefficient norm
inequality required by the disk compactification. -/
lemma realMobius_coefficient_norm (A B C D : ℝ) (hdet : 0 < A * D - B * C) :
    ‖((-B-C : ℝ) : ℂ) + ((A-D : ℝ) : ℂ) * Complex.I‖ <
      ‖((B-C : ℝ) : ℂ) + ((A+D : ℝ) : ℂ) * Complex.I‖ := by
  have hs : ‖((B-C : ℝ) : ℂ) + ((A+D : ℝ) : ℂ) * Complex.I‖ ^ 2 -
      ‖((-B-C : ℝ) : ℂ) + ((A-D : ℝ) : ℂ) * Complex.I‖ ^ 2 =
        4 * (A*D-B*C) := by
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.add_im,
      Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im]
    ring
  nlinarith [norm_nonneg (((B-C : ℝ) : ℂ) + ((A+D : ℝ) : ℂ) * Complex.I),
    norm_nonneg (((-B-C : ℝ) : ℂ) + ((A-D : ℝ) : ℂ) * Complex.I)]

/-- The real normalization, composed with both Cayley maps, on the closed disk. -/
def realMobiusDiskHomeomorph (q : ℂ) (hq : ‖q‖ = 1)
    (A B C D : ℝ) (hdet : 0 < A * D - B * C) :
    {z : ℂ | ‖z‖ ≤ 1} ≃ₜ {z : ℂ | ‖z‖ ≤ 1} :=
  compactifiedMobius q (((B-C : ℝ) : ℂ) + ((A+D : ℝ) : ℂ) * Complex.I)
    (((-B-C : ℝ) : ℂ) + ((A-D : ℝ) : ℂ) * Complex.I) hq
    (realMobius_coefficient_norm A B C D hdet)


lemma realMobiusDiskHomeomorph_at_real (q : ℂ) (hq : ‖q‖ = 1)
    (A B C D : ℝ) (hdet : 0 < A*D-B*C)
    (z : {z : ℂ | ‖z‖ ≤ 1}) (t y : ℝ) (hqz : q-(z : ℂ) ≠ 0)
    (ht : Complex.I*(q+z)/(q-z) = (t : ℂ))
    (hy : A*t+B = y*(C*t+D)) :
    (realMobiusDiskHomeomorph q hq A B C D hdet z : ℂ) =
      ((y : ℂ)-Complex.I)/((y : ℂ)+Complex.I) := by
  let d : ℂ := ((B-C : ℝ) : ℂ) + ((A+D : ℝ) : ℂ)*Complex.I
  let e : ℂ := ((-B-C : ℝ) : ℂ) + ((A-D : ℝ) : ℂ)*Complex.I
  have hde : ‖e‖ < ‖d‖ := realMobius_coefficient_norm A B C D hdet
  have hform : (realMobiusDiskHomeomorph q hq A B C D hdet z : ℂ) =
      (-conj e*q-conj d*z)/(d*q+e*z) := compactifiedMobius_formula q d e hq hde z
  have hden := compactifiedMobius_den q d e hq hde z.property
  have hyi : (y : ℂ)+Complex.I ≠ 0 := by
    intro h
    have hi := congrArg Complex.im h
    simp at hi
  rw [hform]
  apply (div_eq_div_iff hden hyi).mpr
  have ht' := (div_eq_iff hqz).mp ht
  have hy' : (A : ℂ)*t+B = (y : ℂ)*((C : ℂ)*t+D) := by exact_mod_cast hy
  dsimp [d,e]
  simp only [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  linear_combination 2*Complex.I*(q-(z : ℂ))*hy' +
    2*((A : ℂ)-(y : ℂ)*C)*Complex.I*ht' +
    2*(C : ℂ)*(q+(z : ℂ))*(y : ℂ)*Complex.I_sq



open Filter
open scoped _root_.Topology

def inverseCayley (w : ℂ) : ℂ := (w-Complex.I)/(w+Complex.I)

lemma inverseCayley_den {w : ℂ} (hw : 0 ≤ w.im) : w+Complex.I ≠ 0 := by
  intro h
  have hi := congrArg Complex.im h
  simp at hi
  linarith

lemma inverseCayley_norm_le {w : ℂ} (hw : 0 ≤ w.im) : ‖inverseCayley w‖ ≤ 1 := by
  rw [inverseCayley, norm_div, div_le_one (norm_pos_iff.mpr (inverseCayley_den hw))]
  have hs : ‖w+Complex.I‖^2-‖w-Complex.I‖^2 = 4*w.im := by
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.add_im,
      Complex.sub_re, Complex.sub_im, Complex.I_re, Complex.I_im]
    ring
  nlinarith [norm_nonneg (w+Complex.I), norm_nonneg (w-Complex.I)]

lemma inverseCayley_norm_lt {w : ℂ} (hw : 0 < w.im) : ‖inverseCayley w‖ < 1 := by
  rw [inverseCayley, norm_div, div_lt_one (norm_pos_iff.mpr (inverseCayley_den hw.le))]
  have hs : ‖w+Complex.I‖^2-‖w-Complex.I‖^2 = 4*w.im := by
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.add_im,
      Complex.sub_re, Complex.sub_im, Complex.I_re, Complex.I_im]
    ring
  nlinarith [norm_nonneg (w+Complex.I), norm_nonneg (w-Complex.I)]

lemma inverseCayley_continuousOn : ContinuousOn inverseCayley {w : ℂ | 0 ≤ w.im} := by
  exact (continuous_id.sub continuous_const).continuousOn.div
    (continuous_id.add continuous_const).continuousOn (fun w hw ↦ inverseCayley_den hw)

lemma cayley_inverseCayley {w : ℂ} (hw : 0 ≤ w.im) :
    Complex.I*(1+inverseCayley w)/(1-inverseCayley w) = w := by
  have hd := inverseCayley_den hw
  have hne : 1-inverseCayley w ≠ 0 := by
    intro he
    have hh : w-Complex.I = w+Complex.I := by
      have hi : inverseCayley w = 1 := (sub_eq_zero.mp he).symm
      simpa [inverseCayley] using (div_eq_iff hd).mp hi
    have hi := congrArg Complex.im hh
    simp at hi
    linarith
  apply (div_eq_iff hne).mpr
  have he := div_mul_cancel₀ (w-Complex.I) hd
  change (inverseCayley w)*(w+Complex.I) = w-Complex.I at he
  linear_combination he

/-- Two continuous boundary extensions of the same Cayley pullback agree at
all finite points of the closed upper half plane, by density of its interior. -/
lemma inverseCayley_boundary_agreement {W Wbar Fbar : ℂ → ℂ}
    (hWbarEq : EqOn Wbar W {w : ℂ | 0 < w.im})
    (hWbarCont : ContinuousOn Wbar {w : ℂ | 0 ≤ w.im})
    (hFbarEq : EqOn Fbar (fun z ↦ W (Complex.I*(1+z)/(1-z))) {z : ℂ | ‖z‖ < 1})
    (hFbarCont : ContinuousOn Fbar {z : ℂ | ‖z‖ ≤ 1}) :
    EqOn (fun w ↦ Fbar (inverseCayley w)) Wbar {w : ℂ | 0 ≤ w.im} := by
  have heq : EqOn (fun w ↦ Fbar (inverseCayley w)) Wbar {w : ℂ | 0 < w.im} := by
    intro w hw
    change Fbar (inverseCayley w) = Wbar w
    calc
      Fbar (inverseCayley w) = W (Complex.I*(1+inverseCayley w)/(1-inverseCayley w)) :=
        hFbarEq (inverseCayley_norm_lt hw)
      _ = W w := congrArg W (cayley_inverseCayley hw.le)
      _ = Wbar w := (hWbarEq hw).symm
  have hc : ContinuousOn (fun w ↦ Fbar (inverseCayley w)) {w : ℂ | 0 ≤ w.im} :=
    hFbarCont.comp inverseCayley_continuousOn (fun w hw ↦ inverseCayley_norm_le hw)
  apply heq.of_subset_closure hc hWbarCont
  · intro w hw
    exact (show 0 < w.im from hw).le
  · rw [Complex.closure_setOfPred_lt_im]


lemma cayley_boundary_value_at_one {W Wbar Fbar : ℂ → ℂ} {L : ℂ}
    (hWbarEq : EqOn Wbar W {w : ℂ | 0 < w.im})
    (hWbarCont : ContinuousOn Wbar {w : ℂ | 0 ≤ w.im})
    (hFbarEq : EqOn Fbar (fun z ↦ W (Complex.I*(1+z)/(1-z))) {z : ℂ | ‖z‖ < 1})
    (hFbarCont : ContinuousOn Fbar {z : ℂ | ‖z‖ ≤ 1})
    (htop : Tendsto (fun t : ℝ ↦ Wbar (t : ℂ)) atTop (𝓝 L)) : Fbar 1 = L := by
  have hagree := inverseCayley_boundary_agreement hWbarEq hWbarCont hFbarEq hFbarCont
  have hNtop : Tendsto (fun t : ℝ ↦ inverseCayley (t : ℂ)) atTop (𝓝 (1 : ℂ)) := by
    exact HolomorphicAnosov.Analysis.MarkedRectangle.inverseCayley_real_tendsto_one
      tendsto_inv_atTop_zero (eventually_ne_atTop 0)
  have hNwithin : Tendsto (fun t : ℝ ↦ inverseCayley (t : ℂ)) atTop
      (𝓝[{z : ℂ | ‖z‖ ≤ 1}] (1 : ℂ)) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hNtop
      (Filter.Eventually.of_forall (fun t ↦ inverseCayley_norm_le (by simp)))
  have hlim := (hFbarCont (1 : ℂ) (by simp)).tendsto.comp hNwithin
  have heq : (fun t : ℝ ↦ Fbar (inverseCayley (t : ℂ))) =
      (fun t : ℝ ↦ Wbar (t : ℂ)) := by
    funext t
    exact hagree (by simp)
  change Tendsto (fun t : ℝ ↦ Fbar (inverseCayley (t : ℂ))) atTop (𝓝 (Fbar 1)) at hlim
  rw [heq] at hlim
  exact tendsto_nhds_unique hlim htop


lemma diskCayley_im (z : ℂ) :
    (Complex.I*(1+z)/(1-z)).im = (1-‖z‖^2)/‖1-z‖^2 := by
  simp only [Complex.div_im, Complex.mul_im, Complex.mul_re, Complex.add_re,
    Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.I_re, Complex.I_im,
    Complex.one_re, Complex.one_im, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  ring

lemma inverseCayley_diskCayley {z : ℂ} (hz : z ≠ 1) :
    inverseCayley (Complex.I*(1+z)/(1-z)) = z := by
  have hd : 1-z ≠ 0 := sub_ne_zero.mpr hz.symm
  have hi : Complex.I*(1+z)/(1-z)+Complex.I ≠ 0 := by
    have he : Complex.I*(1+z)/(1-z)+Complex.I = 2*Complex.I/(1-z) := by
      apply (eq_div_iff hd).mpr
      have hc := div_mul_cancel₀ (Complex.I*(1+z)) hd
      linear_combination hc
    rw [he]
    exact div_ne_zero (mul_ne_zero (by norm_num) Complex.I_ne_zero) hd
  unfold inverseCayley
  apply (div_eq_iff hi).mpr
  have hc := div_mul_cancel₀ (Complex.I*(1+z)) hd
  linear_combination hc

/-- The punctured unit circle is exactly the inverse-Cayley image of the real line. -/
lemma unit_circle_inverseCayley {z : ℂ} (hz : ‖z‖ = 1) (hz1 : z ≠ 1) :
    ∃ t : ℝ, inverseCayley (t : ℂ) = z := by
  let w := Complex.I*(1+z)/(1-z)
  have hw : w.im = 0 := by
    dsimp [w]
    rw [diskCayley_im, hz]
    norm_num
  refine ⟨w.re, ?_⟩
  have he : (w.re : ℂ) = w := by
    apply Complex.ext <;> simp [hw]
  rw [he]
  exact inverseCayley_diskCayley hz1


lemma cayley_pullback_regular {W Fbar : ℂ → ℂ}
    (hW : ∀ w : ℂ, 0 < w.im → DifferentiableAt ℂ W w ∧ deriv W w ≠ 0)
    (hFbarEq : EqOn Fbar (fun z ↦ W (Complex.I*(1+z)/(1-z))) {z : ℂ | ‖z‖ < 1}) :
    DifferentiableOn ℂ Fbar (Metric.ball (0 : ℂ) 1) ∧
      ∀ z ∈ Metric.ball (0 : ℂ) 1, deriv Fbar z ≠ 0 := by
  have hder (z : ℂ) (hz : ‖z‖ < 1) :
      HasDerivAt Fbar
        (deriv W (Complex.I*(1+z)/(1-z)) * (2*Complex.I/(1-z)^2)) z := by
    have hz1 : z ≠ 1 := by intro he; simp [he] at hz
    have hcz : 0 < (Complex.I*(1+z)/(1-z)).im := by
      rw [diskCayley_im]
      apply div_pos
      · nlinarith [norm_nonneg z]
      · exact sq_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hz1.symm))
    have hc : HasDerivAt (fun w : ℂ ↦ Complex.I*(1+w)/(1-w))
        (2*Complex.I/(1-z)^2) z := by
      have h := ((hasDerivAt_const z Complex.I).mul
        ((hasDerivAt_const z 1).add (hasDerivAt_id z))).div
          ((hasDerivAt_const z 1).sub (hasDerivAt_id z)) (sub_ne_zero.mpr hz1.symm)
      convert h using 1
      · rfl
      · dsimp only [Pi.mul_apply, Pi.add_apply, Pi.sub_apply, id_eq]
        ring
    exact ((hW _ hcz).1.hasDerivAt.comp z hc).congr_of_eventuallyEq
      (hFbarEq.eventuallyEq_of_mem ((isOpen_lt continuous_norm continuous_const).mem_nhds hz))
  constructor
  · intro z hz
    exact (hder z (by simpa using hz)).differentiableAt.differentiableWithinAt
  · intro z hz
    have hz' : ‖z‖ < 1 := by simpa using hz
    rw [(hder z hz').deriv]
    apply mul_ne_zero
    · apply (hW _ ?_).2
      rw [diskCayley_im]
      apply div_pos
      · nlinarith [norm_nonneg z]
      · apply sq_pos_of_pos
        apply norm_pos_iff.mpr
        intro he
        have hz1 := sub_eq_zero.mp he
        simp [← hz1] at hz'
    · apply div_ne_zero
      · exact mul_ne_zero (by norm_num) Complex.I_ne_zero
      · apply pow_ne_zero
        intro he
        have hz1 := sub_eq_zero.mp he
        simp [← hz1] at hz'



/-- A holomorphic bijection of open planar sets has a holomorphic ambient inverse
on its target, with both literal inverse identities. -/
lemma holomorphic_bijOn_inverse {D Q : Set ℂ} (hD : IsOpen D) (hQ : IsOpen Q)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f D) (hb : BijOn f D Q) :
    ∃ g : ℂ → ℂ, DifferentiableOn ℂ g Q ∧ MapsTo g Q D ∧
      (∀ z ∈ D, g (f z) = z) ∧ (∀ w ∈ Q, f (g w) = w) := by
  obtain ⟨e,he⟩ := HolomorphicAnosov.Analysis.exists_homeomorph_eq_holomorphic_bijOn hD hf hb
  let p := hb.toPartialEquiv f D Q
  have heq : p.source.domRestrict p = (Subtype.val : Q → ℂ) ∘ e := by
    funext x
    exact (he x).symm
  have hop : IsOpenMap (p.source.domRestrict p) := by
    rw [heq]
    exact hQ.isOpenEmbedding_subtypeVal.isOpenMap.comp e.isOpenMap
  let E := OpenPartialHomeomorph.ofContinuousOpenRestrict p hf.continuousOn hop hD
  refine ⟨E.symm,?_,(fun _ hw ↦ E.map_target hw),
    (fun _ hz ↦ E.left_inv hz),(fun _ hw ↦ E.right_inv hw)⟩
  intro w hw
  exact (HolomorphicAnosov.Analysis.Complex.coordinateInverseDeriv E hf hw).2.differentiableAt.differentiableWithinAt

lemma closure_open_raw_rectangle {r₀ r₁ y₀ y₁ : ℝ} (hr : r₀ < r₁) (hy : y₀ < y₁) :
    closure (Complex.reProdIm (Ioo r₀ r₁) (Ioo y₀ y₁)) =
      Complex.reProdIm (Icc r₀ r₁) (Icc y₀ y₁) := by
  change closure (Complex.equivRealProdCLM.toHomeomorph ⁻¹' (Ioo r₀ r₁ ×ˢ Ioo y₀ y₁)) =
    Complex.equivRealProdCLM.toHomeomorph ⁻¹' (Icc r₀ r₁ ×ˢ Icc y₀ y₁)
  rw [← Complex.equivRealProdCLM.toHomeomorph.preimage_closure,
    closure_prod_eq,closure_Ioo hr.ne,closure_Ioo hy.ne]

/-- Translation of a closed coordinate rectangle to its origin-based rectangle. -/
def rawRectangleTranslation (r₀ r₁ y₀ y₁ : ℝ) :
    Complex.reProdIm (Icc r₀ r₁) (Icc y₀ y₁) ≃ₜ
      Complex.reProdIm (Icc 0 (r₁-r₀)) (Icc 0 (y₁-y₀)) where
  toFun z := ⟨(z:ℂ)-((r₀:ℂ)+(y₀:ℂ)*Complex.I),by
    rcases z.property with ⟨⟨ha,hb⟩,⟨hc,hd⟩⟩
    change (0 ≤ _ ∧ _ ≤ r₁-r₀) ∧ (0 ≤ _ ∧ _ ≤ y₁-y₀)
    simp only [Complex.sub_re,Complex.sub_im,Complex.add_re,Complex.add_im,
      Complex.ofReal_re,Complex.ofReal_im,Complex.mul_re,Complex.mul_im,
      Complex.I_re,Complex.I_im,mul_zero,mul_one,sub_zero,add_zero,zero_add]
    exact ⟨⟨by linarith,by linarith⟩,⟨by linarith,by linarith⟩⟩⟩
  invFun z := ⟨(z:ℂ)+((r₀:ℂ)+(y₀:ℂ)*Complex.I),by
    rcases z.property with ⟨⟨ha,hb⟩,⟨hc,hd⟩⟩
    change (r₀ ≤ _ ∧ _ ≤ r₁) ∧ (y₀ ≤ _ ∧ _ ≤ y₁)
    simp only [Complex.add_re,Complex.add_im,
      Complex.ofReal_re,Complex.ofReal_im,Complex.mul_re,Complex.mul_im,
      Complex.I_re,Complex.I_im,mul_zero,mul_one,sub_zero,add_zero,zero_add]
    exact ⟨⟨by linarith,by linarith⟩,⟨by linarith,by linarith⟩⟩⟩
  left_inv z := by apply Subtype.ext; simp
  right_inv z := by apply Subtype.ext; simp
  continuous_toFun := (continuous_subtype_val.sub continuous_const).subtype_mk _
  continuous_invFun := (continuous_subtype_val.add continuous_const).subtype_mk _


lemma diskInvolution_norm_lt {a z : ℂ} (ha : ‖a‖ < 1) (hz : ‖z‖ < 1) :
    ‖diskInvolution a z‖ < 1 := by
  have hi := HolomorphicAnosov.diskMobius_norm_identity a z (diskInvolution_den ha hz.le)
  have hpos : 0 < ((1-‖a‖^2)*(1-‖z‖^2))/‖1-conj a*z‖^2 := by
    apply div_pos
    · apply mul_pos <;> nlinarith [norm_nonneg a,norm_nonneg z]
    · exact sq_pos_of_pos (norm_pos_iff.mpr (diskInvolution_den ha hz.le))
  have hn : ‖diskInvolution a z‖ = ‖(z-a)/(1-conj a*z)‖ := by
    simp only [diskInvolution,norm_div,norm_sub_rev]
  rw [← hn] at hi
  nlinarith [norm_nonneg (diskInvolution a z)]

lemma compactifiedMobius_norm_lt_iff (q d e : ℂ) (hq : ‖q‖ = 1)
    (hde : ‖e‖ < ‖d‖) (z : {z : ℂ | ‖z‖ ≤ 1}) :
    ‖(compactifiedMobius q d e hq hde z : ℂ)‖ < 1 ↔ ‖(z : ℂ)‖ < 1 := by
  have hd : 0 < ‖d‖ := lt_of_le_of_lt (norm_nonneg e) hde
  have ha : ‖-conj e / conj d‖ < 1 := by
    simpa [norm_div,Complex.norm_conj] using (div_lt_one hd).mpr hde
  change ‖conj d/d * diskInvolution (-conj e/conj d) (q⁻¹*(z:ℂ))‖ < 1 ↔ _
  simp only [norm_mul, norm_div,Complex.norm_conj,div_self hd.ne',one_mul]
  constructor
  · intro h
    have h' := diskInvolution_norm_lt ha h
    rw [diskInvolution_involutive ha (by simpa only [norm_mul,norm_inv,hq,inv_one,one_mul] using (show ‖(z : ℂ)‖ ≤ 1 from z.property))] at h'
    simpa [norm_mul,norm_inv,hq] using h'
  · intro h
    apply diskInvolution_norm_lt ha
    simpa [norm_mul,norm_inv,hq] using h

lemma compactifiedMobius_holomorphic_bijOn (q d e : ℂ) (hq : ‖q‖ = 1)
    (hde : ‖e‖ < ‖d‖) :
    let j := fun z : ℂ ↦ (-conj e*q-conj d*z)/(d*q+e*z)
    DifferentiableOn ℂ j (Metric.ball (0 : ℂ) 1) ∧
      Set.BijOn j (Metric.ball (0 : ℂ) 1) (Metric.ball (0 : ℂ) 1) := by
  dsimp only
  have hval := compactifiedMobius_formula q d e hq hde
  have hiff := compactifiedMobius_norm_lt_iff q d e hq hde
  refine ⟨?_,?_,?_,?_⟩
  · intro z hz
    apply DifferentiableAt.differentiableWithinAt
    apply DifferentiableAt.div
    · fun_prop
    · fun_prop
    · exact compactifiedMobius_den q d e hq hde (le_of_lt (by simpa using hz))
  · intro z hz
    have hz' : ‖z‖ < 1 := by simpa using hz
    have hh := (hiff ⟨z,hz'.le⟩).mpr hz'
    rw [hval] at hh
    simpa using hh
  · intro z hz w hw heq
    have hz' : ‖z‖ ≤ 1 := le_of_lt (by simpa using hz)
    have hw' : ‖w‖ ≤ 1 := le_of_lt (by simpa using hw)
    have hh : compactifiedMobius q d e hq hde ⟨z,hz'⟩ =
        compactifiedMobius q d e hq hde ⟨w,hw'⟩ := by
      apply Subtype.ext
      simpa only [hval] using heq
    exact congrArg Subtype.val ((compactifiedMobius q d e hq hde).injective hh)
  · intro w hw
    have hw' : ‖w‖ < 1 := by simpa using hw
    let z := (compactifiedMobius q d e hq hde).symm ⟨w,hw'.le⟩
    have hz : ‖(z:ℂ)‖ < 1 := (hiff z).mp (by
      simp only [z, Homeomorph.apply_symm_apply]
      exact hw')
    refine ⟨z,by simpa using hz,?_⟩
    dsimp only
    rw [← hval]
    exact congrArg Subtype.val ((compactifiedMobius q d e hq hde).apply_symm_apply ⟨w,hw'.le⟩)


/-- Any short pair of angular lifts gives exactly the directed closed arc. -/
lemma positiveClosedCircleArc_eq_image_of_lifts {α β : ℝ} (hab : α < β)
    (hshort : β < α+2*Real.pi) :
    PositiveClosedCircleArc (circleMap 0 1 α) (circleMap 0 1 β) =
      circleMap 0 1 '' Icc α β := by
  have hc (t : ℝ) : (Circle.exp t : ℂ) = circleMap 0 1 t := by
    simp [circleMap,Circle.coe_exp]
  ext z
  constructor
  · rintro ⟨a,b,hab',hshort',ha,hb,t,ht,rfl⟩
    have he := exp_short_image_eq hab' hshort' hab hshort
      (Subtype.ext (by simpa only [hc] using ha))
      (Subtype.ext (by simpa only [hc] using hb))
    have hmem : Circle.exp t ∈ Circle.exp '' Icc α β := he ▸ mem_image_of_mem _ ht
    obtain ⟨v,hv,heq⟩ := hmem
    refine ⟨v,hv,?_⟩
    simpa only [hc] using congrArg (fun w : Circle ↦ (w:ℂ)) heq
  · intro hz
    exact ⟨α,β,hab,hshort,rfl,rfl,hz⟩

/-- Adjacent positively ordered marks admit a short angular parameter interval
whose interior contains no mark, including the last interval across the cut. -/
lemma cyclic_adjacent_interval {ζ : Fin 4 → ℂ} (hcyclic : PositiveCircleCyclicOrder ζ)
    (i : Fin 4) : ∃ α β : ℝ, α < β ∧ β < α+2*Real.pi ∧
      circleMap 0 1 α = ζ i ∧ circleMap 0 1 β = ζ (i+1) ∧
      (∀ t ∈ Ioo α β, ∀ j, circleMap 0 1 t ≠ ζ j) := by
  obtain ⟨θ,hθ,hspan,hζ⟩ := hcyclic
  have h01 := hθ (by decide : (0:Fin 4)<1)
  have h12 := hθ (by decide : (1:Fin 4)<2)
  have h23 := hθ (by decide : (2:Fin 4)<3)
  have hmem (j : Fin 4) : θ j ∈ Ico (θ 0) (θ 0+2*Real.pi) :=
    ⟨hθ.monotone (Fin.zero_le j),lt_of_le_of_lt (hθ.monotone (Fin.le_last j)) hspan⟩
  have hinj := injOn_circleMap_of_abs_sub_le' (c := (0:ℂ)) (R := 1)
    (a := θ 0) (b := θ 0+2*Real.pi) (by norm_num) (by linarith)
  have hdistinct (t : ℝ) (ht : t ∈ Ico (θ 0) (θ 0+2*Real.pi))
      (hnt : ∀ j, t ≠ θ j) (j : Fin 4) : circleMap 0 1 t ≠ ζ j := by
    intro heq
    exact hnt j (hinj ht (hmem j) (heq.trans (hζ j).symm))
  fin_cases i
  · refine ⟨θ 0,θ 1,h01,by linarith,hζ 0,hζ 1,?_⟩
    intro t ht
    apply hdistinct t ⟨ht.1.le,by linarith [ht.2]⟩
    intro j
    fin_cases j <;> dsimp <;> linarith [ht.1,ht.2]
  · refine ⟨θ 1,θ 2,h12,by linarith,hζ 1,hζ 2,?_⟩
    intro t ht
    apply hdistinct t ⟨by linarith [ht.1],by linarith [ht.2]⟩
    intro j
    fin_cases j <;> dsimp <;> linarith [ht.1,ht.2]
  · refine ⟨θ 2,θ 3,h23,by linarith,hζ 2,hζ 3,?_⟩
    intro t ht
    apply hdistinct t ⟨by linarith [ht.1],by linarith [ht.2]⟩
    intro j
    fin_cases j <;> dsimp <;> linarith [ht.1,ht.2]
  · refine ⟨θ 3,θ 0+2*Real.pi,hspan,by linarith,hζ 3,?_,?_⟩
    · change circleMap 0 1 (θ 0+2*Real.pi) = ζ 0
      rw [periodic_circleMap]
      exact hζ 0
    · intro t ht
      apply hdistinct t ⟨by linarith [ht.1],ht.2⟩
      intro j
      fin_cases j <;> dsimp <;> linarith [ht.1,ht.2]

/-- A continuous rectangle-boundary path avoiding every corner in its parameter
interior stays on one supporting line. Separate the two vertical lines from the
two horizontal lines, whose intersection consists of the excluded corners, then
separate the two parallel lines; continuity includes both endpoints. -/
lemma rectangle_boundary_path_on_line {a b α β : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hαβ : α < β) (g : ℝ → ℂ) (hg : ContinuousOn g (Icc α β))
    (hboundary : ∀ t ∈ Ioo α β, (g t).re = 0 ∨ (g t).re = a ∨
      (g t).im = 0 ∨ (g t).im = b)
    (hcorners : ∀ t ∈ Ioo α β,
      ¬ (((g t).re = 0 ∨ (g t).re = a) ∧ ((g t).im = 0 ∨ (g t).im = b))) :
    EqOn (fun t ↦ (g t).re) (fun _ ↦ 0) (Icc α β) ∨
    EqOn (fun t ↦ (g t).re) (fun _ ↦ a) (Icc α β) ∨
    EqOn (fun t ↦ (g t).im) (fun _ ↦ 0) (Icc α β) ∨
    EqOn (fun t ↦ (g t).im) (fun _ ↦ b) (Icc α β) := by
  let s := g '' Ioo α β
  have hs : IsPreconnected s := isPreconnected_Ioo.image g (hg.mono Ioo_subset_Icc_self)
  have hsep {u v : Set ℂ} (hu : IsClosed u) (hv : IsClosed v)
      (hcover : s ⊆ u ∪ v) (hdis : ∀ z ∈ s, ¬ (z ∈ u ∧ z ∈ v)) :
      s ⊆ u ∨ s ⊆ v := by
    exact isPreconnected_iff_subset_of_disjoint_closed.mp hs u v hu hv hcover
      (by ext z; exact ⟨fun hz ↦ (hdis z hz.1 hz.2).elim,fun hz ↦ hz.elim⟩)
  have hr0 : IsClosed {z : ℂ | z.re = 0} := isClosed_eq Complex.continuous_re continuous_const
  have hra : IsClosed {z : ℂ | z.re = a} := isClosed_eq Complex.continuous_re continuous_const
  have hi0 : IsClosed {z : ℂ | z.im = 0} := isClosed_eq Complex.continuous_im continuous_const
  have hib : IsClosed {z : ℂ | z.im = b} := isClosed_eq Complex.continuous_im continuous_const
  have hcover : s ⊆ ({z : ℂ | z.re = 0} ∪ {z : ℂ | z.re = a}) ∪
      ({z : ℂ | z.im = 0} ∪ {z : ℂ | z.im = b}) := by
    rintro z ⟨t,ht,rfl⟩
    simpa only [mem_union,mem_ofPred_eq,or_assoc] using hboundary t ht
  have hdis : ∀ z ∈ s, ¬ (z ∈ ({z : ℂ | z.re = 0} ∪ {z : ℂ | z.re = a}) ∧
      z ∈ ({z : ℂ | z.im = 0} ∪ {z : ℂ | z.im = b})) := by
    rintro z ⟨t,ht,rfl⟩
    exact hcorners t ht
  have hext {f : ℂ → ℝ} (hf : Continuous f) {c : ℝ}
      (hh : s ⊆ {z | f z = c}) : EqOn (fun t ↦ f (g t)) (fun _ ↦ c) (Icc α β) := by
    exact (show EqOn (fun t ↦ f (g t)) (fun _ ↦ c) (Ioo α β) from
      fun t ht ↦ hh ⟨t,ht,rfl⟩).of_subset_closure (hf.comp_continuousOn hg)
        continuousOn_const Ioo_subset_Icc_self (by rw [closure_Ioo hαβ.ne])
  rcases hsep (hr0.union hra) (hi0.union hib) hcover hdis with hv | hh
  · rcases hsep hr0 hra hv (by
      intro z hz h
      exact ha.ne' (h.2.symm.trans h.1)) with hl | hr
    · exact Or.inl (hext Complex.continuous_re hl)
    · exact Or.inr (Or.inl (hext Complex.continuous_re hr))
  · rcases hsep hi0 hib hh (by
      intro z hz h
      exact hb.ne' (h.2.symm.trans h.1)) with hl | hr
    · exact Or.inr (Or.inr (Or.inl (hext Complex.continuous_im hl)))
    · exact Or.inr (Or.inr (Or.inr (hext Complex.continuous_im hr)))

lemma rectangle_boundary_path_image {a b α β : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hαβ : α < β) (g : ℝ → ℂ) (hg : ContinuousOn g (Icc α β))
    (hclosed : ∀ t ∈ Icc α β, g t ∈ ClosedRectangle a b)
    (hboundary : ∀ t ∈ Ioo α β, (g t).re = 0 ∨ (g t).re = a ∨
      (g t).im = 0 ∨ (g t).im = b)
    (hcorners : ∀ t ∈ Ioo α β,
      ¬ (((g t).re = 0 ∨ (g t).re = a) ∧ ((g t).im = 0 ∨ (g t).im = b)))
    (i : Fin 4) (hleft : g α = RectangleCorner a b i)
    (hright : g β = RectangleCorner a b (i+1)) :
    g '' Icc α β = ClosedRectangleSide a b i := by
  have hlines := rectangle_boundary_path_on_line ha hb hαβ g hg hboundary hcorners
  have hα : α ∈ Icc α β := ⟨le_rfl,hαβ.le⟩
  have hβ : β ∈ Icc α β := ⟨hαβ.le,le_rfl⟩
  have hre : IsPreconnected ((fun t ↦ (g t).re) '' Icc α β) :=
    isPreconnected_Icc.image _ (Complex.continuous_re.comp_continuousOn hg)
  have him : IsPreconnected ((fun t ↦ (g t).im) '' Icc α β) :=
    isPreconnected_Icc.image _ (Complex.continuous_im.comp_continuousOn hg)
  have hrea := mem_image_of_mem (fun t ↦ (g t).re) hα
  have hreb := mem_image_of_mem (fun t ↦ (g t).re) hβ
  have hima := mem_image_of_mem (fun t ↦ (g t).im) hα
  have himb := mem_image_of_mem (fun t ↦ (g t).im) hβ
  rw [hleft] at hrea hima
  rw [hright] at hreb himb
  fin_cases i
  all_goals norm_num [RectangleCorner] at hleft hright hrea hreb hima himb ⊢
  · have hline : EqOn (fun t ↦ (g t).im) (fun _ ↦ 0) (Icc α β) := by
      rcases hlines with h | h | h | h
      · have := h hβ; simp [hright,ha.ne'] at this
      · have := h hα; simp [hleft,ha.ne] at this
      · exact h
      · have := h hα; simp [hleft,hb.ne] at this
    apply subset_antisymm
    · rintro z ⟨t,ht,rfl⟩
      exact ⟨(hclosed t ht).1,hline ht⟩
    · intro z hz
      obtain ⟨t,ht,heq⟩ := hre.Icc_subset hrea hreb hz.1
      refine ⟨t,ht,Complex.ext heq ?_⟩
      exact (hline ht).trans hz.2.symm
  · have hline : EqOn (fun t ↦ (g t).re) (fun _ ↦ a) (Icc α β) := by
      rcases hlines with h | h | h | h
      · have := h hα; simp [hleft,ha.ne'] at this
      · exact h
      · have := h hβ; simp [hright,hb.ne'] at this
      · have := h hα; simp [hleft,hb.ne] at this
    apply subset_antisymm
    · rintro z ⟨t,ht,rfl⟩
      exact ⟨hline ht,(hclosed t ht).2⟩
    · intro z hz
      obtain ⟨t,ht,heq⟩ := him.Icc_subset hima himb hz.2
      exact ⟨t,ht,Complex.ext ((hline ht).trans hz.1.symm) heq⟩
  · have hline : EqOn (fun t ↦ (g t).im) (fun _ ↦ b) (Icc α β) := by
      rcases hlines with h | h | h | h
      · have := h hα; simp [hleft,ha.ne'] at this
      · have := h hβ; simp [hright,ha.ne] at this
      · have := h hα; simp [hleft,hb.ne'] at this
      · exact h
    apply subset_antisymm
    · rintro z ⟨t,ht,rfl⟩
      exact ⟨(hclosed t ht).1,hline ht⟩
    · intro z hz
      obtain ⟨t,ht,heq⟩ := hre.Icc_subset hreb hrea hz.1
      exact ⟨t,ht,Complex.ext heq ((hline ht).trans hz.2.symm)⟩
  · have hline : EqOn (fun t ↦ (g t).re) (fun _ ↦ 0) (Icc α β) := by
      rcases hlines with h | h | h | h
      · exact h
      · have := h hα; simp [hleft,ha.ne] at this
      · have := h hα; simp [hleft,hb.ne'] at this
      · have := h hβ; simp [hright,hb.ne] at this
    apply subset_antisymm
    · rintro z ⟨t,ht,rfl⟩
      exact ⟨hline ht,(hclosed t ht).2⟩
    · intro z hz
      obtain ⟨t,ht,heq⟩ := him.Icc_subset himb hima hz.2
      exact ⟨t,ht,Complex.ext ((hline ht).trans hz.1.symm) heq⟩
/-- A closed-disk homeomorphism with positively ordered prescribed corner values
and exact boundary containment sends each entire marked circle arc onto its side.
The open angular interval avoids all four marks; injectivity excludes all corners
from its image, and the boundary-path separation theorem selects the side. -/
lemma marked_disk_homeomorph_side_images {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (ζ : Fin 4 → ℂ) (hcircle : ∀ i, ‖ζ i‖ = 1)
    (hcyclic : PositiveCircleCyclicOrder ζ)
    (Φ : Metric.closedBall (0:ℂ) 1 ≃ₜ ClosedRectangle a b)
    (hmarks : ∀ i, (Φ ⟨ζ i,by simpa [Metric.mem_closedBall] using (hcircle i).le⟩ : ℂ) =
      RectangleCorner a b i)
    (hborder : ∀ z : Metric.closedBall (0:ℂ) 1, ‖(z:ℂ)‖ = 1 →
      (Φ z:ℂ).re = 0 ∨ (Φ z:ℂ).re = a ∨ (Φ z:ℂ).im = 0 ∨ (Φ z:ℂ).im = b) :
    ∀ i : Fin 4,
      (fun z : Metric.closedBall (0:ℂ) 1 ↦ (Φ z:ℂ)) ''
        {z | (z:ℂ) ∈ PositiveClosedCircleArc (ζ i) (ζ (i+1))} =
      ClosedRectangleSide a b i := by
  intro i
  obtain ⟨α,β,hab,hshort,hα,hβ,havoid⟩ := cyclic_adjacent_interval hcyclic i
  have hnorm (t : ℝ) : ‖circleMap 0 1 t‖ = 1 := by simp
  let p : ℝ → Metric.closedBall (0:ℂ) 1 := fun t ↦
    ⟨circleMap 0 1 t,by simp [Metric.mem_closedBall]⟩
  let g : ℝ → ℂ := fun t ↦ (Φ (p t):ℂ)
  have hg : Continuous g := by
    apply (continuous_subtype_val.comp Φ.continuous).comp
    apply Continuous.subtype_mk
    unfold circleMap
    fun_prop
  have hgc (t : ℝ) : g t ∈ ClosedRectangle a b := (Φ (p t)).property
  have hgb (t : ℝ) : (g t).re = 0 ∨ (g t).re = a ∨ (g t).im = 0 ∨ (g t).im = b :=
    hborder (p t) (hnorm t)
  have hgneq (t : ℝ) (ht : t ∈ Ioo α β) (j : Fin 4) : g t ≠ RectangleCorner a b j := by
    intro heq
    have hp := Φ.injective (Subtype.ext (heq.trans (hmarks j).symm))
    exact havoid t ht j (congrArg Subtype.val hp)
  have hgcorners (t : ℝ) (ht : t ∈ Ioo α β) :
      ¬ (((g t).re = 0 ∨ (g t).re = a) ∧ ((g t).im = 0 ∨ (g t).im = b)) := by
    rintro ⟨hr|hr,hi|hi⟩
    · apply hgneq t ht 0
      exact Complex.ext hr hi
    · apply hgneq t ht 3
      apply Complex.ext <;> simpa [RectangleCorner] using ‹_›
    · apply hgneq t ht 1
      apply Complex.ext <;> simpa [RectangleCorner] using ‹_›
    · apply hgneq t ht 2
      apply Complex.ext <;> simpa [RectangleCorner] using ‹_›
  have hga : g α = RectangleCorner a b i := by
    change (Φ (p α):ℂ) = _
    have hp : p α = ⟨ζ i,by simpa [Metric.mem_closedBall] using (hcircle i).le⟩ := Subtype.ext hα
    rw [hp,hmarks]
  have hgbeta : g β = RectangleCorner a b (i+1) := by
    change (Φ (p β):ℂ) = _
    have hp : p β = ⟨ζ (i+1),by simpa [Metric.mem_closedBall] using (hcircle (i+1)).le⟩ := Subtype.ext hβ
    rw [hp,hmarks]
  have himage := rectangle_boundary_path_image ha hb hab g hg.continuousOn
    (fun t _ ↦ hgc t) (fun t _ ↦ hgb t) hgcorners i hga hgbeta
  rw [← himage]
  have harc : PositiveClosedCircleArc (ζ i) (ζ (i+1)) = circleMap 0 1 '' Icc α β := by
    rw [← hα,← hβ]
    exact positiveClosedCircleArc_eq_image_of_lifts hab hshort
  ext w
  constructor
  · rintro ⟨z,hz,rfl⟩
    rw [harc] at hz
    obtain ⟨t,ht,heq⟩ := hz
    refine ⟨t,ht,?_⟩
    exact congrArg (fun z ↦ (Φ z:ℂ)) (Subtype.ext heq)
  · rintro ⟨t,ht,rfl⟩
    refine ⟨p t,?_,rfl⟩
    change circleMap 0 1 t ∈ PositiveClosedCircleArc (ζ i) (ζ (i+1))
    rw [harc]
    exact mem_image_of_mem _ ht


/--
The published marked Schwarz–Christoffel construction in a directly reusable
existential form. The target wrapper supplies the public names used downstream.
-/
theorem exists_disk_rectangle_map_source
    (ζ : Fin 4 → ℂ) (hcircle : ∀ i, ‖ζ i‖ = 1)
    (_hdistinct : Function.Injective ζ) (hcyclic : PositiveCircleCyclicOrder ζ)
    (_hpositive : (0 : ℝ) < 1) (_hunit : (1 : ℝ) = 1) :
    ∃ a b : ℝ, 0 < a ∧ 0 < b ∧
      ∃ S T : ℂ → ℂ,
        DifferentiableOn ℂ S (Metric.ball (0 : ℂ) 1) ∧
        DifferentiableOn ℂ T (OpenRectangle a b) ∧
        BijOn S (Metric.ball (0 : ℂ) 1) (OpenRectangle a b) ∧
        MapsTo T (OpenRectangle a b) (Metric.ball (0 : ℂ) 1) ∧
        (∀ z ∈ Metric.ball (0 : ℂ) 1, T (S z) = z) ∧
        (∀ w ∈ OpenRectangle a b, S (T w) = w) ∧
        ∃ boundaryExtension : (Metric.closedBall (0 : ℂ) 1) ≃ₜ ClosedRectangle a b,
          (∀ z : Metric.closedBall (0 : ℂ) 1,
            ‖(z : ℂ)‖ < 1 → (boundaryExtension z : ℂ) = S z) ∧
          (∀ i : Fin 4,
            (boundaryExtension
                ⟨ζ i, by simpa [Metric.mem_closedBall] using (hcircle i).le⟩ : ℂ) =
              RectangleCorner a b i) ∧
          (∀ i : Fin 4,
            (fun z : Metric.closedBall (0 : ℂ) 1 ↦ (boundaryExtension z : ℂ)) ''
                {z | (z : ℂ) ∈ PositiveClosedCircleArc (ζ i) (ζ (i + 1))} =
              ClosedRectangleSide a b i) := by
  obtain ⟨θ, τ, q, x, hθ, hτ0, hτ1, hqeq, hqnorm, hq0, hx, hmarks⟩ :=
    exists_cayley_real_prevertices_of_cyclic ζ hcyclic
  obtain ⟨k, A, B, C, D, hk0, hk1, hdet, hden, hmap⟩ :=
    exists_real_positive_mobius_canonical_prevertices x hx
  let H : ℂ → ℂ := fun z ↦
    ((A : ℂ) * (Complex.I * (q + z) / (q - z)) + B) /
      ((C : ℂ) * (Complex.I * (q + z) / (q - z)) + D)
  have hHmarks (i : Fin 4) : H (ζ i) = (canonicalPrevertex k i : ℂ) := by
    dsimp [H]
    rw [(hmarks i).2.2]
    exact_mod_cast hmap i
  have hHden (i : Fin 4) :
      (C : ℂ) * (Complex.I * (q + ζ i) / (q - ζ i)) + D ≠ 0 := by
    rw [(hmarks i).2.2]
    exact_mod_cast hden (x i) ⟨hx.monotone (Fin.zero_le i), hx.monotone (Fin.le_last i)⟩
  have hki : 1 < 1 / k := (lt_div_iff₀ hk0).mpr (by simpa using hk1)
  have hki' : 1 < k⁻¹ := by simpa using hki
  have hnegki : -1 / k < (-1 : ℝ) := by
    simpa [div_eq_mul_inv] using (neg_lt_neg hki')
  have hnegki' : -k⁻¹ < (-1 : ℝ) := neg_lt_neg hki'
  have hcanonical : StrictMono (canonicalPrevertex k) := by
    apply Fin.strictMono_iff_lt_succ.mpr
    intro i
    fin_cases i <;> simp [canonicalPrevertex] <;> linarith [hki, hki', hnegki, hnegki']
  obtain ⟨W, Wbar, hW, hWbarEq, hWbarCont, hWbarInc, L, hWbarTop, hWbarBot⟩ :=
    exists_marked_rectangle_g3_primitive_with_boundary (canonicalPrevertex k)
      hcanonical.injective
  have hc : Continuous (fun t : ℝ ↦ Wbar (t : ℂ)) := by
    apply continuousOn_univ.mp
    exact hWbarCont.comp Complex.continuous_ofReal.continuousOn (fun t _ ↦ by simp)
  have houter_aligned := schwarzChristoffel_outer_prevertices_aligned
    (canonicalPrevertex k) hcanonical Wbar L hc hWbarTop hWbarBot hWbarInc
  have houter_real_eq : (Wbar ((-1 / k : ℝ) : ℂ)).re =
      (Wbar ((1 / k : ℝ) : ℂ)).re := by
    simpa [canonicalPrevertex] using houter_aligned.1.trans houter_aligned.2.symm
  have htop_re : Filter.Tendsto (fun t : ℝ ↦ (Wbar (t : ℂ)).re) Filter.atTop (nhds L.re) := by
    exact (Complex.continuous_re.tendsto L).comp hWbarTop
  have hbot_re : Filter.Tendsto (fun t : ℝ ↦ (Wbar (t : ℂ)).re) Filter.atBot (nhds L.re) := by
    exact (Complex.continuous_re.tendsto L).comp hWbarBot
  have hleft_real_constant : ∀ u v : ℝ, u ≤ v → v < -1 / k →
      (Wbar (u : ℂ)).re = (Wbar (v : ℂ)).re := by
    intro u v huv hv
    have hinc := hWbarInc u v huv
    have havoid : ∀ j : Fin 4, canonicalPrevertex k j ∉ Icc u v := by
      intro j hj
      fin_cases j <;> simp [canonicalPrevertex, Set.mem_Icc] at hj <;>
        linarith [hnegki, hnegki', hki, hki', hv]
    have hinc' := hinc havoid
    have hz := schwarzChristoffel_outer_increment_re (canonicalPrevertex k)
      huv (Or.inl (by
        intro j
        fin_cases j <;> simp [canonicalPrevertex] <;> linarith [hnegki, hnegki', hv]))
      Wbar hinc'
    exact hz.symm
  have hright_real_constant : ∀ u v : ℝ, 1 / k < u → u ≤ v →
      (Wbar (u : ℂ)).re = (Wbar (v : ℂ)).re := by
    intro u v hu huv
    have hu' : k⁻¹ < u := by simpa using hu
    have hinc := hWbarInc u v huv
    have havoid : ∀ j : Fin 4, canonicalPrevertex k j ∉ Icc u v := by
      intro j hj
      fin_cases j <;> simp [canonicalPrevertex, Set.mem_Icc] at hj <;>
        linarith [hnegki, hnegki', hki, hki', hu, hu']
    have hinc' := hinc havoid
    have hz := schwarzChristoffel_outer_increment_re (canonicalPrevertex k)
      huv (Or.inr (by
        intro j
        fin_cases j <;> simp [canonicalPrevertex] <;> linarith [hnegki, hnegki', hu, hu']))
      Wbar hinc'
    exact hz.symm
  have hcre : Continuous (fun t : ℝ ↦ (Wbar (t : ℂ)).re) :=
    Complex.continuous_re.comp hc
  have houter_endpoints := outer_real_coordinates_eq_shared_limit
    (fun t : ℝ ↦ (Wbar (t : ℂ)).re) hcre
      htop_re hbot_re
      (fun u v huv hv ↦ hleft_real_constant u v huv hv)
      (fun u v huv hu ↦ hright_real_constant u v hu huv)
  have hcentral_increment {a b : ℝ} (hab : a ≤ b) (ha : -1 < a) (hb : b < 1) :
      Wbar (b : ℂ) - Wbar (a : ℂ) = ∫ t in a..b, -Complex.I *
        ∏ j : Fin 4, Complex.exp (-Complex.log ((t : ℂ) -
          (canonicalPrevertex k j : ℂ)) / 2) := by
    apply hWbarInc a b hab
    intro j hj
    fin_cases j <;> simp [canonicalPrevertex, Set.mem_Icc] at hj <;> linarith [hnegki, hnegki']
  have hcentral_strictMono : StrictMonoOn (fun t : ℝ ↦ (Wbar (t : ℂ)).im)
      (Ioo (-1 : ℝ) 1) := by
    intro a ha b hb hab
    exact (canonical_central_increment_strict hk0 hk1 hab ha.1 hb.2 Wbar
      (hcentral_increment hab.le ha.1 hb.2)).2
  have hcentral_real_constant : ∀ t ∈ Ioo (-1 : ℝ) 1,
      (Wbar (t : ℂ)).re = (Wbar 0).re := by
    intro t ht
    rcases lt_trichotomy t 0 with hneg | heq | hpos
    · simpa using (canonical_central_increment_strict hk0 hk1 hneg ht.1
        (by norm_num) Wbar (hcentral_increment hneg.le ht.1 (by norm_num))).1.symm
    · subst t; simp
    · simpa using (canonical_central_increment_strict hk0 hk1 hpos (by norm_num)
        ht.2 Wbar (hcentral_increment hpos.le (by norm_num) ht.2)).1
  have hcentral_closed_side := complex_central_side_coverage
    (by norm_num : (-1 : ℝ) < 1) (fun t : ℝ ↦ Wbar (t : ℂ))
    hc.continuousOn hcentral_strictMono hcentral_real_constant
  have hcentral_height_pos : 0 < (Wbar 1).im - (Wbar (-1)).im := by
    apply sub_pos.mpr
    simpa using hcentral_closed_side.1
      (show (-1 : ℝ) ∈ Icc (-1 : ℝ) 1 by norm_num)
      (show (1 : ℝ) ∈ Icc (-1 : ℝ) 1 by norm_num) (by norm_num)
  have hhorizontal_widths_eq :
      (Wbar (-1)).re - (Wbar ((-1 / k : ℝ) : ℂ)).re =
        (Wbar 1).re - (Wbar ((1 / k : ℝ) : ℂ)).re := by
    have hmiddle_real_eq : (Wbar (-1)).re = (Wbar 1).re := by
      have ha := hcentral_closed_side.2.1 (-1) (by norm_num)
      have hb := hcentral_closed_side.2.1 1 (by norm_num)
      simpa using ha.trans hb.symm
    rw [houter_real_eq, hmiddle_real_eq]
  have hleft_increment {a b : ℝ} (hab : a ≤ b) (ha : -1 / k < a) (hb : b < -1) :
      Wbar (b : ℂ) - Wbar (a : ℂ) = ∫ t in a..b, -Complex.I *
        ∏ j : Fin 4, Complex.exp (-Complex.log ((t : ℂ) -
          (canonicalPrevertex k j : ℂ)) / 2) := by
    apply hWbarInc a b hab
    intro j hj
    fin_cases j <;> simp [canonicalPrevertex, Set.mem_Icc] at hj <;> linarith [hnegki, hnegki']
  have hright_increment {a b : ℝ} (hab : a ≤ b) (ha : 1 < a) (hb : b < 1 / k) :
      Wbar (b : ℂ) - Wbar (a : ℂ) = ∫ t in a..b, -Complex.I *
        ∏ j : Fin 4, Complex.exp (-Complex.log ((t : ℂ) -
          (canonicalPrevertex k j : ℂ)) / 2) := by
    apply hWbarInc a b hab
    intro j hj
    have hb' : b < k⁻¹ := by simpa using hb
    fin_cases j <;> simp [canonicalPrevertex, Set.mem_Icc] at hj <;> linarith [hnegki, hnegki', hki, hki', hb']
  have hleft_strictMono : StrictMonoOn (fun t : ℝ ↦ (Wbar (t : ℂ)).re)
      (Ioo (-1 / k) (-1)) := by
    intro a ha b hb hab
    exact (canonical_left_increment_strict hk0 hk1 hab ha.1 hb.2 Wbar
      (hleft_increment hab.le ha.1 hb.2)).2
  have hright_strictAnti : StrictAntiOn (fun t : ℝ ↦ (Wbar (t : ℂ)).re)
      (Ioo 1 (1 / k)) := by
    intro a ha b hb hab
    exact (canonical_right_increment_strict hk0 hk1 hab ha.1 hb.2 Wbar
      (hright_increment hab.le ha.1 hb.2)).2
  have hmleft : -1 / k < (-1 / k - 1) / 2 ∧ (-1 / k - 1) / 2 < -1 := by
    constructor <;> linarith [hki, hki', hnegki, hnegki']
  have hmright : 1 < (1 + 1 / k) / 2 ∧ (1 + 1 / k) / 2 < 1 / k := by
    constructor <;> linarith [hki, hki']
  have hleft_imag_constant : ∀ t ∈ Ioo (-1 / k) (-1),
      (Wbar (t : ℂ)).im = (Wbar (((-1 / k - 1) / 2 : ℝ) : ℂ)).im := by
    intro t ht
    rcases lt_trichotomy t ((-1 / k - 1) / 2) with hlt | heq | hgt
    · exact (canonical_left_increment_strict hk0 hk1 hlt ht.1 hmleft.2 Wbar
        (hleft_increment hlt.le ht.1 hmleft.2)).1.symm
    · rw [heq]
    · exact (canonical_left_increment_strict hk0 hk1 hgt hmleft.1 ht.2 Wbar
        (hleft_increment hgt.le hmleft.1 ht.2)).1
  have hleft_closed_side := complex_horizontal_side_coverage
    hnegki (fun t : ℝ ↦ Wbar (t : ℂ)) hc.continuousOn
    hleft_strictMono hleft_imag_constant
  have hwidth_pos : 0 < (Wbar (-1)).re - (Wbar ((-1 / k : ℝ) : ℂ)).re := by
    apply sub_pos.mpr
    simpa using hleft_closed_side.1
      (show -1 / k ∈ Icc (-1 / k) (-1) by constructor <;> linarith)
      (show (-1 : ℝ) ∈ Icc (-1 / k) (-1) by constructor <;> linarith)
      (by linarith)
  have hright_imag_constant : ∀ t ∈ Ioo 1 (1 / k),
      (Wbar (t : ℂ)).im = (Wbar (((1 + 1 / k) / 2 : ℝ) : ℂ)).im := by
    intro t ht
    rcases lt_trichotomy t ((1 + 1 / k) / 2) with hlt | heq | hgt
    · exact (canonical_right_increment_strict hk0 hk1 hlt ht.1 hmright.2 Wbar
        (hright_increment hlt.le ht.1 hmright.2)).1.symm
    · rw [heq]
    · exact (canonical_right_increment_strict hk0 hk1 hgt hmright.1 ht.2 Wbar
        (hright_increment hgt.le hmright.1 ht.2)).1
  have hright_neg_strictMono : StrictMonoOn (fun t : ℝ ↦ (-Wbar (t : ℂ)).re)
      (Ioo 1 (1 / k)) := by
    intro a ha b hb hab
    exact neg_lt_neg (hright_strictAnti ha hb hab)
  have hright_neg_imag_constant : ∀ t ∈ Ioo 1 (1 / k),
      (-Wbar (t : ℂ)).im = -(Wbar (((1 + 1 / k) / 2 : ℝ) : ℂ)).im := by
    intro t ht
    simp only [Complex.neg_im, hright_imag_constant t ht]
  have hright_neg_closed_side := complex_horizontal_side_coverage hki
    (fun t : ℝ ↦ -Wbar (t : ℂ)) hc.neg.continuousOn
    hright_neg_strictMono hright_neg_imag_constant
  have hWdiff : DifferentiableOn ℂ W {z : ℂ | 0 < z.im} := by
    intro z hz
    exact (hW z hz).1.differentiableAt.differentiableWithinAt
  have hcanonicalDerivative := canonical_primitive_derivative_square W
    (fun z hz ↦ (hW z hz).2.2)
  let M : ℝ := ∑ j : Fin 4, ‖(canonicalPrevertex k j : ℂ)‖
  have hM0 : 0 ≤ M := by
    dsimp [M]
    exact Finset.sum_nonneg (fun j _ ↦ norm_nonneg ((canonicalPrevertex k j : ℂ)))
  have hMj (j : Fin 4) : ‖(canonicalPrevertex k j : ℂ)‖ ≤ M := by
    dsimp [M]
    exact Finset.single_le_sum
      (fun i _ ↦ norm_nonneg ((canonicalPrevertex k i : ℂ))) (Finset.mem_univ j)
  have hdecay4 : ∀ z : ℂ, 0 < z.im → 2 * M ≤ ‖z‖ →
      ‖deriv W z‖ ≤ 4 / ‖z‖ ^ 2 :=
    canonical_deriv_decay (W := W) (x := canonicalPrevertex k) (M := M)
      (fun z hz ↦ (hW z hz).2.2) hMj hM0
  obtain ⟨Fbar, hFbarEq, hFbarCont⟩ :=
    schwarzChristoffel_primitive_continuous_extension
      (canonicalPrevertex k) hcanonical.injective W
      (fun z hz ↦ ⟨(hW z hz).1.differentiableAt, (hW z hz).2.2⟩)
  have hFbarN := inverseCayley_boundary_agreement hWbarEq hWbarCont hFbarEq hFbarCont
  have hFbar1 := cayley_boundary_value_at_one hWbarEq hWbarCont hFbarEq hFbarCont hWbarTop
  have hFbarRegular := cayley_pullback_regular
    (fun z hz ↦ ⟨(hW z hz).1.differentiableAt, (hW z hz).2.1⟩) hFbarEq
  let J := realMobiusDiskHomeomorph q hqnorm A B C D hdet
  have hJmarks (i : Fin 4) :
      (J ⟨ζ i, (hcircle i).le⟩ : ℂ) =
        ((canonicalPrevertex k i : ℂ)-Complex.I) /
          ((canonicalPrevertex k i : ℂ)+Complex.I) := by
    apply realMobiusDiskHomeomorph_at_real q hqnorm A B C D hdet
      ⟨ζ i, (hcircle i).le⟩ (x i) (canonicalPrevertex k i) (hmarks i).2.1
      (hmarks i).2.2
    exact (div_eq_iff (hden (x i)
      ⟨hx.monotone (Fin.zero_le i), hx.monotone (Fin.le_last i)⟩)).mp (hmap i)
  have hleft_im_ends : (Wbar ((-1/k : ℝ) : ℂ)).im = (Wbar (-1)).im := by
    simpa using (hleft_closed_side.2.1 (-1/k) ⟨le_rfl, hnegki.le⟩).trans
      (hleft_closed_side.2.1 (-1) ⟨hnegki.le, le_rfl⟩).symm
  have hright_im_ends : (Wbar ((1/k : ℝ) : ℂ)).im = (Wbar 1).im := by
    have he := (hright_neg_closed_side.2.1 _ ⟨hki.le, le_rfl⟩).trans
      (hright_neg_closed_side.2.1 _ ⟨le_rfl, hki.le⟩).symm
    simpa using he
  have hmiddle_re_ends : (Wbar (-1)).re = (Wbar 1).re := by
    simpa using (hcentral_closed_side.2.1 (-1) (by norm_num)).trans
      (hcentral_closed_side.2.1 1 (by norm_num)).symm
  have houter_side := schwarzChristoffel_outer_side_coverage (canonicalPrevertex k)
    hcanonical Wbar L hc hWbarTop hWbarBot hWbarInc
  let r₀ := (Wbar ((-1/k : ℝ) : ℂ)).re
  let r₁ := (Wbar (-1)).re
  let y₀ := (Wbar (-1)).im
  let y₁ := (Wbar 1).im
  have hr : r₀ < r₁ := sub_pos.mp hwidth_pos
  have hy : y₀ < y₁ := sub_pos.mp hcentral_height_pos
  have hLre : L.re = r₀ := by
    simpa [r₀, canonicalPrevertex] using houter_aligned.1.symm
  have hLi : L.im ∈ Icc y₀ y₁ := by
    have hl := houter_side.1
    have hh := houter_side.2.1
    change (Wbar ((-1/k : ℝ) : ℂ)).im < L.im at hl
    change L.im < (Wbar ((1/k : ℝ) : ℂ)).im at hh
    rw [hleft_im_ends] at hl
    rw [hright_im_ends] at hh
    exact ⟨hl.le, hh.le⟩
  have hrealBoundary (t : ℝ) :
      Wbar (t : ℂ) ∈ Complex.reProdIm (Icc r₀ r₁) (Icc y₀ y₁) ∧
      Wbar (t : ℂ) ∉ Complex.reProdIm (Ioo r₀ r₁) (Ioo y₀ y₁) := by
    change ((r₀ ≤ (Wbar (t : ℂ)).re ∧ (Wbar (t : ℂ)).re ≤ r₁) ∧
      (y₀ ≤ (Wbar (t : ℂ)).im ∧ (Wbar (t : ℂ)).im ≤ y₁)) ∧
      ¬ ((r₀ < (Wbar (t : ℂ)).re ∧ (Wbar (t : ℂ)).re < r₁) ∧
      (y₀ < (Wbar (t : ℂ)).im ∧ (Wbar (t : ℂ)).im < y₁))
    by_cases hout : t ≤ -1/k ∨ 1/k ≤ t
    · have hm : Wbar (t : ℂ) ∈
          (fun t : ℝ ↦ Wbar (t : ℂ)) ''
            (Iic (canonicalPrevertex k 0) ∪ Ici (canonicalPrevertex k 3)) ∪ {L} := by
        apply Or.inl
        exact ⟨t, by simpa [canonicalPrevertex] using hout, rfl⟩
      rw [houter_side.2.2] at hm
      have hre : (Wbar (t : ℂ)).re = r₀ := hm.1.trans hLre
      have him : (Wbar (t : ℂ)).im ∈ Icc y₀ y₁ := by
        have hi := hm.2
        change (Wbar ((-1/k : ℝ) : ℂ)).im ≤ (Wbar (t : ℂ)).im ∧
          (Wbar (t : ℂ)).im ≤ (Wbar ((1/k : ℝ) : ℂ)).im at hi
        rw [hleft_im_ends,hright_im_ends] at hi
        exact hi
      refine ⟨⟨⟨by rw [hre], by rw [hre]; exact hr.le⟩, him⟩, ?_⟩
      intro hi
      have hlt := hi.1.1
      rw [hre] at hlt
      exact lt_irrefl _ hlt
    have htl : -1/k ≤ t := le_of_lt (lt_of_not_ge (fun h ↦ hout (Or.inl h)))
    have htr : t ≤ 1/k := le_of_lt (lt_of_not_ge (fun h ↦ hout (Or.inr h)))
    by_cases hl : t ≤ -1
    · have ht : t ∈ Icc (-1/k) (-1) := ⟨htl, hl⟩
      have hlow := hleft_closed_side.1.monotoneOn ⟨le_rfl,hnegki.le⟩ ht htl
      have hhigh := hleft_closed_side.1.monotoneOn ht ⟨hnegki.le,le_rfl⟩ hl
      have him : (Wbar (t : ℂ)).im = y₀ := by
        simpa [y₀] using (hleft_closed_side.2.1 t ht).trans
          (hleft_closed_side.2.1 (-1) ⟨hnegki.le,le_rfl⟩).symm
      norm_num only [Complex.ofReal_neg, Complex.ofReal_one] at hlow hhigh
      refine ⟨⟨⟨hlow,hhigh⟩, by rw [him]; exact ⟨le_rfl,hy.le⟩⟩, ?_⟩
      intro hi
      have hlt := hi.2.1
      rw [him] at hlt
      exact lt_irrefl _ hlt
    by_cases hc : t ≤ 1
    · have ht : t ∈ Icc (-1 : ℝ) 1 := ⟨(lt_of_not_ge hl).le,hc⟩
      have hre : (Wbar (t : ℂ)).re = r₁ := by
        simpa [r₁] using (hcentral_closed_side.2.1 t ht).trans
          (hcentral_closed_side.2.1 (-1) (by norm_num)).symm
      have hlow := hcentral_closed_side.1.monotoneOn (a := -1) (by norm_num) ht ht.1
      have hhigh := hcentral_closed_side.1.monotoneOn (b := 1) ht (by norm_num) ht.2
      norm_num only [Complex.ofReal_neg, Complex.ofReal_one] at hlow hhigh
      refine ⟨⟨by rw [hre]; exact ⟨hr.le,le_rfl⟩, ⟨hlow,hhigh⟩⟩, ?_⟩
      intro hi
      have hlt := hi.1.2
      rw [hre] at hlt
      exact lt_irrefl _ hlt
    · have ht : t ∈ Icc 1 (1/k) := ⟨(lt_of_not_ge hc).le,htr⟩
      have hlo := hright_neg_closed_side.1.monotoneOn ⟨le_rfl,hki.le⟩ ht ht.1
      have hhi := hright_neg_closed_side.1.monotoneOn ht ⟨hki.le,le_rfl⟩ ht.2
      simp only [Complex.neg_re, Complex.ofReal_one] at hlo hhi
      have hlow : r₀ ≤ (Wbar (t : ℂ)).re := by
        dsimp [r₀]
        rw [houter_real_eq]
        linarith
      have hhigh : (Wbar (t : ℂ)).re ≤ r₁ := by
        dsimp [r₁]
        rw [hmiddle_re_ends]
        linarith
      have him : (Wbar (t : ℂ)).im = y₁ := by
        have he := (hright_neg_closed_side.2.1 t ht).trans
          (hright_neg_closed_side.2.1 _ ⟨le_rfl,hki.le⟩).symm
        simpa [y₁] using he
      refine ⟨⟨⟨hlow,hhigh⟩, by rw [him]; exact ⟨hy.le,le_rfl⟩⟩, ?_⟩
      intro hi
      have hlt := hi.2.2
      rw [him] at hlt
      exact lt_irrefl _ hlt
  have hFbarBoundary : ∀ z ∈ Metric.sphere (0 : ℂ) 1,
      Fbar z ∈ Complex.reProdIm (Icc r₀ r₁) (Icc y₀ y₁) ∧
      Fbar z ∉ Complex.reProdIm (Ioo r₀ r₁) (Ioo y₀ y₁) := by
    intro z hz
    change ((r₀ ≤ (Fbar z).re ∧ (Fbar z).re ≤ r₁) ∧
      (y₀ ≤ (Fbar z).im ∧ (Fbar z).im ≤ y₁)) ∧
      ¬ ((r₀ < (Fbar z).re ∧ (Fbar z).re < r₁) ∧
      (y₀ < (Fbar z).im ∧ (Fbar z).im < y₁))
    by_cases hz1 : z = 1
    · subst z
      rw [hFbar1]
      refine ⟨⟨by rw [hLre]; exact ⟨le_rfl,hr.le⟩,hLi⟩, ?_⟩
      intro hi
      have hlt := hi.1.1
      rw [hLre] at hlt
      exact lt_irrefl _ hlt
    · obtain ⟨t,ht⟩ := unit_circle_inverseCayley (by simpa using hz) hz1
      have he : Fbar (inverseCayley (t : ℂ)) = Wbar (t : ℂ) := hFbarN (by simp)
      rw [← ht, he]
      exact hrealBoundary t
  have hFbarBij := disk_rectangle_bijOn_of_boundary hr hy hFbarRegular.1
    (by simpa only [Metric.closedBall, dist_zero_right] using hFbarCont)
    hFbarRegular.2 hFbarBoundary
  let Q := Complex.reProdIm (Ioo r₀ r₁) (Ioo y₀ y₁)
  have hQc : Convex ℝ Q :=
    (convex_Ioo r₀ r₁).linear_preimage Complex.reCLM.toLinearMap |>.inter
      ((convex_Ioo y₀ y₁).linear_preimage Complex.imCLM.toLinearMap)
  have hQo : IsOpen Q := isOpen_Ioo.reProdIm isOpen_Ioo
  have hQne : Q.Nonempty := by
    refine ⟨((r₀+r₁)/2 : ℝ) + ((y₀+y₁)/2 : ℝ) * Complex.I, ?_⟩
    change _ ∈ Complex.reProdIm (Ioo r₀ r₁) (Ioo y₀ y₁)
    simp only [Complex.reProdIm, Set.mem_inter_iff, Set.mem_preimage,
      Set.mem_Ioo, Complex.add_re, Complex.add_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.mul_re, Complex.mul_im, Complex.I_re,
      Complex.I_im, mul_zero, mul_one,  sub_zero, add_zero, zero_add]
    exact ⟨⟨by linarith,by linarith⟩,⟨by linarith,by linarith⟩⟩
  have hQb : Bornology.IsBounded Q :=
    (isCompact_Icc.reProdIm isCompact_Icc).isBounded.subset
      (fun z hz ↦ ⟨⟨hz.1.1.le,hz.1.2.le⟩,⟨hz.2.1.le,hz.2.2.le⟩⟩)
  obtain ⟨E,hE⟩ := convex_continuous_extension_homeomorph hQc hQo hQne hQb
    Fbar hFbarRegular.1 hFbarBij
    (by simpa only [Metric.closedBall, dist_zero_right] using hFbarCont)
  let d : ℂ := ((B-C : ℝ) : ℂ) + ((A+D : ℝ) : ℂ)*Complex.I
  let e : ℂ := ((-B-C : ℝ) : ℂ) + ((A-D : ℝ) : ℂ)*Complex.I
  let j : ℂ → ℂ := fun z ↦ (-conj e*q-conj d*z)/(d*q+e*z)
  have hj := compactifiedMobius_holomorphic_bijOn q d e hqnorm
    (realMobius_coefficient_norm A B C D hdet)
  change DifferentiableOn ℂ j (ball (0:ℂ) 1) ∧ BijOn j (ball (0:ℂ) 1) (ball (0:ℂ) 1) at hj
  have hJval (z : {z : ℂ | ‖z‖ ≤ 1}) : (J z : ℂ) = j z :=
    compactifiedMobius_formula q d e hqnorm (realMobius_coefficient_norm A B C D hdet) z
  let a := r₁-r₀
  let b := y₁-y₀
  let c : ℂ := (r₀:ℂ)+(y₀:ℂ)*Complex.I
  let S : ℂ → ℂ := fun z ↦ Fbar (j z)-c
  have hSdiff : DifferentiableOn ℂ S (ball (0:ℂ) 1) :=
    (hFbarRegular.1.comp hj.1 hj.2.mapsTo).sub_const c
  have htranslate (w : ℂ) : w-c ∈ OpenRectangle a b ↔ w ∈ Q := by
    change (0 < (w-c).re ∧ (w-c).re < a) ∧ (0 < (w-c).im ∧ (w-c).im < b) ↔
      (r₀ < w.re ∧ w.re < r₁) ∧ (y₀ < w.im ∧ w.im < y₁)
    simp only [c,a,b,Complex.sub_re,Complex.sub_im,Complex.add_re,Complex.add_im,
      Complex.ofReal_re,Complex.ofReal_im,Complex.mul_re,Complex.mul_im,
      Complex.I_re,Complex.I_im,mul_zero,mul_one,sub_zero,add_zero,zero_add]
    constructor <;> intro h <;> rcases h with ⟨⟨h1,h2⟩,⟨h3,h4⟩⟩ <;>
      exact ⟨⟨by linarith,by linarith⟩,⟨by linarith,by linarith⟩⟩
  have hSbij : BijOn S (ball (0:ℂ) 1) (OpenRectangle a b) := by
    have hcomp := hFbarBij.comp hj.2
    refine ⟨fun z hz ↦ (htranslate _).mpr (hcomp.mapsTo hz),?_,?_⟩
    · intro z hz w hw heq
      exact hcomp.injOn hz hw (sub_left_injective heq)
    · intro w hw
      have hwc : w+c ∈ Q := (htranslate _).mp (by simpa using hw)
      obtain ⟨z,hz,heq⟩ := hcomp.surjOn hwc
      refine ⟨z,hz,?_⟩
      change Fbar (j z)-c = w
      change Fbar (j z) = w+c at heq
      rw [heq,add_sub_cancel_right]
  obtain ⟨T,hTdiff,hTmap,hTS,hST⟩ := holomorphic_bijOn_inverse
    isOpen_ball (isOpen_Ioo.reProdIm isOpen_Ioo) hSdiff hSbij
  let J₀ : closedBall (0:ℂ) 1 ≃ₜ closedBall (0:ℂ) 1 :=
    (Homeomorph.setCongr (by ext z; simp [mem_closedBall])).trans
      (J.trans (Homeomorph.setCongr (by ext z; simp [mem_closedBall])))
  let E₀ := E.trans (Homeomorph.setCongr (closure_open_raw_rectangle hr hy))
  let Φ : closedBall (0:ℂ) 1 ≃ₜ ClosedRectangle a b :=
    J₀.trans (E₀.trans (rawRectangleTranslation r₀ r₁ y₀ y₁))
  have hΦval (z : closedBall (0:ℂ) 1) : (Φ z : ℂ) = S z := by
    change (E (J₀ z) : ℂ)-c = Fbar (j z)-c
    rw [hE]
    congr 2
    exact hJval _
  have hΦmarks : ∀ i : Fin 4,
      (Φ ⟨ζ i,by simpa [Metric.mem_closedBall] using (hcircle i).le⟩ : ℂ) =
        RectangleCorner a b i := by
    intro i
    rw [hΦval]
    change Fbar (j (ζ i))-c = RectangleCorner a b i
    rw [← hJval ⟨ζ i,(hcircle i).le⟩,hJmarks]
    change Fbar (inverseCayley (canonicalPrevertex k i : ℂ))-c = RectangleCorner a b i
    have hFN : Fbar (inverseCayley (canonicalPrevertex k i : ℂ)) = Wbar (canonicalPrevertex k i : ℂ) := hFbarN (by simp)
    rw [hFN]
    fin_cases i
    all_goals simp only [RectangleCorner,canonicalPrevertex]
    · apply Complex.ext
      · simp [c,r₀]
      · simp only [Complex.sub_im,c,Complex.add_im,Complex.ofReal_im,Complex.mul_im,
          Complex.ofReal_re,Complex.I_im,Complex.I_re,mul_one,mul_zero,add_zero,zero_add,Complex.zero_im]
        exact sub_eq_zero.mpr hleft_im_ends
    · apply Complex.ext <;> simp [c,a,r₁,y₀]
    · apply Complex.ext
      · simp only [Complex.sub_re,c,Complex.add_re,Complex.ofReal_re,Complex.mul_re,
          Complex.ofReal_im,Complex.I_re,Complex.I_im,mul_zero,zero_mul,sub_zero,add_zero]
        change (Wbar (1:ℂ)).re-r₀ = r₁-r₀
        exact congrArg (fun t ↦ t-r₀) hmiddle_re_ends.symm
      · simp [c,b,y₁]
    · apply Complex.ext
      · simp only [Complex.sub_re,c,Complex.add_re,Complex.ofReal_re,Complex.mul_re,
          Complex.ofReal_im,Complex.I_re,Complex.I_im,mul_zero,zero_mul,sub_zero,add_zero]
        change (Wbar ((1/k:ℝ):ℂ)).re-r₀ = 0
        exact sub_eq_zero.mpr houter_real_eq.symm
      · simp only [Complex.sub_im,c,Complex.add_im,Complex.ofReal_re,Complex.mul_im,
          Complex.ofReal_im,Complex.I_re,Complex.I_im,mul_zero,mul_one,add_zero,zero_add]
        change (Wbar ((1/k:ℝ):ℂ)).im-y₀ = y₁-y₀
        exact congrArg (fun t ↦ t-y₀) hright_im_ends
  have hborder (z : closedBall (0:ℂ) 1) (hz : ‖(z:ℂ)‖ = 1) :
      (Φ z:ℂ).re = 0 ∨ (Φ z:ℂ).re = a ∨ (Φ z:ℂ).im = 0 ∨ (Φ z:ℂ).im = b := by
    by_contra hn
    push Not at hn
    have hc := (Φ z).property
    have hi : (Φ z:ℂ) ∈ OpenRectangle a b :=
      ⟨⟨lt_of_le_of_ne hc.1.1 hn.1.symm,lt_of_le_of_ne hc.1.2 hn.2.1⟩,
       ⟨lt_of_le_of_ne hc.2.1 hn.2.2.1.symm,lt_of_le_of_ne hc.2.2 hn.2.2.2⟩⟩
    obtain ⟨w,hw,heq⟩ := hSbij.surjOn hi
    have hwc : w ∈ closedBall (0:ℂ) 1 := ball_subset_closedBall hw
    have he := Φ.injective (Subtype.ext ((hΦval ⟨w,hwc⟩).trans heq))
    have hwz : w = (z:ℂ) := congrArg Subtype.val he
    have hw' : ‖w‖ < 1 := by simpa using hw
    rw [hwz,hz] at hw'
    exact lt_irrefl _ hw'
  exact ⟨a,b,sub_pos.mpr hr,sub_pos.mpr hy,S,T,hSdiff,hTdiff,hSbij,hTmap,hTS,hST,Φ,
    (fun z _ ↦ hΦval z),hΦmarks,
    marked_disk_homeomorph_side_images (sub_pos.mpr hr) (sub_pos.mpr hy) ζ hcircle hcyclic Φ hΦmarks hborder⟩

end HolomorphicAnosov.Analysis.MarkedRectangle.Source

