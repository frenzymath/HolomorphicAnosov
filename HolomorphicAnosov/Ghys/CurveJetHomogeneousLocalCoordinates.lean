import HolomorphicAnosov.Ghys.CurveJetAffineData
import HolomorphicAnosov.Analysis.Complex.HolomorphicFlatCoordinatePrimitive

/-! Local scalar coordinates of homogeneous holomorphic jet sections. (Ghys, Lemma 3.2) -/

open Filter Set
open scoped Topology _root_.Topology Manifold ContDiff
noncomputable section
namespace HolomorphicAnosov.Ghys
universe u
variable (L : Type u) [TopologicalSpace L] [ChartedSpace ℂ L]
variable [IsManifold (modelWithCornersSelf ℂ ℂ) ∞ L]

/-- A homogeneous holomorphic jet section has holomorphic quadratic coefficients satisfying the
second-derivative transition law. Near each chart point there is a biholomorphic coordinate `H`
satisfying `H″ = -2 A H′`. (Ghys, Lemma 3.2) -/
theorem homogeneous_curve_jet_section_local_coordinates
    [T2Space L] [SecondCountableTopology L]
    (A1 : ChartedSpace (ℂ × ℂ) (CurveJet1 L))
    (A2 : ChartedSpace ((ℂ × ℂ) × ℂ) (CurveJet2 L))
    (hAtlases : CurveJetCoefficientAtlases L A1 A2)
    (σ : HomogeneousCurveJetSection L A1 A2) :
    (∃ A : LeafChart L → ℂ → ℂ,
        (∀ c, DifferentiableOn ℂ (A c) c.1.target) ∧
        (∀ c (j : CurveJet1 L), curveJet1Base L j ∈ c.1.source →
          (curveJet2Coeff L c (σ.1 j)).2 =
            A c (curveJet1Coeff L c j).1 * (curveJet1Coeff L c j).2 ^ 2) ∧
        ∀ c d (z : ℂ), z ∈ c.1.target → c.1.symm z ∈ d.1.source →
          A d (d.1 (c.1.symm z)) * deriv (d.1 ∘ c.1.symm) z ^ 2 =
            deriv (d.1 ∘ c.1.symm) z * A c z +
              iteratedDeriv 2 (d.1 ∘ c.1.symm) z / 2) ∧
    (∀ (c : LeafChart L) (z : ℂ), z ∈ c.1.target → ∃ (A : ℂ → ℂ) (e : OpenPartialHomeomorph ℂ ℂ),
        z ∈ e.source ∧ e.source ⊆ c.1.target ∧
        ContDiffOn ℂ ∞ e e.source ∧ ContDiffOn ℂ ∞ e.symm e.target ∧
        (∀ j : CurveJet1 L, curveJet1Base L j ∈ c.1.source →
          (curveJet2Coeff L c (σ.1 j)).2 =
            A (curveJet1Coeff L c j).1 * (curveJet1Coeff L c j).2 ^ 2) ∧
        ∀ w ∈ e.source,
          deriv e w ≠ 0 ∧ deriv (deriv e) w = (-2 : ℂ) * A w * deriv e w) := by
  rcases hAtlases with ⟨hM1, hM2, hcharts, ha1, ha2⟩
  have hsection_truncation
      (σ : HomogeneousCurveJetSection L A1 A2) (j : CurveJet1 L) :
      curveJetTruncation L (σ.1 j) = j := σ.2.1 j
  have hnormalized (σ : HomogeneousCurveJetSection L A1 A2) (c : LeafChart L) :
      ∃ A : ℂ → ℂ, DifferentiableOn ℂ A c.1.target ∧
        ∀ j : CurveJet1 L, curveJet1Base L j ∈ c.1.source →
          (curveJet2Coeff L c (σ.1 j)).2 =
            A (curveJet1Coeff L c j).1 * (curveJet1Coeff L c j).2 ^ 2 := by
    let : ChartedSpace (ℂ × ℂ) (CurveJet1 L) := A1
    let : ChartedSpace ((ℂ × ℂ) × ℂ) (CurveJet2 L) := A2
    obtain ⟨e1, e2, _, _, hs1, hs2, ht1, ht2, he1, he2,
      _, he1inv, he2smooth, _⟩ := hcharts c
    let A := fun z : ℂ ↦ (e2 (σ.1 (e1.symm (z, 1)))).2
    have hunit (z : ℂ) (hz : z ∈ c.1.target) : (z, 1) ∈ e1.target := by
      rw [ht1]
      exact ⟨hz, one_ne_zero⟩
    have hσsource (j : CurveJet1 L) (hj : j ∈ e1.source) : σ.1 j ∈ e2.source := by
      rw [hs2]
      change curveJet2Base L (σ.1 j) ∈ c.1.source
      rw [← curve_jet_truncation_base L (σ.1 j), hsection_truncation σ j]
      change j ∈ (curveJet1Base L) ⁻¹' c.1.source
      rwa [← hs1]
    refine ⟨A, ?_, ?_⟩
    · intro z hz
      have hzin := hunit z hz
      have h1 := he1inv.contMDiffAt (e1.open_target.mem_nhds hzin)
      have h2 := he2smooth.contMDiffAt
        (e2.open_source.mem_nhds (hσsource _ (e1.map_target hzin)))
      have hcomp : ContMDiffAt (modelWithCornersSelf ℂ (ℂ × ℂ))
          (modelWithCornersSelf ℂ ((ℂ × ℂ) × ℂ)) ∞
          (fun w ↦ e2 (σ.1 (e1.symm w))) (z, 1) :=
        h2.comp (z, 1) ((σ.2.2.1 _).comp (z, 1) h1)
      have hslic : ContDiffAt ℂ ∞ (fun w : ℂ ↦ (w, (1 : ℂ))) z :=
        contDiffAt_id.prodMk contDiffAt_const
      have hscalar : ContDiffAt ℂ ∞ (fun w : ℂ × ℂ ↦ e2 (σ.1 (e1.symm w)))
          (z, 1) := contMDiffAt_iff_contDiffAt.mp hcomp
      have hcomposed := hscalar.comp z hslic
      have hdiff : ContDiffAt ℂ ∞ A z := hcomposed.snd
      exact (hdiff.differentiableAt (by simp)).differentiableWithinAt
    · intro j hj
      have hbij := ((leaf_jet_complex_manifold L).2.2.2.1 c).1
      let w := curveJet1Coeff L c j
      have hw : w ∈ curveJet1Target L c := hbij.mapsTo hj
      let j₀ := e1.symm (w.1, 1)
      have hj₀ : j₀ ∈ e1.source := e1.map_target (hunit _ hw.1)
      have hj₀base : curveJet1Base L j₀ ∈ c.1.source := by
        change j₀ ∈ (curveJet1Base L) ⁻¹' c.1.source
        rwa [← hs1]
      have hj₀coeff : curveJet1Coeff L c j₀ = (w.1, 1) := by
        rw [← he1 hj₀]
        exact e1.right_inv (hunit _ hw.1)
      let omega : ℂˣ := Units.mk0 w.2 hw.2
      have hscale := (curve_jet_reparametrization L).2.2.2.1 omega j₀
      have hscaledbase : curveJet1Base L (curveJet1Scale L omega j₀) ∈ c.1.source :=
        hscale.1.symm ▸ hj₀base
      have hscaled : curveJet1Scale L omega j₀ = j := by
        apply hbij.injOn hscaledbase hj
        rw [hscale.2 c hj₀base, hj₀coeff]
        simp only [omega, Units.val_mk0, mul_one]
        exact Prod.eta w
      have hquad := congrArg Prod.snd
        (homogeneous_curve_jet_section_coeff_scale L σ omega j₀ c hj₀base)
      rw [hscaled] at hquad
      have hA : A w.1 = (curveJet2Coeff L c (σ.1 j₀)).2 := by
        exact congrArg Prod.snd (he2 (hσsource j₀ hj₀))
      change (curveJet2Coeff L c (σ.1 j)).2 = A w.1 * w.2 ^ 2
      rw [hA, hquad]
      change w.2 ^ 2 * _ = _ * w.2 ^ 2
      ring
  have hconnection (σ : HomogeneousCurveJetSection L A1 A2) :
      ∃ A : LeafChart L → ℂ → ℂ,
        (∀ c, DifferentiableOn ℂ (A c) c.1.target) ∧
        (∀ c (j : CurveJet1 L), curveJet1Base L j ∈ c.1.source →
          (curveJet2Coeff L c (σ.1 j)).2 =
            A c (curveJet1Coeff L c j).1 * (curveJet1Coeff L c j).2 ^ 2) ∧
        ∀ c d (z : ℂ), z ∈ c.1.target → c.1.symm z ∈ d.1.source →
          A d (d.1 (c.1.symm z)) * deriv (d.1 ∘ c.1.symm) z ^ 2 =
            deriv (d.1 ∘ c.1.symm) z * A c z +
              iteratedDeriv 2 (d.1 ∘ c.1.symm) z / 2 := by
    classical
    choose A hA hquad using hnormalized σ
    refine ⟨A, hA, hquad, ?_⟩
    intro c d z hz hzd
    have hcoeff := (leaf_jet_complex_manifold L).2.2.2.1
    obtain ⟨j, hjc, hjcoeff⟩ := (hcoeff c).1.surjOn
      (show (z, (1 : ℂ)) ∈ curveJet1Target L c from ⟨hz, one_ne_zero⟩)
    have hjbase : curveJet1Base L j = c.1.symm z := by
      calc
        curveJet1Base L j = c.1.symm (c.1 (curveJet1Base L j)) :=
          (c.1.left_inv hjc).symm
        _ = c.1.symm z := congrArg c.1.symm (congrArg Prod.fst hjcoeff)
    have hjd : curveJet1Base L j ∈ d.1.source := hjbase ▸ hzd
    have hbase : curveJet2Base L (σ.1 j) = curveJet1Base L j := by
      rw [← curve_jet_truncation_base L (σ.1 j), hsection_truncation σ j]
    have hcfirst : (curveJet2Coeff L c (σ.1 j)).1 = (z, 1) := by
      have htrcoeff := ((hcoeff c).2.2 (σ.1 j) (hbase ▸ hjc)).2
      rw [hsection_truncation σ j] at htrcoeff
      exact htrcoeff.symm.trans hjcoeff
    have hcsecond : (curveJet2Coeff L c (σ.1 j)).2 = A c z := by
      simpa only [hjcoeff, one_pow, mul_one] using hquad c j hjc
    have htransition := (leaf_jet_complex_manifold L).2.2.1 c d
    have hfirst := htransition.1 j ⟨hjc, hjd⟩
    have hsecond := congrArg Prod.snd
      (htransition.2 (σ.1 j) ⟨hbase ▸ hjc, hbase ▸ hjd⟩)
    have hqd := hquad d j hjd
    rw [hfirst, hjcoeff] at hqd
    dsimp only [curveJet2Transition] at hsecond
    rw [hcfirst, hcsecond] at hsecond
    dsimp [curveJet1Transition, curveJet2Transition] at hqd hsecond
    simpa only [mul_one, one_pow] using hqd.symm.trans hsecond
  have hflatPrimitive (σ : HomogeneousCurveJetSection L A1 A2)
      (c : LeafChart L) (z : ℂ) (hz : z ∈ c.1.target) :
      ∃ (r : ℝ) (A H : ℂ → ℂ), 0 < r ∧ Metric.ball z r ⊆ c.1.target ∧
        DifferentiableOn ℂ A c.1.target ∧
        (∀ j : CurveJet1 L, curveJet1Base L j ∈ c.1.source →
          (curveJet2Coeff L c (σ.1 j)).2 =
            A (curveJet1Coeff L c j).1 * (curveJet1Coeff L c j).2 ^ 2) ∧
        DifferentiableOn ℂ H (Metric.ball z r) ∧
        ∀ w ∈ Metric.ball z r,
          deriv H w ≠ 0 ∧ deriv (deriv H) w = (-2 : ℂ) * A w * deriv H w := by
    obtain ⟨A, hA, hquad⟩ := hnormalized σ c
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp c.1.open_target z hz
    obtain ⟨H, hH, hderiv⟩ :=
      holomorphic_flat_coordinate_primitive Metric.isOpen_ball (convex_ball z r) (hA.mono hball)
    exact ⟨r, A, H, hr, hball, hA, hquad, hH, hderiv⟩
  have hlocalCoordinate (σ : HomogeneousCurveJetSection L A1 A2)
      (c : LeafChart L) (z : ℂ) (hz : z ∈ c.1.target) :
      ∃ (A : ℂ → ℂ) (e : OpenPartialHomeomorph ℂ ℂ),
        z ∈ e.source ∧ e.source ⊆ c.1.target ∧
        ContDiffOn ℂ ∞ e e.source ∧ ContDiffOn ℂ ∞ e.symm e.target ∧
        (∀ j : CurveJet1 L, curveJet1Base L j ∈ c.1.source →
          (curveJet2Coeff L c (σ.1 j)).2 =
            A (curveJet1Coeff L c j).1 * (curveJet1Coeff L c j).2 ^ 2) ∧
        ∀ w ∈ e.source,
          deriv e w ≠ 0 ∧ deriv (deriv e) w = (-2 : ℂ) * A w * deriv e w := by
    obtain ⟨r, A, H, hr, hball, hA, hquad, hH, hderiv⟩ := hflatPrimitive σ c z hz
    have hzball : z ∈ Metric.ball z r := Metric.mem_ball_self hr
    have hHs : ContDiffOn ℂ ∞ H (Metric.ball z r) := hH.contDiffOn Metric.isOpen_ball
    have hHz : ContDiffAt ℂ ∞ H z := hHs.contDiffAt (Metric.ball_mem_nhds z hr)
    have hd := ((hH z hzball).differentiableAt (Metric.ball_mem_nhds z hr)).hasDerivAt
      |>.hasFDerivAt_equiv (hderiv z hzball).1
    let e₀ := hHz.toOpenPartialHomeomorph H hd (by simp)
    let e := e₀.restrOpen (Metric.ball z r) Metric.isOpen_ball
    have he : (e : ℂ → ℂ) = H := rfl
    have heBall : e.source ⊆ Metric.ball z r := fun _ hw ↦ hw.2
    refine ⟨A, e, ⟨hHz.mem_toOpenPartialHomeomorph_source hd (by simp), hzball⟩,
      heBall.trans hball, ?_, ?_, hquad, ?_⟩
    · simpa only [he] using hHs.mono heBall
    · intro w hw
      have hpre := heBall (e.map_target hw)
      have hne : deriv e (e.symm w) ≠ 0 := by
        simpa only [he] using (hderiv _ hpre).1
      have hder : HasDerivAt e (deriv e (e.symm w)) (e.symm w) := by
        simpa only [he] using
          ((hH _ hpre).differentiableAt (Metric.isOpen_ball.mem_nhds hpre)).hasDerivAt
      have hsmooth : ContDiffAt ℂ ∞ e (e.symm w) := by
        simpa only [he] using hHs.contDiffAt (Metric.isOpen_ball.mem_nhds hpre)
      exact (e.contDiffAt_symm_deriv hne hw hder hsmooth).contDiffWithinAt
    · intro w hw
      simpa only [he] using hderiv w (heBall hw)
  exact ⟨hconnection σ, hlocalCoordinate σ⟩

end HolomorphicAnosov.Ghys

