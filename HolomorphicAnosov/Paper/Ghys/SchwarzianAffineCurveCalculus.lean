import HolomorphicAnosov.Analysis.Complex.SchwarzianMobiusConverse
import HolomorphicAnosov.Ghys.SchwarzianCoordinateIndependence
import HolomorphicAnosov.Geometry.LocalHolonomyPathContinuation
import HolomorphicAnosov.Ghys.AffineProjectiveStructure
import HolomorphicAnosov.Ghys.AnosovIntrinsicFoliationPresentation
import HolomorphicAnosov.Paper.Ghys.ActualInvariantSectionFlowboxCoverG5
import HolomorphicAnosov.Paper.Zhang.StableFoliations
import HolomorphicAnosov.Ghys.AffineSchwarzianQuadraticForm
import HolomorphicAnosov.Paper.Ghys.Proposition31
import HolomorphicAnosov.Paper.Ghys.StableHolonomyHolomorphic
import Mathlib.Topology.MetricSpace.HausdorffDistance

/-! This file establishes coordinate independence, the composition law, and the Möbius criterion for
the Schwarzian on affine complex curves (Ghys, §4, pp. 594–595). -/

noncomputable section
open Set Filter _root_.Topology
open scoped ContDiff Manifold
namespace HolomorphicAnosov.Ghys
universe u v w
attribute [local instance] complex_isManifold_real

section Curves
variable {L₀ : Type u} {L₁ : Type v} {L₂ : Type w}
  [TopologicalSpace L₀] [TopologicalSpace L₁] [TopologicalSpace L₂]
  [ChartedSpace (ComplexModel 1) L₀] [ChartedSpace (ComplexModel 1) L₁]
  [ChartedSpace (ComplexModel 1) L₂]
  [IsManifold (complexModel 1) ∞ L₀] [IsManifold (complexModel 1) ∞ L₁]
  [IsManifold (complexModel 1) ∞ L₂]

omit [IsManifold (complexModel 1) ∞ L₀] [IsManifold (complexModel 1) ∞ L₁]
  [IsManifold (complexModel 1) ∞ L₂] in
/-- The Schwarzian in affine coordinates is a quadratic differential, satisfies the composition law,
and vanishes precisely for local Möbius maps. (Ghys, §4, p. 594;
Efraimidis–Ferrada-Salas–Hernández–Vargas, §2.3, Thm 2, p. 8; Dummit, §2.2.1, p. 11; McMullen,
Math 213a notes, p. 70; Lyubich, §2.9.1, pp. 96–97; Teschl, §4.1, pp. 111–113 and §2.2, pp.
36–38.) -/
theorem schwarzian_affine_curve_calculus
    (A₀ : ComplexAffineStructure L₀) (A₁ : ComplexAffineStructure L₁)
    (A₂ : ComplexAffineStructure L₂)
    (h : OpenPartialHomeomorph L₀ L₁) (hh : IsHolomorphicCurveLocalMap h)
    (c : OpenPartialHomeomorph L₀ ℂ) (d : OpenPartialHomeomorph L₁ ℂ)
    (hc : c ∈ ComplexAffineStructure.maximalAtlas L₀ A₀)
    (hd : d ∈ ComplexAffineStructure.maximalAtlas L₁ A₁)
    (x : L₀) (hxc : x ∈ c.source) (hxh : x ∈ h.source)
    (hxd : h x ∈ d.source) :
    IsOpen (affineLocalMapDomain c h d) ∧
    DifferentiableOn ℂ (affineLocalMapExpression c h d) (affineLocalMapDomain c h d) ∧
    (∀ z ∈ affineLocalMapDomain c h d, deriv (affineLocalMapExpression c h d) z ≠ 0) ∧
    (∀ (c' : OpenPartialHomeomorph L₀ ℂ) (d' : OpenPartialHomeomorph L₁ ℂ),
      c' ∈ ComplexAffineStructure.maximalAtlas L₀ A₀ →
      d' ∈ ComplexAffineStructure.maximalAtlas L₁ A₁ →
      x ∈ c'.source → h x ∈ d'.source →
      schwarzianQuadraticAt c h d x = schwarzianQuadraticAt c' h d' x) ∧
    ((∀ᶠ z in 𝓝 (c x), schwarzian (affineLocalMapExpression c h d) z = 0) ↔
      IsMobiusScalarGerm (affineLocalMapExpression c h d) (c x)) ∧
    ((∃ a : ComplexAffineTransformation,
        ∀ᶠ z in 𝓝 (c x), affineLocalMapExpression c h d z = a.apply z) →
      schwarzianQuadraticAt c h d x = 0) ∧
    (∀ (g : OpenPartialHomeomorph L₁ L₂) (e : OpenPartialHomeomorph L₂ ℂ),
      IsHolomorphicCurveLocalMap g →
      e ∈ ComplexAffineStructure.maximalAtlas L₂ A₂ →
      h x ∈ g.source → g (h x) ∈ e.source →
      schwarzian (affineLocalMapExpression c (h.trans g) e) (c x) =
        schwarzian (affineLocalMapExpression c h d) (c x) +
        schwarzian (affineLocalMapExpression d g e) (d (h x)) *
          deriv (affineLocalMapExpression c h d) (c x) ^ 2 ∧
      ∀ v : TangentSpace (complexModel 1) x,
        schwarzianQuadraticAt c (h.trans g) e x v =
          schwarzianQuadraticAt c h d x v +
          schwarzianQuadraticAt d g e (h x)
            (mfderiv (complexModel 1) (complexModel 1) h x v)) := by
  obtain ⟨hΩ, hdiff, hne, hAffineZero, hChain⟩ :=
    affine_local_map_schwarzian_calculus A₀ A₁ A₂ h hh c d hc hd x hxc hxh hxd
  refine ⟨hΩ, hdiff, hne, ?_, ?_, hAffineZero, hChain⟩
  · intro c' d' hc' hd' hxc' hxd'
    exact schwarzian_quadratic_coordinate_independent A₀ A₁ h hh c c' d d'
      hc hc' hd hd' x hxc hxc' hxh hxd hxd'
  · constructor
    · intro hzero
      have hcx : c x ∈ affineLocalMapDomain c h d := by
        exact ⟨⟨c.map_source hxc, by simpa only [Set.mem_preimage, c.left_inv hxc] using hxh⟩,
          by simpa only [Set.mem_preimage, c.left_inv hxc] using hxd⟩
      obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp
        (inter_mem (hΩ.mem_nhds hcx) hzero)
      exact schwarzian_zero_mobius_germ Metric.isOpen_ball (Metric.mem_ball_self hr)
        (hdiff.mono fun _ hz ↦ (hball hz).1)
        (fun z hz ↦ hne z (hball hz).1) (fun _ hz ↦ (hball hz).2)
    · intro hH
      let H : ℂ → ℂ := affineLocalMapExpression c h d
      let z : ℂ := c x
      change IsMobiusScalarGerm H z at hH
      change ∀ᶠ w in 𝓝 z, schwarzian H w = 0
      obtain ⟨m, hm⟩ := hH
      obtain ⟨g, hg⟩ := m.property
      have hcoord : ∀ᶠ w in 𝓝 z, g 1 0 * w + g 1 1 ≠ 0 ∧
          H w = (g 0 0 * w + g 0 1) / (g 1 0 * w + g 1 1) := by
        apply hm.mono
        intro w hw
        have hfin (v : ℂ) : complexProjectiveLineFinite v =
            OnePoint.equivProjectivization ℂ (v : OnePoint ℂ) := by
          simp only [complexProjectiveLineFinite, complexProjectiveLineChartInv,
            complexProjectiveLineMk, OnePoint.equivProjectivization_apply_coe]
          congr 1
          funext i
          fin_cases i <;> rfl
        have he : (H w : OnePoint ℂ) = g • (w : OnePoint ℂ) := by
          apply (OnePoint.equivProjectivization ℂ).injective
          rw [OnePoint.equivProjectivization_smul, ← hfin, ← hfin]
          exact hw.trans (hg _)
        rw [OnePoint.smul_some_eq_ite] at he
        split_ifs at he with hq
        · exact (OnePoint.coe_ne_infty (H w) he).elim
        · exact ⟨hq, OnePoint.coe_injective he⟩
      have he : H =ᶠ[𝓝 z] fun t ↦ (g 0 0 * t + g 0 1) / (g 1 0 * t + g 1 1) :=
        hcoord.mono fun _ h ↦ h.2
      filter_upwards [hcoord, he.deriv, he.deriv.deriv, he.deriv.deriv.deriv] with w hw h1 h2 h3
      unfold schwarzian
      rw [h1, h2, h3]
      let a : ℂ := g 0 0
      let b : ℂ := g 0 1
      let c : ℂ := g 1 0
      let d : ℂ := g 1 1
      have hΔ : a * d - b * c ≠ 0 := by
        simpa only [Matrix.det_fin_two] using g.det_ne_zero
      have hq : c * w + d ≠ 0 := hw.1
      let F : ℂ → ℂ := fun w ↦ (a * w + b) / (c * w + d)
      let D : ℂ := a * d - b * c
      have Q (w : ℂ) : HasDerivAt (fun t : ℂ ↦ c * t + d) c w := by
        simpa using ((hasDerivAt_id w).const_mul c).add_const d
      have D₁ (w : ℂ) (hw : c * w + d ≠ 0) : deriv F w = D / (c * w + d) ^ 2 := by
        have hp : HasDerivAt (fun t : ℂ ↦ a * t + b) a w := by
          simpa using ((hasDerivAt_id w).const_mul a).add_const b
        convert (hp.div (Q w) hw).deriv using 1
        dsimp [D]
        congr 1
        ring
      have N (w : ℂ) (hw : c * w + d ≠ 0) : ∀ᶠ t in 𝓝 w, c * t + d ≠ 0 :=
        (Q w).continuousAt.eventually_ne hw
      have D₂ (w : ℂ) (hw : c * w + d ≠ 0) :
          deriv (deriv F) w = -2 * c * D / (c * w + d) ^ 3 := by
        have he : deriv F =ᶠ[𝓝 w] fun t ↦ D / (c * t + d) ^ 2 :=
          (N w hw).mono fun t ht ↦ D₁ t ht
        rw [he.deriv_eq]
        convert ((hasDerivAt_const w D).div ((Q w).pow 2) (pow_ne_zero 2 hw)).deriv using 1 ;
          simp only [Pi.pow_apply] ; field_simp ; ring
      have hO : IsOpen {w : ℂ | c * w + d ≠ 0} :=
        isOpen_ne.preimage ((continuous_const.mul continuous_id).add continuous_const)
      have hF : DifferentiableOn ℂ F {w : ℂ | c * w + d ≠ 0} := by
        intro w hw
        exact DifferentiableAt.differentiableWithinAt
          ((((hasDerivAt_id w).const_mul a).add_const b).div (Q w) hw).differentiableAt
      have hn : deriv F w ≠ 0 := by
        rw [D₁ w hq]
        exact div_ne_zero hΔ (pow_ne_zero 2 hq)
      let Nf : ℂ → ℂ := fun w ↦ deriv (deriv F) w / deriv F w
      have hN : Nf =ᶠ[𝓝 w] fun w ↦ -2 * c / (c * w + d) := by
        apply (N w hq).mono
        intro w hw
        dsimp [Nf]
        rw [D₂ w hw, D₁ w hw]
        dsimp [D]
        field_simp [hΔ, hw]
        field_simp [show a * d - c * b ≠ 0 by simpa [mul_comm] using hΔ]
      have hdN : deriv Nf w = 2 * c ^ 2 / (c * w + d) ^ 2 := by
        rw [hN.deriv_eq]
        convert ((hasDerivAt_const w (-2 * c)).div (Q w) hq).deriv using 1 ; ring
      have hquot := (((hF.deriv hO).deriv hO).differentiableAt (hO.mem_nhds hq)).hasDerivAt.div
        ((hF.deriv hO).differentiableAt (hO.mem_nhds hq)).hasDerivAt hn
      change HasDerivAt Nf _ w at hquot
      have hS : schwarzian F w = deriv Nf w - (1 / 2 : ℂ) * (Nf w) ^ 2 := by
        rw [hquot.deriv]
        dsimp [schwarzian, Nf]
        field_simp [hn]
        ring
      change schwarzian F w = 0
      rw [hS, hdN, hN.eq_of_nhds]
      field_simp [hq]
      ring

end Curves

end HolomorphicAnosov.Ghys

