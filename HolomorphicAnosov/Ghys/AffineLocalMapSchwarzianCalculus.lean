import HolomorphicAnosov.Analysis.Complex.SchwarzianChainRule

/-! This file establishes regularity, affine vanishing, and the scalar and tangent composition laws
for the Schwarzian in holomorphic coordinates. (Ghys, §4, p.594) -/

noncomputable section
open Set Filter _root_.Topology
open scoped ContDiff Manifold
namespace HolomorphicAnosov.Ghys
universe u v w

variable {L₀ : Type u} {L₁ : Type v} {L₂ : Type w}
  [TopologicalSpace L₀] [TopologicalSpace L₁] [TopologicalSpace L₂]
  [ChartedSpace (ComplexModel 1) L₀] [ChartedSpace (ComplexModel 1) L₁]
  [ChartedSpace (ComplexModel 1) L₂]

set_option backward.isDefEq.respectTransparency false in
/-- A local biholomorphism has a holomorphic scalar expression with nonzero derivative on its open
coordinate domain, and affine germs have zero Schwarzian. The Schwarzian satisfies scalar and
tangent composition laws. (Ghys, §4, p.594; Dummit, §2.2.1, p.11) -/
theorem affine_local_map_schwarzian_calculus
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
  have hΩ : IsOpen (affineLocalMapDomain c h d) := by
    exact ((c.symm.trans h).trans d).open_source
  have hdiff : DifferentiableOn ℂ (affineLocalMapExpression c h d)
      (affineLocalMapDomain c h d) := by
    apply mdifferentiableOn_iff_differentiableOn.mp
    have hcd : ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ∞ (affineLocalMapExpression c h d)
        (affineLocalMapDomain c h d) := by
      apply hd.1.1.comp
      · apply hh.1.comp
        · exact hc.1.2.mono (fun z hz ↦ hz.1.1)
        · exact fun z hz ↦ hz.1.2
      · exact fun z hz ↦ hz.2
    exact hcd.mdifferentiableOn (by simp)
  have hne : ∀ z ∈ affineLocalMapDomain c h d,
      deriv (affineLocalMapExpression c h d) z ≠ 0 := by
    let e := (c.symm.trans h).trans d
    have hinv : ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ∞ e.symm e.target := by
      apply hc.1.1.comp
      · apply hh.2.comp
        · exact hd.1.2.mono (fun z hz ↦ hz.1)
        · exact fun z hz ↦ hz.2.1
      · exact fun z hz ↦ hz.2.2
    have hinvd : DifferentiableOn ℂ e.symm e.target :=
      mdifferentiableOn_iff_differentiableOn.mp (hinv.mdifferentiableOn (by simp))
    intro z hz
    have hforward := (hdiff.differentiableAt (hΩ.mem_nhds hz)).hasDerivAt
    have hback := (hinvd.differentiableAt
      (e.open_target.mem_nhds (e.map_source hz))).hasDerivAt
    have hchain := hback.comp z hforward
    have hprod : deriv e.symm (e z) * deriv (affineLocalMapExpression c h d) z = 1 := by
      exact (hchain.congr_of_eventuallyEq (Filter.EventuallyEq.symm (e.eventually_left_inverse hz))).unique
        (hasDerivAt_id z)
    exact fun hzero ↦ by simp [hzero] at hprod
  have hAffineZero : (∃ a : ComplexAffineTransformation,
      ∀ᶠ z in 𝓝 (c x), affineLocalMapExpression c h d z = a.apply z) →
      schwarzianQuadraticAt c h d x = 0 := by
    rintro ⟨a, ha⟩
    let F : ℂ → ℂ := affineLocalMapExpression c h d
    have he : F =ᶠ[𝓝 (c x)] (fun z ↦ a.apply z) := ha
    have h1 : deriv F (c x) = a.slope := by
      rw [he.deriv_eq]
      simp [ComplexAffineTransformation.apply]
    have h2 : deriv (deriv F) (c x) = 0 := by
      rw [he.deriv.deriv_eq]
      simp [ComplexAffineTransformation.apply]
    have h3 : deriv (deriv (deriv F)) (c x) = 0 := by
      rw [he.deriv.deriv.deriv_eq]
      simp [ComplexAffineTransformation.apply]
    simp [F, schwarzianQuadraticAt, schwarzian, h1, h2, h3]
  have hScalarChain : ∀ (g : OpenPartialHomeomorph L₁ L₂)
      (e : OpenPartialHomeomorph L₂ ℂ), IsHolomorphicCurveLocalMap g →
      e ∈ ComplexAffineStructure.maximalAtlas L₂ A₂ →
      h x ∈ g.source → g (h x) ∈ e.source →
      schwarzian (affineLocalMapExpression c (h.trans g) e) (c x) =
        schwarzian (affineLocalMapExpression c h d) (c x) +
        schwarzian (affineLocalMapExpression d g e) (d (h x)) *
          deriv (affineLocalMapExpression c h d) (c x) ^ 2 := by
    intro g e hgg he hxg hxe
    let F := affineLocalMapExpression c h d
    let G := affineLocalMapExpression d g e
    let U := affineLocalMapDomain c h d
    let V := affineLocalMapDomain d g e
    have hV : IsOpen V := ((d.symm.trans g).trans e).open_source
    have hG : DifferentiableOn ℂ G V := by
      apply mdifferentiableOn_iff_differentiableOn.mp
      have hcd : ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ∞ G V := by
        apply he.1.1.comp
        · apply hgg.1.comp
          · exact hd.1.2.mono (fun z hz ↦ hz.1.1)
          · exact fun z hz ↦ hz.1.2
        · exact fun z hz ↦ hz.2
      exact hcd.mdifferentiableOn (by simp)
    have hGne : deriv G (d (h x)) ≠ 0 := by
      let q := (d.symm.trans g).trans e
      have hinv : ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ∞ q.symm q.target := by
        apply hd.1.1.comp
        · apply hgg.2.comp
          · exact he.1.2.mono (fun z hz ↦ hz.1)
          · exact fun z hz ↦ hz.2.1
        · exact fun z hz ↦ hz.2.2
      have hy : d (h x) ∈ V := by
        change (d (h x) ∈ d.target ∧ d.symm (d (h x)) ∈ g.source) ∧
          g (d.symm (d (h x))) ∈ e.source
        simpa [d.left_inv hxd] using And.intro (And.intro (d.map_source hxd) hxg) hxe
      have hinvd : DifferentiableOn ℂ q.symm q.target :=
        mdifferentiableOn_iff_differentiableOn.mp (hinv.mdifferentiableOn (by simp))
      have hforward := (hG.differentiableAt (hV.mem_nhds hy)).hasDerivAt
      have hback := (hinvd.differentiableAt
        (q.open_target.mem_nhds (q.map_source hy))).hasDerivAt
      have hp : deriv q.symm (q (d (h x))) * deriv G (d (h x)) = 1 := by
        exact ((hback.comp (d (h x)) hforward).congr_of_eventuallyEq
          (Filter.EventuallyEq.symm (q.eventually_left_inverse hy))).unique
          (hasDerivAt_id (d (h x)))
      exact fun hzero ↦ by simp [hzero] at hp
    have hzU : c x ∈ U := by
      change (c x ∈ c.target ∧ c.symm (c x) ∈ h.source) ∧ h (c.symm (c x)) ∈ d.source
      simpa [c.left_inv hxc] using And.intro (And.intro (c.map_source hxc) hxh) hxd
    have hFx : F (c x) = d (h x) := by
      simp [F, affineLocalMapExpression, c.left_inv hxc]
    have hzV : F (c x) ∈ V := by
      rw [hFx]
      change (d (h x) ∈ d.target ∧ d.symm (d (h x)) ∈ g.source) ∧
        g (d.symm (d (h x))) ∈ e.source
      simpa [d.left_inv hxd] using And.intro (And.intro (d.map_source hxd) hxg) hxe
    let W := U ∩ F ⁻¹' V
    have hW : IsOpen W := hdiff.continuousOn.isOpen_inter_preimage hΩ hV
    have hzW : c x ∈ W := ⟨hzU, hzV⟩
    have hcomp := Analysis.Complex.schwarzian_chain_rule (F := F) (G := G) hW hV
      (hdiff.mono inter_subset_left) hG (fun z hz ↦ hz.2) hzW
      (hne (c x) hzU) (by simpa [hFx] using hGne)
    have heq : affineLocalMapExpression c (h.trans g) e =ᶠ[𝓝 (c x)] G ∘ F := by
      filter_upwards [hΩ.mem_nhds hzU] with z hz
      change e (g (h (c.symm z))) = e (g (d.symm (d (h (c.symm z)))))
      rw [d.left_inv hz.2]
    change schwarzian (affineLocalMapExpression c (h.trans g) e) (c x) =
      schwarzian F (c x) + schwarzian G (d (h x)) * deriv F (c x) ^ 2
    rw [hFx] at hcomp
    simpa only [schwarzian, heq.deriv_eq, heq.deriv.deriv_eq,
      heq.deriv.deriv.deriv_eq] using hcomp
  refine ⟨hΩ, hdiff, hne, hAffineZero, ?_⟩
  intro g e hg he hxg hxe
  have hs := hScalarChain g e hg he hxg hxe
  refine ⟨hs, ?_⟩
  intro v
  let F := affineLocalMapExpression c h d
  have hz : c x ∈ affineLocalMapDomain c h d := by
    change (c x ∈ c.target ∧ c.symm (c x) ∈ h.source) ∧ h (c.symm (c x)) ∈ d.source
    simpa [c.left_inv hxc] using And.intro (And.intro (c.map_source hxc) hxh) hxd
  have hF := (hdiff.differentiableAt (hΩ.mem_nhds hz)).mdifferentiableAt
  have hcD := ((hc.1.1 x hxc).contMDiffAt (c.open_source.mem_nhds hxc)).mdifferentiableAt
    (by simp : (∞ : ℕ∞ω) ≠ 0)
  have hhD := ((hh.1 x hxh).contMDiffAt (h.open_source.mem_nhds hxh)).mdifferentiableAt
    (by simp : (∞ : ℕ∞ω) ≠ 0)
  have hdD := ((hd.1.1 (h x) hxd).contMDiffAt (d.open_source.mem_nhds hxd)).mdifferentiableAt
    (by simp : (∞ : ℕ∞ω) ≠ 0)
  have hEq : F ∘ c =ᶠ[𝓝 x] d ∘ h := by
    filter_upwards [c.open_source.mem_nhds hxc] with y hy
    simp [F, affineLocalMapExpression, c.left_inv hy]
  have hD := congrArg (fun T ↦ T v)
    (hEq.mfderiv_eq (I := complexModel 1) (I' := 𝓘(ℂ)))
  rw [mfderiv_comp x hF hcD, mfderiv_comp x hdD hhD, mfderiv_eq_fderiv] at hD
  change (fderiv ℂ F (c x)) (mfderiv (complexModel 1) 𝓘(ℂ) c x v) =
    (mfderiv (complexModel 1) 𝓘(ℂ) d (h x)
      (mfderiv (complexModel 1) (complexModel 1) h x v) : ℂ) at hD
  rw [fderiv_eq_deriv_mul] at hD
  let vc : ℂ := mfderiv (complexModel 1) 𝓘(ℂ) c x v
  let vd : ℂ := mfderiv (complexModel 1) 𝓘(ℂ) d (h x)
    (mfderiv (complexModel 1) (complexModel 1) h x v)
  change deriv F (c x) * vc = vd at hD
  change schwarzian (affineLocalMapExpression c (h.trans g) e) (c x) * (vc * vc) =
    schwarzian (affineLocalMapExpression c h d) (c x) * (vc * vc) +
      schwarzian (affineLocalMapExpression d g e) (d (h x)) * (vd * vd)
  rw [hs, ← hD]
  dsimp only [F]
  ring

end HolomorphicAnosov.Ghys
