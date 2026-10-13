import HolomorphicAnosov.SurfaceTorusSupport.ProjectiveActionHolomorphic
import HolomorphicAnosov.Geometry.ProjectiveFixedInfinityAffine
import HolomorphicAnosov.Analysis.Complex.ProjectiveDeveloping.Helpers.ProjectiveFiniteNeInfinity
import Mathlib.GroupTheory.GroupAction.Primitive

noncomputable section
open Set Filter Topology IsManifold
open scoped ContDiff Manifold
namespace HolomorphicAnosov

/-- The standard ratio chart, normalized at a chosen pole, gives a holomorphic coordinate on the
complement of any point of CP¹. (Demailly, V §15.A, p. 277; Ghys, p. 598) -/
theorem projective_pole_affine_chart (pole : ComplexProjectiveLine) :
    ∃ m : Matrix.ProjectiveSpecialLinearGroup (Fin 2) ℂ,
      m • pole = complexProjectiveLineInfinity ∧
    ∃ q : OpenPartialHomeomorph ComplexProjectiveLine ℂ,
      q.source = {pole}ᶜ ∧ q.target = Set.univ ∧
      ContMDiffOn (complexModel 1) 𝓘(ℂ) ∞ q q.source ∧
      ContMDiffOn 𝓘(ℂ) (complexModel 1) ∞ q.symm q.target ∧
      (∀ z, q z = complexProjectiveLineChartFun 1 (m • z) 0) := by
  obtain ⟨m, hm⟩ := MulAction.exists_smul_eq
    (Matrix.ProjectiveSpecialLinearGroup (Fin 2) ℂ) pole complexProjectiveLineInfinity
  let H : ComplexProjectiveLine ≃ₜ ComplexProjectiveLine :=
    { toEquiv :=
        { toFun := fun z ↦ m • z
          invFun := fun z ↦ m⁻¹ • z
          left_inv := fun z ↦ inv_smul_smul m z
          right_inv := fun z ↦ smul_inv_smul m z }
      continuous_toFun := (projective_special_linear_action_contMDiff m).continuous
      continuous_invFun := (projective_special_linear_action_contMDiff m⁻¹).continuous }
  let e := ContinuousLinearEquiv.funUnique (Fin 1) ℂ ℂ
  let q := (H.toOpenPartialHomeomorph.trans (complexProjectiveLineChart 1)).trans
    e.toHomeomorph.toOpenPartialHomeomorph
  have hsource : (complexProjectiveLineChart 1).source = {complexProjectiveLineInfinity}ᶜ := by
    ext z
    constructor
    · intro hz heq
      subst z
      have hh := projective_left_inv 1 complexProjectiveLineInfinity hz
      exact Ghys.developing_finite_ne_infinity _ (by
        convert hh using 1
        congr 1
)
    · intro hz
      by_contra hn
      exact hz (Ghys.developing_eq_infinity_of_not_finite_source z hn)
  refine ⟨m, hm, q, ?_, ?_, ?_, ?_, fun _ ↦ rfl⟩
  · ext z
    change (z ∈ Set.univ ∧ H z ∈ (complexProjectiveLineChart 1).source) ∧
      (complexProjectiveLineChart 1) (H z) ∈ Set.univ ↔ z ≠ pole
    simp only [Set.mem_univ, true_and, and_true, hsource, Set.mem_compl_iff,
      Set.mem_singleton_iff]
    exact not_congr ⟨fun h ↦ (MulAction.injective m) (h.trans hm.symm), fun h ↦ h ▸ hm⟩
  · ext z
    change z ∈ Set.univ ∧ e.symm z ∈ (complexProjectiveLineChart 1).target ∧
      (complexProjectiveLineChart 1).symm (e.symm z) ∈ Set.univ ↔ z ∈ Set.univ
    simp [complexProjectiveLineChart]
  · intro z hz
    change ContMDiffWithinAt (complexModel 1) 𝓘(ℂ) ∞
      (e ∘ (complexProjectiveLineChart 1) ∘ H) q.source z
    apply e.contDiff.contMDiff.contMDiffAt.comp_contMDiffWithinAt
    apply ((contMDiffOn_of_mem_maximalAtlas (IsManifold.subset_maximalAtlas
      (show complexProjectiveLineChart 1 ∈ atlas (ComplexModel 1) ComplexProjectiveLine from ⟨1, rfl⟩))).contMDiffAt ?_).comp_contMDiffWithinAt
    · exact (projective_special_linear_action_contMDiff m z).contMDiffWithinAt
    · exact (complexProjectiveLineChart 1).open_source.mem_nhds hz.1.2
  · intro z hz
    change ContMDiffWithinAt 𝓘(ℂ) (complexModel 1) ∞
      (H.symm ∘ (complexProjectiveLineChart 1).symm ∘ e.symm) q.target z
    apply (projective_special_linear_action_contMDiff m⁻¹ _).comp_contMDiffWithinAt
    apply ((contMDiffOn_symm_of_mem_maximalAtlas (IsManifold.subset_maximalAtlas
      (show complexProjectiveLineChart 1 ∈ atlas (ComplexModel 1) ComplexProjectiveLine from ⟨1, rfl⟩))).contMDiffAt ?_).comp_contMDiffWithinAt
    · exact e.symm.contDiff.contMDiff.contMDiffAt.contMDiffWithinAt
    · exact (complexProjectiveLineChart 1).open_target.mem_nhds (by trivial)
end HolomorphicAnosov

namespace HolomorphicAnosov
/-- A holomorphic chart from the whole source onto a punctured projective line, composed with a
holomorphic chart from that complement onto ℂ, gives a biholomorphism. (Ghys, p. 598) -/
theorem projective_pole_coordinate
    {L : Type*} [TopologicalSpace L] [ChartedSpace (ComplexModel 1) L]
    (o : ComplexProjectiveLine) (e : OpenPartialHomeomorph L ComplexProjectiveLine)
    (q : OpenPartialHomeomorph ComplexProjectiveLine ℂ)
    (hes : e.source = Set.univ) (het : e.target = {o}ᶜ)
    (hqs : q.source = {o}ᶜ) (hqt : q.target = Set.univ)
    (he : ContMDiffOn (complexModel 1) (complexModel 1) ∞ e e.source)
    (hei : ContMDiffOn (complexModel 1) (complexModel 1) ∞ e.symm e.target)
    (hq : ContMDiffOn (complexModel 1) 𝓘(ℂ) ∞ q q.source)
    (hqi : ContMDiffOn 𝓘(ℂ) (complexModel 1) ∞ q.symm q.target) :
    ∃ H : Diffeomorph (complexModel 1) 𝓘(ℂ) L ℂ ∞,
      ∀ z, H z = q (e z) := by
  let c := e.trans q
  have hs : c.source = Set.univ := by
    ext z
    change z ∈ e.source ∧ e z ∈ q.source ↔ z ∈ Set.univ
    have hz : z ∈ e.source := hes.symm ▸ Set.mem_univ z
    have hez : e z ∈ q.source := (het.trans hqs.symm) ▸ e.map_source hz
    simp only [hz, hez, and_self, Set.mem_univ]
  have ht : c.target = Set.univ := by
    ext z
    change z ∈ q.target ∧ q.symm z ∈ e.target ↔ z ∈ Set.univ
    have hz : z ∈ q.target := hqt.symm ▸ Set.mem_univ z
    have hez : q.symm z ∈ e.target := (hqs.trans het.symm) ▸ q.map_target hz
    simp only [hz, hez, and_self, Set.mem_univ]
  let H := c.toHomeomorphOfSourceEqUnivTargetEqUniv hs ht
  refine ⟨{ toEquiv := H.toEquiv, contMDiff_toFun := ?_, contMDiff_invFun := ?_ },
    fun _ ↦ rfl⟩
  · apply contMDiffOn_univ.mp
    exact hq.comp (hes ▸ he) (fun z hz ↦ by
      change e z ∈ q.source
      rw [hqs, ← het]
      exact e.map_source (hes.symm ▸ hz))
  · apply contMDiffOn_univ.mp
    exact hei.comp (hqt ▸ hqi) (fun z hz ↦ by
      change q.symm z ∈ e.target
      rw [het, ← hqs]
      exact q.map_target (hqt.symm ▸ hz))
end HolomorphicAnosov

namespace HolomorphicAnosov
/-- A projectively equivariant developing map whose range is the complement of one point has affine
transformations after pole normalization. (Ghys, p. 598) -/
theorem projective_common_pole_affine_formula
    {E G : Type*} (D : E → ComplexProjectiveLine) (A : G → E ≃ E)
    (ρ : G → Matrix.ProjectiveSpecialLinearGroup (Fin 2) ℂ)
    (o : ComplexProjectiveLine) (hrange : Set.range D = {o}ᶜ)
    (hequiv : ∀ g x, D (A g x) = ρ g • D x)
    (m : Matrix.ProjectiveSpecialLinearGroup (Fin 2) ℂ)
    (hm : m • o = complexProjectiveLineInfinity)
    (q : ComplexProjectiveLine → ℂ)
    (hq : ∀ z, q z = complexProjectiveLineChartFun 1 (m • z) 0) :
    ∀ g : G, ∃ a b : ℂ, ∀ x,
      q (D (A g x)) = a * q (D x) + b := by
  have hfix (g : G) : ρ g • o = o := by
    by_contra hn
    have hr : ρ g • o ∈ Set.range D := by rw [hrange]; exact hn
    obtain ⟨x, hx⟩ := hr
    obtain ⟨y, rfl⟩ := (A g).surjective x
    have heq : D y = o := (MulAction.injective (ρ g)) ((hequiv g y).symm.trans hx)
    have hy : D y ∈ {o}ᶜ := hrange ▸ Set.mem_range_self y
    exact hy heq
  have hconj (g : G) :
      (m * ρ g * m⁻¹) • complexProjectiveLineInfinity = complexProjectiveLineInfinity := by
    rw [← hm, mul_smul, mul_smul, inv_smul_smul, hfix, hm]
  intro g
  obtain ⟨a, b, hab⟩ := projective_fixed_infinity_chart_affine (m * ρ g * m⁻¹) (hconj g)
  refine ⟨a, b, fun x ↦ ?_⟩
  have hx : m • D x ≠ complexProjectiveLineInfinity := by
    intro h
    have hh := (MulAction.injective m) (h.trans hm.symm)
    have hx : D x ∈ {o}ᶜ := hrange ▸ Set.mem_range_self x
    exact hx hh
  have h := hab (m • D x) hx
  simpa only [hq, hequiv, mul_smul, inv_smul_smul] using h
end HolomorphicAnosov
