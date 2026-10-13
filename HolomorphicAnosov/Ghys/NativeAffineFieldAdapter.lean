import HolomorphicAnosov.Geometry.NativeLeafRebase
import HolomorphicAnosov.Geometry.ComplexMobiusPSLNormalization
import HolomorphicAnosov.Paper.Ghys.OrderedProjectiveProductDevelopment

noncomputable section
namespace HolomorphicAnosov.Ghys
open Set Filter _root_.Topology
open scoped ContDiff Manifold
attribute [local instance] complex_isManifold_real

/-- Combine an affine germ for one coordinate with native local constancy of the other. -/
theorem native_affine_field_of_transverse_germ
    {S : Type*} [MetricSpace S] [ChartedSpace (ComplexModel 2) S]
    [IsManifold (complexModel 2) ∞ S]
    (f : S ≃ₜ S) (P : RealTangentDistribution (realModel 2) S) (x : S)
    (L : NativeCompleteAffineAsymptoticLeaf f P x)
    (e : OpenPartialHomeomorph S (ComplexProjectiveLine × ComplexProjectiveLine))
    (vary other : (ComplexProjectiveLine × ComplexProjectiveLine) → ComplexProjectiveLine)
    (Q : S → ComplexProjectiveLine) (τ : S → ℂ) (R : ℂ → ComplexProjectiveLine)
    (hvary : ∀ z ∈ e.source, vary (e z) = Q z)
    (hother : ∀ z ∈ e.source, other (e z) = R (τ z))
    (hτ : ∀ z ∈ e.source, MDifferentiableAt (realModel 2) 𝓘(ℝ, ℂ) τ z)
    (hkill : ∀ z ∈ e.source, ∀ v ∈ P z,
      mfderiv (realModel 2) 𝓘(ℝ, ℂ) τ z v = 0) :
    letI := L.native.topology
    letI := L.complexCharts
    ∀ y : StableAsymptoticLeaf f x, y.val ∈ e.source →
      (∃ c ∈ ComplexAffineStructure.maximalAtlas _ L.affineStructure,
        y ∈ c.source ∧ ∃ g : ComplexMobiusTransformation,
          ∀ᶠ z in 𝓝 y, z ∈ c.source ∧
            Q z.val = g.apply (complexProjectiveLineFinite (c z))) →
      ∃ c ∈ ComplexAffineStructure.maximalAtlas _ L.affineStructure,
        y ∈ c.source ∧ ∃ g : Matrix.ProjectiveSpecialLinearGroup (Fin 2) ℂ,
          ∀ᶠ z in 𝓝 y, z ∈ c.source ∧ z.val ∈ e.source ∧
            vary (e z.val) = g • complexProjectiveLineFinite (c z) ∧
            other (e z.val) = other (e y.val) := by
  let := L.native.topology
  let := L.complexCharts
  intro y hy h
  obtain ⟨c, hc, hyc, g, hg⟩ := h
  obtain ⟨g', hg', _⟩ := complex_mobius_psl_normalization g
  obtain ⟨W, hWo, hyW, hWV, hW⟩ :=
    Theorem12PlaqueSupport.nativeAsymptoticLeaf_transverse_locally_constant
      (realModel 2) f P x L.native τ e.source e.open_source hτ hkill y hy
  refine ⟨c, hc, hyc, g', ?_⟩
  filter_upwards [hg, hWo.mem_nhds hyW] with z hzg hzW
  have hz := hWV hzW
  refine ⟨hzg.1, hz, ?_, ?_⟩
  · exact (hvary z.val hz).trans (hzg.2.trans (hg' _).symm)
  · rw [hother z.val hz, hother y.val hy, hW z hzW]


theorem native_stable_affine_field_of_transverse_germ
    {S : Type*} [MetricSpace S] [ChartedSpace (ComplexModel 2) S]
    [IsManifold (complexModel 2) ∞ S]
    (f : S ≃ₜ S) (P : RealTangentDistribution (realModel 2) S) (x : S)
    (L : NativeCompleteAffineAsymptoticLeaf f P x)
    (e : OpenPartialHomeomorph S (ComplexProjectiveLine × ComplexProjectiveLine))
    (Q : S → ComplexProjectiveLine) (τ : S → ℂ) (R : ℂ → ComplexProjectiveLine)
    (hvary : ∀ z ∈ e.source, (e z).1 = Q z)
    (hother : ∀ z ∈ e.source, (e z).2 = R (τ z))
    (hτ : ∀ z ∈ e.source, MDifferentiableAt (realModel 2) 𝓘(ℝ, ℂ) τ z)
    (hkill : ∀ z ∈ e.source, ∀ v ∈ P z,
      mfderiv (realModel 2) 𝓘(ℝ, ℂ) τ z v = 0) :
    letI := L.native.topology
    letI := L.complexCharts
    ∀ y : StableAsymptoticLeaf f x, y.val ∈ e.source →
      (∃ c ∈ ComplexAffineStructure.maximalAtlas _ L.affineStructure,
        y ∈ c.source ∧ ∃ g : ComplexMobiusTransformation,
          ∀ᶠ z in 𝓝 y, z ∈ c.source ∧
            Q z.val = g.apply (complexProjectiveLineFinite (c z))) →
      ∃ c ∈ ComplexAffineStructure.maximalAtlas _ L.affineStructure,
        y ∈ c.source ∧ ∃ g : Matrix.ProjectiveSpecialLinearGroup (Fin 2) ℂ,
          ∀ᶠ z in 𝓝 y, z ∈ c.source ∧ z.val ∈ e.source ∧
            (e z.val).1 = g • complexProjectiveLineFinite (c z) ∧
            (e z.val).2 = (e y.val).2 := by
  exact native_affine_field_of_transverse_germ f P x L e Prod.fst Prod.snd
    Q τ R hvary hother hτ hkill

theorem native_unstable_affine_field_of_transverse_germ
    {S : Type*} [MetricSpace S] [ChartedSpace (ComplexModel 2) S]
    [IsManifold (complexModel 2) ∞ S]
    (f : S ≃ₜ S) (P : RealTangentDistribution (realModel 2) S) (x : S)
    (L : NativeCompleteAffineAsymptoticLeaf f.symm P x)
    (e : OpenPartialHomeomorph S (ComplexProjectiveLine × ComplexProjectiveLine))
    (Q : S → ComplexProjectiveLine) (τ : S → ℂ) (R : ℂ → ComplexProjectiveLine)
    (hvary : ∀ z ∈ e.source, (e z).2 = Q z)
    (hother : ∀ z ∈ e.source, (e z).1 = R (τ z))
    (hτ : ∀ z ∈ e.source, MDifferentiableAt (realModel 2) 𝓘(ℝ, ℂ) τ z)
    (hkill : ∀ z ∈ e.source, ∀ v ∈ P z,
      mfderiv (realModel 2) 𝓘(ℝ, ℂ) τ z v = 0) :
    letI := L.native.topology
    letI := L.complexCharts
    ∀ y : UnstableAsymptoticLeaf f x, y.val ∈ e.source →
      (∃ c ∈ ComplexAffineStructure.maximalAtlas _ L.affineStructure,
        y ∈ c.source ∧ ∃ g : ComplexMobiusTransformation,
          ∀ᶠ z in 𝓝 y, z ∈ c.source ∧
            Q z.val = g.apply (complexProjectiveLineFinite (c z))) →
      ∃ c ∈ ComplexAffineStructure.maximalAtlas _ L.affineStructure,
        y ∈ c.source ∧ ∃ g : Matrix.ProjectiveSpecialLinearGroup (Fin 2) ℂ,
          ∀ᶠ z in 𝓝 y, z ∈ c.source ∧ z.val ∈ e.source ∧
            (e z.val).2 = g • complexProjectiveLineFinite (c z) ∧
            (e z.val).1 = (e y.val).1 := by
  exact native_affine_field_of_transverse_germ f.symm P x L e Prod.snd Prod.fst
    Q τ R hvary hother hτ hkill

end HolomorphicAnosov.Ghys

