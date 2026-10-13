import HolomorphicAnosov.Geometry.ComplexHolomorphicCompatibility
import HolomorphicAnosov.Geometry.ComplexTangent
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import Mathlib.MeasureTheory.Integral.CurveIntegral.Poincare

/-! Holomorphic primitives of closed coordinate one-forms and their manifold differentials. (Zhang,
Lemma 2.4, p. 7) -/

noncomputable section
namespace HolomorphicAnosov.Paper.Zhang.TransverseParallelSupport
open Set TopologicalSpace
open scoped ContDiff Manifold
attribute [local instance] HolomorphicAnosov.complex_isManifold_real
universe u

/-- A closed complex coordinate one-form on an open convex chart domain has a holomorphic radial
primitive whose manifold differential is the original one-form. (Zhang, Lemma 2.4, p. 7) -/
theorem closed_coordinate_form_primitive
    {d : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel d) X]
    [IsManifold (complexModel d) ∞ X]
    (α : (x : X) → TangentSpace (complexModel d) x →L[ℂ] ℂ)
    (c : OpenPartialHomeomorph X (ComplexModel d))
    (hc : c ∈ IsManifold.maximalAtlas (complexModel d) ∞ X)
    (B : Set (ComplexModel d)) (hBo : IsOpen B) (hBc : Convex ℝ B)
    (hBt : B ⊆ c.target) (z₀ : ComplexModel d) (hz₀ : z₀ ∈ B)
    (A : ComplexModel d → ComplexModel d →L[ℂ] ℂ)
    (hcoord : ∀ z ∈ B, ∀ v : ComplexModel d,
      A z v = α (c.symm z) (mfderiv (complexModel d) (complexModel d) c.symm z v))
    (hAd : DifferentiableOn ℝ A B)
    (hclosed : ∀ z ∈ B, ∀ v w : ComplexModel d,
      fderiv ℝ A z v w = fderiv ℝ A z w v) :
    let t : X → ℂ := fun x ↦ curveIntegral A (Path.segment z₀ (c x))
    ContMDiffOn (complexModel d) 𝓘(ℂ, ℂ) ∞ t (c.source ∩ c ⁻¹' B) ∧
      ∀ y ∈ c.source ∩ c ⁻¹' B, ∀ v : TangentSpace (complexModel d) y,
        tangentSpaceCastModel 𝓘(ℂ, ℂ) (t y)
          (mfderiv (complexModel d) 𝓘(ℂ, ℂ) t y v) = α y v := by
  let P := fun z ↦ curveIntegral A (Path.segment z₀ z)
  have hP (z) (hz : z ∈ B) : HasFDerivAt P (A z) z := by
    have hPw := hBc.hasFDerivWithinAt_curveIntegral_segment_of_hasFDerivWithinAt_symmetric
      (fun w hw ↦ ((hAd w hw).differentiableAt (hBo.mem_nhds hw)).hasFDerivAt.hasFDerivWithinAt)
      (fun w hw v _ v' _ ↦ hclosed w hw v v') hz₀ hz
    exact hPw.hasFDerivAt (hBo.mem_nhds hz)
  have hPd : DifferentiableOn ℂ P B := fun z hz ↦ (hP z hz).differentiableAt.differentiableWithinAt
  have hGd : DifferentiableOn ℂ (fun z : ComplexModel d ↦ (fun _ : Fin 1 ↦ P z)) B :=
    differentiableOn_pi.2 (fun _ ↦ hPd)
  have hGs := (complex_contDiffOn_iff_differentiableOn hBo).2 hGd
  have hPs : ContDiffOn ℂ ∞ P B := (contDiffOn_pi.1 hGs) 0
  constructor
  · exact hPs.contMDiffOn.comp
      ((contMDiffOn_of_mem_maximalAtlas hc).mono (fun y hy ↦ hy.1)) (fun y hy ↦ hy.2)
  · intro y hy v
    have hdc := (contMDiffAt_of_mem_maximalAtlas hc hy.1).mdifferentiableAt (by simp)
    have hdci := (contMDiffAt_symm_of_mem_maximalAtlas hc (hBt hy.2)).mdifferentiableAt
      (by simp)
    have hcomp := mfderiv_comp y hdci hdc
    have heq : (c.symm ∘ c : X → X) =ᶠ[nhds y] id := by
      filter_upwards [c.open_source.mem_nhds hy.1] with w hw
      exact c.left_inv hw
    rw [heq.mfderiv_eq, mfderiv_id] at hcomp
    have hPc := mfderiv_comp y (hP (c y) hy.2).differentiableAt.mdifferentiableAt hdc
    change tangentSpaceCastModel 𝓘(ℂ, ℂ) ((P ∘ c) y)
      (mfderiv (complexModel d) 𝓘(ℂ, ℂ) (P ∘ c) y v) = α y v
    rw [hPc, mfderiv_eq_fderiv, (hP (c y) hy.2).fderiv]
    change A (c y) (mfderiv (complexModel d) (complexModel d) c y v) = α y v
    refine (hcoord (c y) hy.2 (mfderiv (complexModel d) (complexModel d) c y v)).trans ?_
    rw [c.left_inv hy.1]
    have hcancel := congrArg (fun L ↦ L v) hcomp
    change v = mfderiv (complexModel d) (complexModel d) c.symm (c y)
      (mfderiv (complexModel d) (complexModel d) c y v) at hcancel
    exact congrArg (fun w : TangentSpace (complexModel d) y ↦ α y w) hcancel.symm

end HolomorphicAnosov.Paper.Zhang.TransverseParallelSupport
