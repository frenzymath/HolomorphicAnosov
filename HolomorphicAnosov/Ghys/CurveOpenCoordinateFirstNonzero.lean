import HolomorphicAnosov.Geometry.Manifold.OpenSubsetInclusionTangentG9
import HolomorphicAnosov.Ghys.LeafJetComplexManifold
import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace

/-! Nonvanishing of the first coefficient in an open holomorphic coordinate. (Ghys, §3 p.591;
Michor, §§1.1–1.3) -/
noncomputable section
namespace HolomorphicAnosov.Ghys
open Set Filter _root_.Topology
open scoped Manifold ContDiff
universe u
variable (L : Type u) [TopologicalSpace L] [ChartedSpace ℂ L]
variable [IsManifold 𝓘(ℂ) ∞ L]

omit [IsManifold 𝓘(ℂ) ∞ L] in
/-- A scalar function agreeing with a holomorphic coordinate on an open branch has nonzero first
coefficient on every admissible parametrization germ based in that branch. (Ghys, §3 p.591; Michor,
§§1.1–1.3) -/
theorem curveParamGerm_openCoordinate_first_ne_zero
    (U : TopologicalSpace.Opens L) (V : TopologicalSpace.Opens ℂ)
    (e : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) U V ∞) (φ : L → ℂ)
    (hφ : ∀ y : U, φ y.val = (e y).val)
    (γ : CurveParamGerm L) (hγ : curveGermBase L γ.1 ∈ U) :
    germFirst (γ.1.map φ) ≠ 0 := by
  let x : U := ⟨curveGermBase L γ.1, hγ⟩
  have hs : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ∞ (fun y : U ↦ φ y.val) :=
    (contMDiff_subtype_val.comp e.contMDiff).congr hφ
  have hp : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ∞ φ x.val :=
    contMDiffAt_subtype_iff.mp (hs.contMDiffAt (x := x))
  have he : Function.Bijective (mfderiv 𝓘(ℂ) 𝓘(ℂ) (e : U → V) x) :=
    (e.toOpenPartialHomeomorph_mdifferentiable (show (∞ : WithTop ℕ∞) ≠ 0 by simp)).mfderiv_bijective (by simp)
  have hv := openSubsetInclusion_mfderiv_bijective 𝓘(ℂ) V (e x)
  have hu := openSubsetInclusion_mfderiv_bijective 𝓘(ℂ) U x
  have hrestricted : Function.Injective
      (mfderiv 𝓘(ℂ) 𝓘(ℂ) (fun y : U ↦ φ y.val) x) := by
    have hfun : (fun y : U ↦ φ y.val) = (Subtype.val : V → ℂ) ∘ e := funext hφ
    rw [hfun, mfderiv_comp x
      (contMDiff_subtype_val.mdifferentiable (show (∞ : WithTop ℕ∞) ≠ 0 by simp) _)
      (e.mdifferentiable (show (∞ : WithTop ℕ∞) ≠ 0 by simp) x)]
    exact hv.injective.comp he.injective
  have hi : Function.Injective (mfderiv 𝓘(ℂ) 𝓘(ℂ) φ x.val) := by
    change Function.Injective (mfderiv 𝓘(ℂ) 𝓘(ℂ) (φ ∘ Subtype.val) x) at hrestricted
    rw [mfderiv_comp x (hp.mdifferentiableAt (show (∞ : WithTop ℕ∞) ≠ 0 by simp))
      (contMDiff_subtype_val.mdifferentiable (show (∞ : WithTop ℕ∞) ≠ 0 by simp) x)] at hrestricted
    exact Function.Injective.of_comp_right hrestricted (show Function.Surjective
      (mfderiv 𝓘(ℂ) 𝓘(ℂ) (Subtype.val : U → L) x) from hu.surjective)
  obtain ⟨g, hg0, hg, hgi, hge⟩ := γ.2
  have hb : x.val = g 0 := by
    change curveGermBase L γ.1 = g 0
    rw [← hge]
    rfl
  have hgd : g.MDifferentiable 𝓘(ℂ) 𝓘(ℂ) :=
    ⟨hg.mdifferentiableOn (by norm_num), hgi.mdifferentiableOn (by norm_num)⟩
  have hcomp : Function.Injective (mfderiv 𝓘(ℂ) 𝓘(ℂ) (φ ∘ g) 0) := by
    rw [mfderiv_comp 0 ((hb ▸ hp).mdifferentiableAt (show (∞ : WithTop ℕ∞) ≠ 0 by simp))
      ((hg.contMDiffAt (g.open_source.mem_nhds hg0)).mdifferentiableAt
        (show (∞ : WithTop ℕ∞) ≠ 0 by simp))]
    exact (hb ▸ hi).comp (hgd.mfderiv_bijective hg0).injective
  rw [mfderiv_eq_fderiv] at hcomp
  rw [← hge]
  change deriv (φ ∘ g) 0 ≠ 0
  intro hzero
  have hunit : (1 : ℂ) = 0 := hcomp (hzero.trans (map_zero _).symm)
  exact one_ne_zero hunit

end HolomorphicAnosov.Ghys
