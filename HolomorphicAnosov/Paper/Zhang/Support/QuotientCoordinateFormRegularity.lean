import HolomorphicAnosov.Geometry.Manifold.VectorBundle.HolomorphicQuotientLineConnection
import HolomorphicAnosov.Geometry.Manifold.VectorBundle.HolomorphicTangentSubbundle
import HolomorphicAnosov.Geometry.Manifold.VectorBundle.HolomorphicQuotientTangentLine
import Mathlib.Geometry.Manifold.Algebra.Structures
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension

/-! Regularity of quotient one-forms in inverse-chart tangent coordinates. (Zhang, Lemma 2.4, p. 7;
Demailly, V §11, p. 267, §14 (14.1), p. 273) -/
noncomputable section
namespace HolomorphicAnosov.Paper.Zhang.TransverseParallelSupport
open Set TopologicalSpace Bundle
open scoped ContDiff Manifold
universe u

/-- The coordinate one-form obtained from a normalized holomorphic quotient frame, the quotient
projection, and the inverse-chart differential is complex smooth and real differentiable on the
chart/frame overlap. (Zhang, Lemma 2.4, p. 7; Demailly, V §11, p. 267, §14 (14.1), p. 273) -/
theorem quotient_coordinate_form_regularity
    {d : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel d) X]
    [IsManifold (complexModel d) ∞ X]
    (U : (x : X) → Submodule ℂ (TangentSpace (complexModel d) x)) {r : ℕ}
    (hU : IsHolomorphicTangentSubbundle r U) (hline : IsQuotientTangentLine U)
    (V : Opens X) (e : QuotientLineConnection.HolomorphicFrame U V)
    (c : OpenPartialHomeomorph X (ComplexModel d))
    (hc : c ∈ IsManifold.maximalAtlas (complexModel d) ∞ X)
    (θ : ComplexModel d → ComplexModel d →L[ℂ] ℂ)
    (hθ : ∀ z (hz : z ∈ c.target ∩ c.symm ⁻¹' (V : Set X)), ∀ v : ComplexModel d,
      θ z v = e.coordinate (c.symm z) hz.2
        (QuotientLineConnection.projection U (c.symm z)
          (mfderiv (complexModel d) (complexModel d) c.symm z
            ((NormedSpace.fromTangentSpace z).symm v)))) :
    ContDiffOn ℂ ∞ θ (c.target ∩ c.symm ⁻¹' (V : Set X)) ∧
      DifferentiableOn ℝ θ (c.target ∩ c.symm ⁻¹' (V : Set X)) := by
  classical
  have hregular : ContDiffOn ℂ ∞ θ (c.target ∩ c.symm ⁻¹' (V : Set X)) := by
    apply contDiffOn_clm_apply.mpr
    intro v z hz
    obtain ⟨D, hxD⟩ := exists_quotient_local_data U hU hline (c.symm z)
    obtain ⟨W, T, hW, hxW, hWV, hT, hTe⟩ := e.holomorphic (c.symm z) hz.2
    have hcs := contMDiffOn_symm_of_mem_maximalAtlas hc
    have hcz := hcs.contMDiffAt (c.open_target.mem_nhds hz.1)
    let tv : ComplexModel d → TangentBundle (complexModel d) X := fun w ↦
      ⟨c.symm w, mfderiv (complexModel d) (complexModel d) c.symm w
        ((NormedSpace.fromTangentSpace w).symm v)⟩
    have htv : ContMDiffAt (complexModel d) (complexModel d).tangent ∞ tv z := by
      have ht := hcs.contMDiffOn_tangentMapWithin (m := ∞) (by simp)
        c.open_target.uniqueMDiffOn
      have hconst : ContMDiff (complexModel d) (complexModel d).tangent ∞
          (fun w : ComplexModel d ↦
            (⟨w, (NormedSpace.fromTangentSpace w).symm v⟩ :
              TangentBundle (complexModel d) (ComplexModel d))) := by
        intro w
        exact contMDiffAt_vectorSpace_iff_contDiffAt.mpr contDiffAt_const
      have hcomp := ht.comp hconst.contMDiffOn (fun w hw ↦ hw)
      apply (hcomp.contMDiffAt (c.open_target.mem_nhds hz.1)).congr_of_eventuallyEq
      filter_upwards [c.open_target.mem_nhds hz.1] with w hw
      dsimp [tv, tangentMapWithin]
      rw [mfderivWithin_of_isOpen c.open_target hw]
    have hnum := (D.hscalar (tv z) hxD).comp z htv
    have hden := (D.hscalar ⟨c.symm z, T (c.symm z)⟩ hxD).comp z
      ((hT.contMDiffAt (hW.mem_nhds hxW)).comp z hcz)
    have hnonzero : D.θ (c.symm z) (T (c.symm z)) ≠ 0 := by
      rw [← D.apply_mk (c.symm z) hxD, hTe _ hxW]
      intro heq
      have hs : e.sectionValue (c.symm z) = 0 := (D.L _ hxD).injective (by simpa using heq)
      have hn := e.normalized (c.symm z) hz.2
      rw [hs, map_zero] at hn
      exact zero_ne_one hn
    have hratio := hnum.contDiffAt.div hden.contDiffAt hnonzero
    apply (hratio.congr_of_eventuallyEq ?_).contDiffWithinAt
    have hnb := hcz.continuousAt.preimage_mem_nhds
      ((D.V.isOpen.inter hW).mem_nhds ⟨hxD, hxW⟩)
    filter_upwards [c.open_target.mem_nhds hz.1, hnb] with w hw hwDW
    have hwV := hWV hwDW.2
    rw [hθ w ⟨hw, hwV⟩]
    dsimp only [Function.comp_def, tv, Pi.div_apply]
    rw [eq_div_iff (by
      rw [← D.apply_mk (c.symm w) hwDW.1, hTe _ hwDW.2]
      intro heq
      have hs : e.sectionValue (c.symm w) = 0 :=
        (D.L _ hwDW.1).injective (by simpa using heq)
      have hn := e.normalized (c.symm w) hwV
      rw [hs, map_zero] at hn
      exact zero_ne_one hn)]
    rw [← D.apply_mk (c.symm w) hwDW.1,
      ← D.apply_mk (c.symm w) hwDW.1, hTe _ hwDW.2]
    let a := QuotientLineConnection.projection U (c.symm w)
      (mfderiv (complexModel d) (complexModel d) c.symm w
        ((NormedSpace.fromTangentSpace w).symm v))
    have ha : (e.coordinate (c.symm w) hwV a) • e.sectionValue (c.symm w) = a := by
      apply (e.coordinate (c.symm w) hwV).injective
      simp [e.normalized]
    simpa only [map_smul, smul_eq_mul] using congrArg (D.L (c.symm w) hwDW.1) ha
  exact ⟨hregular, (hregular.differentiableOn (by simp)).restrictScalars ℝ⟩

end HolomorphicAnosov.Paper.Zhang.TransverseParallelSupport

