import HolomorphicAnosov.Geometry.RealTangentTopForm
import HolomorphicAnosov.Geometry.BiholomorphToReal
import Mathlib.Geometry.Manifold.ContMDiff.Atlas

open scoped ContDiff
open Set
namespace HolomorphicAnosov
universe u
variable {d : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel d) X]

/-- Pullback by a biholomorphism preserves smooth positive real top forms. (Demailly, I (1.13), p.
10) -/
theorem positive_topForm_biholomorph_pullback [IsManifold (complexModel d) ∞ X]
    (F : Biholomorph d d X X) (ν : RealTangentTopForm d X)
    (hν : IsSmoothPositiveRealTangentTopForm ν) :
    IsSmoothPositiveRealTangentTopForm (realTangentTopFormPullback F ν) := by
  intro e he
  let e' := F.symm.toHomeomorph.toOpenPartialHomeomorph.trans e
  have het : e'.target = e.target := by
    ext z
    simp [e']
  have he' : e' ∈ IsManifold.maximalAtlas (complexModel d) ∞ X := by
    apply e'.mem_maximalAtlas_of_contMDiffOn
    · exact (contMDiffOn_of_mem_maximalAtlas he).comp
        F.symm.contMDiff.contMDiffOn (fun x hx ↦ hx.2)
    · exact F.contMDiff.comp_contMDiffOn
        ((contMDiffOn_symm_of_mem_maximalAtlas he).mono (by rw [het]))
  have hcoeff : Set.EqOn
      (realTangentTopFormChartCoefficient (realTangentTopFormPullback F ν) e)
      (realTangentTopFormChartCoefficient ν e') e.target := by
    intro z hz
    have hc := contMDiffAt_symm_of_mem_maximalAtlas he hz
    have hr : ContMDiffAt (realModel d) (realModel d) ∞ e.symm z := by
      obtain ⟨hc, hd⟩ := contMDiffAt_iff.mp hc
      exact contMDiffAt_iff.mpr ⟨hc, hd.restrict_scalars ℝ⟩
    change ν (F (e.symm z))
      (fun i ↦ mfderiv (realModel d) (realModel d) F (e.symm z)
        (mfderiv (realModel d) (realModel d) e.symm z
          ((NormedSpace.fromTangentSpace z).symm
            (Pi.single i.1 (if i.2 = 0 then 1 else Complex.I))))) =
      ν (F (e.symm z))
        (fun i ↦ mfderiv (realModel d) (realModel d) (F ∘ e.symm) z
          ((NormedSpace.fromTangentSpace z).symm
            (Pi.single i.1 (if i.2 = 0 then 1 else Complex.I))))
    have hF : MDifferentiable (realModel d) (realModel d) F :=
      F.toReal.contMDiff.mdifferentiable (by simp)
    rw [mfderiv_comp z (hF _)
      (hr.mdifferentiableAt (by simp))]
    rfl
  refine ⟨?_, ?_⟩
  · exact ((het ▸ (hν e' he').1)).congr hcoeff
  · intro z hz
    rw [hcoeff hz]
    exact (hν e' he').2 z (het.symm ▸ hz)

end HolomorphicAnosov

