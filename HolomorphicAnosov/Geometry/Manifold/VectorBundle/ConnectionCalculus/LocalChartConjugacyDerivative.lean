import HolomorphicAnosov.Geometry.BiholomorphToReal
import Mathlib.Geometry.Manifold.MFDeriv.Atlas

open Set _root_.Topology TopologicalSpace
open scoped Manifold ContDiff Classical
attribute [local instance] HolomorphicAnosov.complex_isManifold_real

noncomputable section
namespace HolomorphicAnosov.ConnectionCalculus
universe u
variable {d : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel d) X] [IsManifold (complexModel d) ∞ X]

omit [IsManifold (complexModel d) ∞ X] in
/-- The manifold derivative of a local coordinate conjugacy is the composition of the target chart
derivative, map derivative, and source inverse-chart derivative. -/
theorem local_chart_conjugacy_mfderiv
    (f : Biholomorph d d X X)
    (c c' : OpenPartialHomeomorph X (ComplexModel d))
    (F : ComplexModel d → ComplexModel d) (z : ComplexModel d)
    (hc : c ∈ IsManifold.maximalAtlas (complexModel d) ∞ X)
    (hc' : c' ∈ IsManifold.maximalAtlas (complexModel d) ∞ X)
    (hz : z ∈ c.target)
    (hcz : f (c.symm z) ∈ c'.source)
    (hlocal : F =ᶠ[𝓝 z] (c' ∘ f ∘ c.symm)) :
    mfderiv (realModel d) (realModel d) F z =
      (mfderiv (realModel d) (realModel d) c' (f (c.symm z))).comp
        ((mfderiv (realModel d) (realModel d) f (c.symm z)).comp
          (mfderiv (realModel d) (realModel d) c.symm z)) := by
  have hcs : MDifferentiableAt (realModel d) (realModel d) c.symm z := by
    obtain ⟨hcont, hreg⟩ := contMDiffAt_iff.mp
      (contMDiffAt_symm_of_mem_maximalAtlas hc hz)
    exact (contMDiffAt_iff.mpr ⟨hcont, hreg.restrict_scalars ℝ⟩).mdifferentiableAt (by simp)
  have hcf : MDifferentiableAt (realModel d) (realModel d) f (c.symm z) :=
    f.toReal.contMDiff.mdifferentiable (by simp) _
  have hcc' : MDifferentiableAt (realModel d) (realModel d) c' (f (c.symm z)) := by
    obtain ⟨hcont, hreg⟩ := contMDiffAt_iff.mp
      (contMDiffAt_of_mem_maximalAtlas hc' hcz)
    exact (contMDiffAt_iff.mpr ⟨hcont, hreg.restrict_scalars ℝ⟩).mdifferentiableAt (by simp)
  have hcomp : mfderiv (realModel d) (realModel d)
      ((c' : X → ComplexModel d) ∘ (f : X → X) ∘ c.symm) z =
      (mfderiv (realModel d) (realModel d) c' (f (c.symm z))).comp
        ((mfderiv (realModel d) (realModel d) f (c.symm z)).comp
          (mfderiv (realModel d) (realModel d) c.symm z)) := by
    have hcfcomp : MDifferentiableAt (realModel d) (realModel d)
        ((c' : X → ComplexModel d) ∘ (f : X → X)) (c.symm z) :=
      hcc'.comp _ hcf
    change mfderiv (realModel d) (realModel d)
      (((c' : X → ComplexModel d) ∘ (f : X → X)) ∘ c.symm) z = _
    rw [mfderiv_comp _ hcfcomp hcs, mfderiv_comp _ hcc' hcf]
    rfl
  simpa only [Function.comp_assoc] using HasMFDerivAt.mfderiv
    ((hcc'.hasMFDerivAt.comp z (hcf.hasMFDerivAt.comp z hcs.hasMFDerivAt)).congr_of_eventuallyEq_abuse hlocal)

end HolomorphicAnosov.ConnectionCalculus

