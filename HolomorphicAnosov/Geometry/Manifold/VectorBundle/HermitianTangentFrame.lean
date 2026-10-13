import HolomorphicAnosov.Geometry.HermitianTangentMetric
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

/-! Coordinate tangent frames associated with holomorphic charts are smooth on the underlying real
manifold (Demailly, I §3.C, p.23; II (3.3)–(3.5), pp.85–86; V Example 1.3, pp.253–254; Ghys, §2,
p.588). -/

open Bundle Set
open scoped ContDiff Manifold

namespace HolomorphicAnosov

noncomputable section

universe u

attribute [local instance] complex_isManifold_real

set_option backward.isDefEq.respectTransparency false in
/-- The tangent frame obtained by applying the inverse differential of a chart in the complex
maximal atlas to a standard coordinate vector is real smooth on the chart source. -/
theorem contMDiffOn_hermitianTangentChartFrame
    {d : ℕ} {X : Type u}
    [TopologicalSpace X] [ChartedSpace (ComplexModel d) X]
    [IsManifold (complexModel d) ∞ X]
    (e : OpenPartialHomeomorph X (ComplexModel d))
    (he : e ∈ IsManifold.maximalAtlas (complexModel d) ∞ X)
    (i : Fin d) :
    ContMDiffOn (realModel d) ((realModel d).prod 𝓘(ℝ, ComplexModel d)) ∞
      (fun x ↦ TotalSpace.mk'
        (E := fun x : X ↦ TangentSpace (complexModel d) x)
        (ComplexModel d) x (hermitianTangentChartFrame e (e x) i)) e.source := by
  have hs := contMDiffOn_symm_of_mem_maximalAtlas he
  have htm := hs.contMDiffOn_tangentMapWithin (m := ∞) (by simp)
    e.open_target.uniqueMDiffOn
  have hinput : ContMDiffOn (complexModel d) ((complexModel d).tangent) ∞
      (fun x ↦ (tangentBundleModelSpaceHomeomorph (complexModel d)).symm
        (e x, Pi.single i 1)) e.source :=
    contMDiff_tangentBundleModelSpaceHomeomorph_symm.comp_contMDiffOn
      ((contMDiffOn_of_mem_maximalAtlas he).prodMk_space contMDiffOn_const)
  have hc := htm.comp hinput (fun x hx ↦ e.map_source hx)
  have hc' : ContMDiffOn (complexModel d)
      ((complexModel d).prod 𝓘(ℂ, ComplexModel d)) ∞
      (fun x ↦ TotalSpace.mk'
        (E := fun x : X ↦ TangentSpace (complexModel d) x)
        (ComplexModel d) x (hermitianTangentChartFrame e (e x) i)) e.source := by
    apply hc.congr
    intro x hx
    simp only [Function.comp_apply, tangentBundleModelSpaceHomeomorph_coe_symm, tangentMapWithin]
    dsimp only [TotalSpace.toProd, Equiv.coe_fn_symm_mk]
    rw [mfderivWithin_of_mem_nhds (e.open_target.mem_nhds (e.map_source hx))]
    simp only [hermitianTangentChartFrame]
    apply TotalSpace.ext (e.left_inv hx).symm
    rfl
  intro x hx
  obtain ⟨hc, hd⟩ := contMDiffWithinAt_iff.mp (hc' x hx)
  exact contMDiffWithinAt_iff.mpr ⟨hc, hd.restrict_scalars ℝ⟩

end
end HolomorphicAnosov
