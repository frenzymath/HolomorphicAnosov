import HolomorphicAnosov.Geometry.ConnectionChristoffelLocal.WholeChart
import HolomorphicAnosov.Geometry.SmoothAffineConnection
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.VectorField.Pullback
/-!
Whole-open charts preserve membership in the maximal smooth atlas. (Andrews, Prop. 8.3.1 and Ex.
8.3.2, p.74)
-/


open Set Bundle IsManifold Module TopologicalSpace
open scoped Manifold ContDiff Topology _root_.Topology
namespace HolomorphicAnosov
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
namespace ConnectionChristoffelLocal
omit [FiniteDimensional ℝ E] in
/-- A chart in the maximal smooth atlas of the whole open subtype induces a chart in the maximal
smooth atlas of `M`. -/
theorem wholeChart_mem_maximalAtlas
    (c : OpenPartialHomeomorph ((⊤ : Opens M)) E)
    (hc : c ∈ maximalAtlas 𝓘(ℝ, E) ∞ ((⊤ : Opens M))) :
    wholeChart c ∈ maximalAtlas 𝓘(ℝ, E) ∞ M := by
  apply OpenPartialHomeomorph.mem_maximalAtlas_of_contMDiffOn
  · intro p hp
    have hpc : (⟨p, mem_univ p⟩ : (⊤ : Opens M)) ∈ c.source := hp.2
    have hcAt := contMDiffAt_of_mem_maximalAtlas hc hpc
    have ha : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ (fun q : M ↦ c ⟨q, mem_univ q⟩) p :=
      (contMDiffAt_subtype_iff (U := ⊤) (x := ⟨p, mem_univ p⟩)).mp hcAt
    exact ha.contMDiffWithinAt
  · intro x hx
    have hxc : x ∈ c.target := hx.1
    have hs := contMDiffAt_symm_of_mem_maximalAtlas hc hxc
    exact ((contMDiff_subtype_val (I := 𝓘(ℝ, E)) (U := ⊤) (n := ∞)
      (c.symm x)).comp x hs).contMDiffWithinAt

end ConnectionChristoffelLocal
end
end HolomorphicAnosov
