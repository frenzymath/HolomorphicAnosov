import HolomorphicAnosov.Geometry.ComplexMDerivativeRealification
import HolomorphicAnosov.Geometry.HermitianMetricVolumeDefinitions
import Mathlib.Geometry.Manifold.ContMDiff.Atlas

/-! This file identifies paired real tangent frames obtained from compatible complex charts. -/


open scoped ContDiff
namespace HolomorphicAnosov
universe u

set_option backward.isDefEq.respectTransparency false in
/-- On its actual target, a compatible chart's real paired inverse frame is the realification of its complex inverse frame and its multiples by i. (Demailly, VI §4.) -/
theorem hermitian_paired_chart_frame {d : ℕ} {X : Type u}
    [TopologicalSpace X] [ChartedSpace (ComplexModel d) X]
    [IsManifold (complexModel d) ∞ X]
    (e : OpenPartialHomeomorph X (ComplexModel d))
    (he : e ∈ IsManifold.maximalAtlas (complexModel d) ∞ X)
    (z : ComplexModel d) (hz : z ∈ e.target) (i : ComplexPairedIndex d) :
    realTangentPairedChartFrame e z i = complexTangentToReal d (e.symm z)
      (if i.2 = 0 then hermitianTangentChartFrame e z i.1
       else Complex.I • hermitianTangentChartFrame e z i.1) := by
  have hf : MDifferentiableAt (complexModel d) (complexModel d) e.symm z :=
    ((contMDiffOn_symm_of_mem_maximalAtlas he).mdifferentiableOn (by simp)).mdifferentiableAt
      (e.open_target.mem_nhds hz)
  unfold realTangentPairedChartFrame hermitianTangentChartFrame
  let c : TangentSpace (complexModel d) z ≃L[ℂ] ComplexModel d :=
    NormedSpace.fromTangentSpace z
  change mfderiv (realModel d) (realModel d) e.symm z
      (complexTangentToReal d z (c.symm
        (Pi.single i.1 (if i.2 = 0 then 1 else Complex.I)))) = _
  rw [mfderiv_complex_to_real hf]
  apply congrArg (complexTangentToReal d (e.symm z))
  split_ifs with hi
  · rfl
  · have hp : Pi.single i.1 Complex.I = Complex.I • (Pi.single i.1 (1 : ℂ)) := by
      ext j
      by_cases hj : j = i.1 <;> simp [hj]
    rw [hp, map_smul, map_smul]

end HolomorphicAnosov
