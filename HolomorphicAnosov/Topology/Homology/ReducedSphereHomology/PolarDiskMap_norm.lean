import HolomorphicAnosov.Topology.GoodPairCollapse
import HolomorphicAnosov.Topology.GoodPairReducedHomologyExactSequence
import HolomorphicAnosov.Topology.Homology.IntegralReducedSingularHomology
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.Convex.Contractible
import HolomorphicAnosov.Topology.Homology.ReducedSphereHomology.AppendEuclidean_norm_sq
import HolomorphicAnosov.Topology.Homology.ReducedSphereHomology.PolarDiskMap

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace HolomorphicAnosov.Topology.Homology

theorem polarDiskMap_norm (m : ℕ) (x : EuclideanSpace ℝ (Fin m)) :
    ‖polarDiskMap m x‖ = 1 := by
  have hfirst : (Real.pi * Real.sinc (Real.pi * ‖x‖)) ^ 2 * ‖x‖ ^ 2 =
      Real.sin (Real.pi * ‖x‖) ^ 2 := by
    by_cases hx : ‖x‖ = 0
    · simp [hx]
    · rw [Real.sinc_of_ne_zero (mul_ne_zero Real.pi_ne_zero hx)]
      field_simp
  have hn : ‖polarDiskMap m x‖ ^ 2 = 1 := by
    rw [polarDiskMap, appendEuclidean_norm_sq, norm_smul, Real.norm_eq_abs,
      mul_pow, sq_abs, hfirst]
    exact Real.sin_sq_add_cos_sq _
  nlinarith [norm_nonneg (polarDiskMap m x)]

end HolomorphicAnosov.Topology.Homology
