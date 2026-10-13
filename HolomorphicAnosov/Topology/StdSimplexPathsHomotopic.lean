import Mathlib.Geometry.Convex.ConvexSpace.Topology
import Mathlib.Topology.Homotopy.Path

open Convexity
universe u
namespace HolomorphicAnosov.Topology

/-- Two paths in a finite standard simplex with the same endpoints are
homotopic relative endpoints.
Source: Hatcher, Algebraic Topology, p.167, straight contraction inside a
triangle. Interpolate the barycentric weights linearly at each path parameter.
The weights stay nonnegative with sum one, vary continuously, and agree at
both endpoints throughout the homotopy. This works in every finite dimension. -/
theorem stdSimplex_paths_homotopic {ι : Type u} [Finite ι]
    {a b : StdSimplex ℝ ι} (p q : Path a b) : p.Homotopic q := by
  classical
  let F : unitInterval × unitInterval → StdSimplex ℝ ι := fun z ↦
    { weights := (1 - (z.1 : ℝ)) • (p z.2).weights + (z.1 : ℝ) • (q z.2).weights
      nonneg := by
        intro i
        exact add_nonneg (mul_nonneg (sub_nonneg.mpr z.1.property.2) ((p z.2).nonneg i))
          (mul_nonneg z.1.property.1 ((q z.2).nonneg i))
      total := by
        simp [Finsupp.sum_add_index, Finsupp.sum_smul_index, ← Finsupp.mul_sum] }
  refine ⟨{ toFun := F, continuous_toFun := ?_, map_zero_left := ?_, map_one_left := ?_, prop' := ?_ }⟩
  · apply (StdSimplex.isEmbedding_toFun_comp_weights ℝ ι).continuous_iff.2
    apply continuous_pi
    intro i
    dsimp [F]
    fun_prop
  · intro t
    apply StdSimplex.ext
    simp [F]
  · intro t
    apply StdSimplex.ext
    simp [F]
  · intro s t ht
    rcases ht with ht | ht
    · subst t
      apply StdSimplex.ext
      simp [F, ← add_smul]
    · have ht' : t = 1 := ht
      subst t
      apply StdSimplex.ext
      simp [F, ← add_smul]
end HolomorphicAnosov.Topology
