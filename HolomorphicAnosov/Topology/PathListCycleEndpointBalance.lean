import HolomorphicAnosov.Topology.PathSingularChain
import HolomorphicAnosov.Topology.PathListBoundaryCoefficients
import HolomorphicAnosov.Topology.ListSumSingleCount
import Mathlib.Data.List.Count

noncomputable section
open CategoryTheory
universe u
namespace HolomorphicAnosov.Topology

/-- A positive finite path sum that is a native singular cycle has equal
incoming and outgoing occurrence counts at each point.
Source: Hatcher, Algebraic Topology, Theorem 2A.1 proof p.167. The boundary
coefficient formula makes the target and source unit-coordinate sums equal.
Evaluate at the constant zero-simplex of the chosen point; these coefficients
are the occurrence counts. Constant zero-simplexes distinguish points. -/
theorem pathList_cycle_endpoint_balance {X : Type u} [TopologicalSpace X]
    [DecidableEq X] (l : List (Σ x y : X, Path x y))
    (hc : ((integralSingularChains X).d 1 0)
      ((l.map (fun p ↦ pathSingularChain p.2.2)).sum) = 0) (v : X) :
    (l.map (fun p ↦ p.1)).count v = (l.map (fun p ↦ p.2.1)).count v := by
  classical
  have h := pathList_boundary_coefficients l
  rw [hc, map_zero] at h
  have he := (sub_eq_zero.mp h.symm)
  have hv := congrArg (fun f ↦ f (ContinuousMap.const (Convexity.StdSimplex ℝ (Fin 1)) v)) he
  rw [list_sum_single_count, list_sum_single_count] at hv
  have hi : Function.Injective (ContinuousMap.const (Convexity.StdSimplex ℝ (Fin 1)) :
      X → C(Convexity.StdSimplex ℝ (Fin 1), X)) := by
    intro a b hab
    exact congrArg (fun f : C(Convexity.StdSimplex ℝ (Fin 1), X) ↦ f default) hab
  have hv' : (((l.map (fun p ↦ p.2.1)).map (ContinuousMap.const (Convexity.StdSimplex ℝ (Fin 1)))).count
      (ContinuousMap.const (Convexity.StdSimplex ℝ (Fin 1)) v) : ULift.{u} ℤ) =
    (((l.map (fun p ↦ p.1)).map (ContinuousMap.const (Convexity.StdSimplex ℝ (Fin 1)))).count
      (ContinuousMap.const (Convexity.StdSimplex ℝ (Fin 1)) v) : ULift.{u} ℤ) := by
    simpa only [List.map_map, Function.comp_def, Nat.reduceAdd] using hv
  rw [List.count_map_of_injective _ _ hi, List.count_map_of_injective _ _ hi] at hv'
  have hd := congrArg ULift.down hv'
  exact_mod_cast hd.symm
end HolomorphicAnosov.Topology
