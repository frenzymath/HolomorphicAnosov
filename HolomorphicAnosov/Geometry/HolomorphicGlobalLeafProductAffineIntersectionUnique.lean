import HolomorphicAnosov.Geometry.ComplexHolomorphicCompatibility
import HolomorphicAnosov.Geometry.ComplexModel
import HolomorphicAnosov.Geometry.RegularHolomorphicFoliation
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace

namespace HolomorphicAnosov

open Set TopologicalSpace _root_.Topology
open scoped ContDiff Manifold

universe u v w

set_option autoImplicit false

/-- Complementary affine subspaces have the stated unique intersection.    Both projection components and all equality cases are derived in the original vector space. -/
theorem affine_intersection_unique {V : Type w}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (S U : Submodule ℝ V) (hSU : IsCompl S U) (a b : V) :
    ∃! y : V, y - a ∈ S ∧ y - b ∈ U := by
  let ps := S.projection U hSU
  let pu := U.projection S hSU.symm
  let y := ps b + pu a
  have hdec (z : V) : ps z + pu z = z :=
    Submodule.projection_add_projection_eq_self hSU z
  have hya : y - a = ps b - ps a := by
    dsimp [y]
    calc
      ps b + pu a - a = ps b + pu a - (ps a + pu a) :=
        congrArg (fun z ↦ ps b + pu a - z) (hdec a).symm
      _ = ps b - ps a := by abel
  have hyb : y - b = pu a - pu b := by
    dsimp [y]
    calc
      ps b + pu a - b = ps b + pu a - (ps b + pu b) :=
        congrArg (fun z ↦ ps b + pu a - z) (hdec b).symm
      _ = pu a - pu b := by abel
  refine ⟨y, ⟨?_, ?_⟩, ?_⟩
  · rw [hya]
    exact S.sub_mem (Submodule.projection_apply_mem hSU b)
      (Submodule.projection_apply_mem hSU a)
  · rw [hyb]
    exact U.sub_mem (Submodule.projection_apply_mem hSU.symm a)
      (Submodule.projection_apply_mem hSU.symm b)
  · intro z hz
    have hzpu : pu z = pu a := by
      have hh := Submodule.projection_apply_of_mem_right hSU.symm hz.1
      change pu (z - a) = 0 at hh
      rw [map_sub, sub_eq_zero] at hh
      exact hh
    have hzps : ps z = ps b := by
      have hh := Submodule.projection_apply_of_mem_right hSU hz.2
      change ps (z - b) = 0 at hh
      rw [map_sub, sub_eq_zero] at hh
      exact hh
    rw [← hdec z, hzps, hzpu]

