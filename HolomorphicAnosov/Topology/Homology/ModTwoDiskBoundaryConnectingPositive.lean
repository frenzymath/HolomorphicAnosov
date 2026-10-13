import HolomorphicAnosov.Topology.SingularSubspaceSubcomplex
import Mathlib.AlgebraicTopology.SingularHomology.HomotopyInvariance
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Module.ULift

/-! Hatcher, Algebraic Topology, Corollary 2.11 p.113, disk-pair dimension
shift in Theorem 2.13/Corollary 2.14 p.114, relative exact sequence pp.116–118,
and unchanged arbitrary-coefficient proofs p.153.
-/
open CategoryTheory CategoryTheory.Limits
namespace HolomorphicAnosov
noncomputable section

/-- The actual disk-boundary connecting map is invertible from relative degree
q+2 to ordinary boundary degree q+1, over the fixed mod-two coefficient object.

Source: Hatcher pp.113–118,153. The native closed disk is convex and contracts
to a point. Its positive singular homology therefore vanishes, using the prism
homotopy and the point chain calculation. Both ambient terms adjoining this
connecting map in the literal pair long exact sequence are in positive degrees,
so exactness makes the connecting map an isomorphism. The degree-one to reduced
zero comparison and quotient-sphere identification are not claimed here. -/
theorem modTwoDiskBoundaryConnectingPositive (d q : ℕ) :
    let D := {x : EuclideanSpace ℝ (Fin d) // ‖x‖ ≤ 1}
    let A : Set D := {x | ‖x.val‖ = 1}
    let P := singularSubspacePair (TopCat.of D) A
    let R0 : ModuleCat.{0} (ZMod 2) := ModuleCat.of (ZMod 2) (ULift.{0} (ZMod 2))
    IsIso (P.homologyδ R0 (q + 2) (q + 1)) := by
  dsimp only
  let E := EuclideanSpace ℝ (Fin d)
  let D := {x : E // ‖x‖ ≤ 1}
  let A : Set D := {x | ‖x.val‖ = 1}
  let P := singularSubspacePair (TopCat.of D) A
  let R0 : ModuleCat.{0} (ZMod 2) := ModuleCat.of (ZMod 2) (ULift.{0} (ZMod 2))
  have hcontract : ContractibleSpace D := by
    have : ContractibleSpace (Metric.closedBall (0 : E) 1) :=
      Metric.contractibleSpace_closedBall (by norm_num)
    have hset : Metric.closedBall (0 : E) 1 = {x : E | ‖x‖ ≤ 1} := by
      ext x
      change dist x 0 ≤ 1 ↔ ‖x‖ ≤ 1
      rw [show dist x 0 = ‖x‖ from dist_zero_right x]
    rw [hset] at this
    exact this
  let : ContractibleSpace D := hcontract
  obtain ⟨e⟩ := ContractibleSpace.hequiv_unit D
  have hz (n : ℕ) (hn : n ≠ 0) :
      IsZero ((TopCat.toSSet.obj (TopCat.of D)).homology R0 n) := by
    let F := (AlgebraicTopology.singularHomologyFunctor (ModuleCat (ZMod 2)) n).obj R0
    let i : F.obj (TopCat.of D) ≅ F.obj (TopCat.of Unit) :=
      { hom := F.map (TopCat.ofHom e.toFun)
        inv := F.map (TopCat.ofHom e.invFun)
        hom_inv_id := by
          rw [← Functor.map_comp]
          obtain ⟨H⟩ := e.left_inv
          exact (TopCat.Homotopy.congr_homologyMap_singularChainComplexFunctor
            H R0 n).trans (F.map_id _)
        inv_hom_id := by
          rw [← Functor.map_comp]
          obtain ⟨H⟩ := e.right_inv
          exact (TopCat.Homotopy.congr_homologyMap_singularChainComplexFunctor
            H R0 n).trans (F.map_id _) }
    exact IsZero.of_iso
      (AlgebraicTopology.isZero_singularHomologyFunctor_of_totallyDisconnectedSpace
        (ModuleCat (ZMod 2)) n R0 (TopCat.of Unit) hn) i
  change IsIso ((P.shortExact_chainComplexShortComplex R0).δ
    (q + 2) (q + 1) _)
  exact (P.shortExact_chainComplexShortComplex R0).isIso_δ
    (q + 2) (q + 1) (by simp) (hz (q + 2) (by omega)) (hz (q + 1) (by omega))

end
end HolomorphicAnosov
