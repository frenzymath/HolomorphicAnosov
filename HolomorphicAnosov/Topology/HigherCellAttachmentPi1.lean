import HolomorphicAnosov.Topology.CWOneSkeletonLoopApproximation
import HolomorphicAnosov.Topology.Pi1SurjectiveLoopCriterion
import HolomorphicAnosov.Topology.FiniteCompositionPi1
import HolomorphicAnosov.Topology.FiniteHigherCellAttachmentPi1
import Mathlib.Topology.CWComplex.Classical.Finite
import Mathlib.AlgebraicTopology.RelativeCellComplex.Basic
import Mathlib.Topology.Category.TopCat.Sphere

/-!
# Fundamental-group surjectivity after finitely many higher-cell attachments

Source: Hatcher, *Algebraic Topology*, Proposition 1.26, pp. 50–51, and Lemma 1.15,
p. 35. Each attachment below is the ordinary topological adjunction quotient, using the
native Euclidean closed disk and its boundary sphere. It is not a homotopy model.
Mathlib supplies the genuine pushout and finite ordered attachment data. The general
attachment assertion reduces to the finite-batch geometric theorem. The finite
one-skeleton clause follows from the existing relative cellular-approximation theorem.
-/

namespace HolomorphicAnosov

universe u

open CategoryTheory

/-- Attaching finitely many cells of dimensions at least two to a path-connected
Hausdorff CW complex gives a surjection on its original based fundamental group.

Source: Hatcher, Proposition 1.26, pp.50–51, iterated in the original stage order.
Each stage's cell indices inject into `attachments.Cells`, so each batch is finite.
The finite-batch theorem gives path connectedness and fundamental-group surjectivity
at every successor stage. Finite categorical composition then transports through
the initial and final isomorphisms supplied by the relative cell complex. Neither
intermediate classical CW structures nor sorting cells by dimension is needed.
-/
theorem hatcher_higher_cell_attachment_pi1_surjective
    {X Y : TopCat.{u}} [T2Space X] [PathConnectedSpace X]
    [Topology.CWComplex (Set.univ : Set X)]
    (inclusion : X ⟶ Y) (m : ℕ)
    (attachments : HomotopicalAlgebra.RelativeCellComplex.{u}
      (fun (_ : Fin (m + 1)) (n : {n : ℕ // 2 ≤ n}) ↦
        TopCat.diskBoundaryInclusion.{u} n.val) inclusion)
    [Finite attachments.Cells] (x0 : X) :
    Function.Surjective (FundamentalGroup.map inclusion.hom x0) := by
  apply (finite_composition_pi1_surjective inclusion m
    attachments.toTransfiniteCompositionOfShape ?_).2 x0
  intro j hpc
  have hj : ¬ IsMax j.castSucc := by
    rw [isMax_iff_eq_top]
    exact Fin.castSucc_ne_last j
  let a := attachments.attachCells j.castSucc hj
  let : Finite a.ι := Finite.of_injective
    (fun k : a.ι => (⟨j.castSucc, hj, k⟩ : attachments.Cells)) (by
      intro k l h
      cases h
      rfl)
  let := hpc
  have h := finite_higher_cell_attachment_pathConnected_pi1_surjective
    (attachments.F.map (homOfLE (Order.le_succ j.castSucc))) a
  let P (k : {k : Fin (m + 1) // j.castSucc ≤ k}) : Prop :=
    PathConnectedSpace (attachments.F.obj k.val) ∧ ∀ x : attachments.F.obj j.castSucc,
      Function.Surjective (FundamentalGroup.map (attachments.F.map (homOfLE k.property)).hom x)
  have he : (⟨Order.succ j.castSucc, Order.le_succ j.castSucc⟩ :
      {k : Fin (m + 1) // j.castSucc ≤ k}) = ⟨j.succ, j.castSucc_le_succ⟩ :=
    Subtype.ext j.orderSucc_castSucc
  exact (congrArg P he).mp h

/-- In a finite connected nonempty Hausdorff CW complex, the original one-skeleton
inclusion is surjective on the based fundamental group at every original vertex.

Source: Hatcher, Theorem 4.8, pp.349–351, relative to the loop's endpoints.
The existing one-skeleton loop approximation gives, for each based loop, a based
homotopic loop in the original one-skeleton. The fundamental-group quotient loop
criterion gives surjectivity. The chosen vertex rules out the empty complex;
loop edges, parallel edges and a singleton one-skeleton require no special case.
DAG node: `topo.hatcher_higher_cell_attachment_pi1_surjective_g10`.
-/
theorem finite_cw_one_skeleton_pi1_surjective
    {X : Type u} [TopologicalSpace X] [T2Space X] [ConnectedSpace X]
    [Topology.CWComplex (Set.univ : Set X)]
    [Topology.CWComplex.Finite (Set.univ : Set X)]
    (x0 : X)
    (hx0 : x0 ∈ (Topology.CWComplex.skeletonLT (Set.univ : Set X) 1 : Set X)) :
    let K1 := ↥(Topology.CWComplex.skeletonLT (Set.univ : Set X) 2 : Set X)
    let k1 : K1 :=
      ⟨x0, Topology.CWComplex.skeletonLT_mono (show (1 : ℕ∞) ≤ 2 by decide) hx0⟩
    let inclusion : C(K1, X) := ⟨Subtype.val, continuous_subtype_val⟩
    Function.Surjective (FundamentalGroup.map inclusion k1) := by
  dsimp only
  apply (pi1_surjective_iff_loop_homotopic _ _).mpr
  intro α
  exact cw_one_skeleton_loop_approximation x0 hx0 α


end HolomorphicAnosov
