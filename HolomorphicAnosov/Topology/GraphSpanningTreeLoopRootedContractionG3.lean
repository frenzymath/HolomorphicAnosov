import HolomorphicAnosov.Topology.BasedHomotopyUniqueness
import HolomorphicAnosov.Topology.GraphSpanningTreeLoopRootedContractionApplyG3
import HolomorphicAnosov.Topology.GraphSpanningTreeLoopPrescribedTreeDataG3
import Mathlib.Topology.CWComplex.Classical.Graph
import Mathlib.Combinatorics.Graph.Simple
import Mathlib.Combinatorics.Graph.Delete
import Mathlib.Combinatorics.SimpleGraph.Acyclic

namespace HolomorphicAnosov

open _root_.Topology

/-- A supplied simple spanning tree admits the rooted contraction required by
Hatcher's quotient argument.

Source: Hatcher, *Algebraic Topology*, Proposition 1A.1 p.84, with the
finite rooted-tree data from the simple graph and the ordinary-product
weak-CW gluing in `rooted_cw_tree_inclusion_contraction`. The statement is
kept as the exact geometric residual for the supplied subcomplex: it produces
a contraction of the literal tree carrier, fixes the chosen root, and stays
inside that carrier. No quotient or fundamental-group conclusion is hidden in
this residual.
-/
theorem graph_spanning_tree_loop_rooted_contraction_g3
    {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X]
    [Topology.CWComplex (Set.univ : Set X)]
    (hdim : ∀ n : ℕ, 1 < n → IsEmpty (Topology.RelCWComplex.cell (Set.univ : Set X) n))
    (T : Topology.RelCWComplex.Subcomplex (Set.univ : Set X))
    (hT0 : T.I 0 = Set.univ)
    (hTsimple : ((Topology.CWComplex.OneSkeletonGraph (Set.univ : Set X)).restrict (T.I 1)).Simple)
    (hTtree :
      ((Topology.CWComplex.OneSkeletonGraph (Set.univ : Set X)).restrict (T.I 1)).toSimpleGraph.IsTree)
    (v0 : Topology.RelCWComplex.cell (Set.univ : Set X) 0)
    (r0 : (T : Set X))
    (hr0 : r0.val = Topology.RelCWComplex.map (C := Set.univ) 0 v0 ![]) :
    ∃ H : C(unitInterval × (T : Set X), X),
      (∀ x, H (0, x) = x.val) ∧
      (∀ x, H (1, x) = r0.val) ∧
      (∀ t, H (t, r0) = r0.val) ∧
      (∀ q, H q ∈ (T : Set X)) := by
  have hdata := graph_spanning_tree_loop_prescribed_tree_data_g3 T hT0 hTsimple hTtree v0
  dsimp at hdata
  obtain ⟨d, parent, edge, hdr, hdepth, hlink⟩ := hdata
  let : Topology.CWComplex (T : Set X) := Topology.CWComplex.Subcomplex.instCWComplex T
  let rootT : Topology.RelCWComplex.cell (T : Set X) 0 :=
    ⟨v0, by rw [hT0]; trivial⟩
  let cv : {v : Topology.RelCWComplex.cell (T : Set X) 0 // v ≠ rootT} →
      {v : ((Topology.CWComplex.OneSkeletonGraph (Set.univ : Set X)).restrict (T.I 1)).vertexSet // v ≠ ⟨v0, by trivial⟩} := fun v =>
    ⟨⟨v.val.val, by trivial⟩, by
      intro hv
      apply v.property
      apply Subtype.ext
      exact congrArg (fun z : ((Topology.CWComplex.OneSkeletonGraph (Set.univ : Set X)).restrict (T.I 1)).vertexSet => z.val) hv⟩
  let parentT : {v : Topology.RelCWComplex.cell (T : Set X) 0 // v ≠ rootT} →
      Topology.RelCWComplex.cell (T : Set X) 0 := fun v =>
    ⟨parent (cv v), by rw [hT0]; trivial⟩
  let edgeT : {v : Topology.RelCWComplex.cell (T : Set X) 0 // v ≠ rootT} ≃
      Topology.RelCWComplex.cell (T : Set X) 1 := by
    let f : {v : Topology.RelCWComplex.cell (T : Set X) 0 // v ≠ rootT} →
        Topology.RelCWComplex.cell (T : Set X) 1 := fun v =>
      ⟨(edge (cv v)).val, by
        convert (edge (cv v)).property using 1; simp [Graph.restrict]⟩
    let g : Topology.RelCWComplex.cell (T : Set X) 1 →
        {v : Topology.RelCWComplex.cell (T : Set X) 0 // v ≠ rootT} := fun e =>
        ⟨⟨(edge.symm ⟨e.val, by
          convert e.property using 1; simp [Graph.restrict]⟩).val, by rw [hT0]; trivial⟩, by
        intro hv
        apply (edge.symm ⟨e.val, by
          convert e.property using 1; simp [Graph.restrict]⟩).property
        exact congrArg (fun z : Topology.RelCWComplex.cell (T : Set X) 0 =>
          (⟨z.val, by trivial⟩ : ((Topology.CWComplex.OneSkeletonGraph (Set.univ : Set X)).restrict (T.I 1)).vertexSet)) hv⟩
    refine { toFun := f, invFun := g, left_inv := ?_, right_inv := ?_ }
    · intro v
      apply Subtype.ext
      apply Subtype.ext
      dsimp [f, g, cv]
      simp [f, cv]
    · intro e
      apply Subtype.ext
      dsimp [f, g, cv]
      let ge : {e // e ∈ ((Topology.CWComplex.OneSkeletonGraph (Set.univ : Set X)).restrict (T.I 1)).edgeSet} :=
        ⟨e.val, by convert e.property using 1; simp [Graph.restrict]⟩
      change (edge (cv (g e))).val = e.val
      have hcv : cv (g e) = edge.symm ge := by
        apply Subtype.ext
        apply Subtype.ext
        rfl
      rw [hcv]
      exact congrArg (fun z : {e // e ∈ ((Topology.CWComplex.OneSkeletonGraph (Set.univ : Set X)).restrict (T.I 1)).edgeSet} => z.val) (edge.apply_symm_apply ge)
  let dT : Topology.RelCWComplex.cell (T : Set X) 0 → ℕ := fun v => d ⟨v.val, by trivial⟩
  have hdrT : dT rootT = 0 := by simpa [dT, rootT] using hdr
  have hdepthT : ∀ v, dT (parentT v) + 1 = dT v.val := by
    intro v
    simpa [dT, parentT, cv] using hdepth (cv v)
  have hhighT : ∀ n, IsEmpty (Topology.RelCWComplex.cell (T : Set X) (n + 2)) := by
    intro n
    have he := hdim (n + 2) (by omega)
    exact ⟨fun z => he.false z.val⟩
  have hlinkT : ∀ v, (Topology.CWComplex.OneSkeletonGraph (T : Set X)).IsLink
      (edgeT v) (parentT v) v.val := by
    intro v
    simpa [edgeT, parentT, cv, Topology.CWComplex.Subcomplex.cell_def,
      Topology.CWComplex.Subcomplex.map_def, Graph.restrict] using (hlink (cv v)).2
  obtain ⟨H, hzero, hone, hroot, hmem⟩ :=
    rooted_cw_tree_inclusion_contraction
      (T : Set X) hhighT rootT dT hdrT parentT hdepthT edgeT hlinkT
  refine ⟨H, hzero, ?_, ?_, hmem⟩
  · intro x
    convert hone x using 1; simp [rootT, hr0]
  · intro t
    let rc : (T : Set X) := ⟨Topology.RelCWComplex.map (C := Set.univ) 0 v0 ![], by
      convert r0.property using 1; simp [← hr0]⟩
    have hrc : r0 = rc := by
      apply Subtype.ext
      exact hr0
    rw [hrc]
    simpa [rc, rootT, Topology.CWComplex.Subcomplex.map_def] using hroot t

end HolomorphicAnosov
