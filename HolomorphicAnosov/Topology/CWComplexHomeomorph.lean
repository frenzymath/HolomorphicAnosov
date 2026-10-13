import Mathlib.Topology.CWComplex.Classical.Basic
import Mathlib.Topology.Homeomorph.Lemmas

namespace HolomorphicAnosov
universe u
open Set
open _root_.Topology
/--
Transport a CW structure along a homeomorphism of the ambient spaces.

Source: Hatcher, *Algebraic Topology*, Appendix A, Theorem A.6 (pp. 524--525):
cell structures are invariant under homeomorphism by transporting each characteristic
map and its source.  The implementation follows the explicit field transfer used by
`cwComplex_ulift` in this project: continuity and closedness are pulled back through
the homeomorphism, while disjointness, attaching maps and coverage are transported
pointwise.  No additional topological assumptions are introduced.
-/
theorem cwComplex_homeomorph
    (X : Type u) (Y : Type) [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) [Topology.CWComplex (Set.univ : Set Y)] :
    Nonempty (Topology.CWComplex (Set.univ : Set X)) := by
  let m : ∀ n : ℕ, ULift.{u} (Topology.CWComplex.cell (Set.univ : Set Y) n) →
      PartialEquiv (Fin n → ℝ) X := fun n i ↦
    (Topology.CWComplex.map (C := (Set.univ : Set Y)) n i.down).transEquiv e.symm.toEquiv
  let : Topology.CWComplex (Set.univ : Set X) :=
    { cell := fun n ↦ ULift.{u} (Topology.CWComplex.cell (Set.univ : Set Y) n)
      map := m
      source_eq := by
        intro n i
        exact Topology.CWComplex.source_eq (C := (Set.univ : Set Y)) n i.down
      continuousOn := by
        intro n i
        exact e.symm.continuous.comp_continuousOn
          (Topology.CWComplex.continuousOn (C := (Set.univ : Set Y)) n i.down)
      continuousOn_symm := by
        intro n i
        exact (Topology.CWComplex.continuousOn_symm (C := (Set.univ : Set Y)) n i.down).comp
          e.continuous.continuousOn (fun _ h ↦ h)
      pairwiseDisjoint' := by
        intro a _ b _ hab
        change Disjoint (↑(m a.1 a.2) '' Metric.ball 0 1)
          (↑(m b.1 b.2) '' Metric.ball 0 1)
        rw [Set.disjoint_left]
        rintro y ⟨x, hx, rfl⟩ ⟨z, hz, hyz⟩
        have hyz' : (Topology.CWComplex.map (C := (Set.univ : Set Y)) a.1 a.2.down) x =
            (Topology.CWComplex.map (C := (Set.univ : Set Y)) b.1 b.2.down) z := by
          simpa [m, PartialEquiv.coe_transEquiv] using congrArg e hyz.symm
        have hab' : (⟨a.1, a.2.down⟩ : Σ n, Topology.CWComplex.cell (Set.univ : Set Y) n) ≠
              ⟨b.1, b.2.down⟩ := by
          intro h
          apply hab
          exact congrArg (fun p : Σ n, Topology.CWComplex.cell (Set.univ : Set Y) n ↦
            (⟨p.1, ULift.up p.2⟩ : Σ n, ULift.{u} (Topology.CWComplex.cell (Set.univ : Set Y) n))) h
        exact Set.disjoint_left.1
          (Topology.CWComplex.pairwiseDisjoint' (C := (Set.univ : Set Y))
            (Set.mem_univ _) (Set.mem_univ _) hab')
          ⟨x, hx, rfl⟩ ⟨z, hz, hyz'.symm⟩
      mapsTo' := by
        intro n i
        obtain ⟨I, hI⟩ := Topology.CWComplex.mapsTo (C := (Set.univ : Set Y)) n i.down
        refine ⟨fun j ↦ (I j).map ⟨ULift.up, ULift.up_injective⟩, ?_⟩
        intro x hx
        rcases Set.mem_iUnion.1 (hI hx) with ⟨m', hm'⟩
        rcases Set.mem_iUnion.1 hm' with ⟨hmn, hm'⟩
        rcases Set.mem_iUnion.1 hm' with ⟨j, hm'⟩
        rcases Set.mem_iUnion.1 hm' with ⟨hj, y, hy, hxy⟩
        refine Set.mem_iUnion.2 ⟨m', Set.mem_iUnion.2 ⟨hmn, ?_⟩⟩
        refine Set.mem_iUnion.2 ⟨ULift.up j, Set.mem_iUnion.2 ⟨by simpa using hj, ?_⟩⟩
        exact ⟨y, hy, congrArg e.symm hxy⟩
      closed' := by
        intro A hA hclosed
        have hB : IsClosed (Set.image (fun x : X => (e : X → Y) x) A) := by
          apply Topology.CWComplex.closed' (C := (Set.univ : Set Y))
            (Set.image (fun x : X => (e : X → Y) x) A) (by simp)
          intro n i
          let D : Set Y :=
            (↑(Topology.CWComplex.map (C := (Set.univ : Set Y)) n i) :
              (Fin n → ℝ) → Y) '' (Metric.closedBall 0 1)
          have hpre : IsClosed (Set.preimage (e : X → Y)
              (Set.inter (Set.image (fun x : X => (e : X → Y) x) A) D)) := by
            have hc := hclosed n (ULift.up i)
            rw [show Set.preimage (e : X → Y)
                (Set.inter (Set.image (fun x : X => (e : X → Y) x) A) D) =
                A ∩ m n (ULift.up i) '' Metric.closedBall 0 1 by
              ext x
              constructor
              · intro hx
                rcases hx.1 with ⟨y, hy, hey⟩
                have hxy : y = x := e.injective hey
                subst y
                rcases hx.2 with ⟨u, hu, hux⟩
                exact ⟨hy, ⟨u, hu, by simpa [m, PartialEquiv.coe_transEquiv] using congrArg e.symm hux⟩⟩
              · intro hx
                refine ⟨⟨x, hx.1, rfl⟩, ?_⟩
                rcases hx.2 with ⟨u, hu, huX⟩
                exact ⟨u, hu, by simpa [m, PartialEquiv.coe_transEquiv] using congrArg e huX⟩]
            exact hc
          exact (e.isClosed_preimage).mp hpre
        have hp : IsClosed (e ⁻¹' (e '' A)) := (e.isClosed_preimage).mpr hB
        simpa only [e.preimage_image] using hp
      union' := by
        apply Set.eq_univ_of_forall
        intro x
        have hx : e x ∈ ⋃ n, ⋃ i : Topology.CWComplex.cell (Set.univ : Set Y) n,
            (Topology.CWComplex.map (C := (Set.univ : Set Y)) n i) '' Metric.closedBall 0 1 := by
          rw [Topology.CWComplex.union']
          trivial
        rcases Set.mem_iUnion.1 hx with ⟨n, hn⟩
        rcases Set.mem_iUnion.1 hn with ⟨i, y, hy, hxy⟩
        exact Set.mem_iUnion.2 ⟨n, Set.mem_iUnion.2
          ⟨ULift.up i, y, hy, by simpa [m, PartialEquiv.coe_transEquiv] using congrArg e.symm hxy⟩⟩ }
  exact ⟨inferInstance⟩
end HolomorphicAnosov
