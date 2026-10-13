import Mathlib.Topology.CWComplex.Classical.Basic
import Mathlib.Topology.Homeomorph.Lemmas

namespace HolomorphicAnosov
universe u v
open Set

/-- Transport a CW structure along the canonical universe lift homeomorphism. -/
theorem cwComplex_ulift
    (X : Type v) [TopologicalSpace X]
    [Topology.CWComplex (Set.univ : Set X)] :
    Nonempty (Topology.CWComplex (Set.univ : Set (ULift.{u} X))) := by
  let e : ULift.{u} X ≃ₜ X := Homeomorph.ulift
  let m : ∀ n : ℕ, ULift.{u} (Topology.CWComplex.cell (Set.univ : Set X) n) →
      PartialEquiv (Fin n → ℝ) (ULift.{u} X) := fun n i ↦
    (Topology.CWComplex.map (C := (Set.univ : Set X)) n i.down).transEquiv e.symm.toEquiv
  let : Topology.CWComplex (Set.univ : Set (ULift.{u} X)) :=
    { cell := fun n ↦ ULift.{u} (Topology.CWComplex.cell (Set.univ : Set X) n)
      map := m
      source_eq := by
        intro n i
        exact (Topology.CWComplex.source_eq (C := (Set.univ : Set X)) n i.down)
      continuousOn := by
        intro n i
        exact e.symm.continuous.comp_continuousOn
          (Topology.CWComplex.continuousOn n i.down)
      continuousOn_symm := by
        intro n i
        exact (Topology.CWComplex.continuousOn_symm n i.down).comp
          e.continuous.continuousOn (fun _ h ↦ h)
      pairwiseDisjoint' := by
        intro a _ b _ hab
        change Disjoint (↑(m a.1 a.2) '' Metric.ball 0 1)
          (↑(m b.1 b.2) '' Metric.ball 0 1)
        rw [Set.disjoint_left]
        rintro y ⟨x, hx, rfl⟩ ⟨z, hz, hyz⟩
        have hyz' : (Topology.CWComplex.map a.1 a.2.down) x =
            (Topology.CWComplex.map b.1 b.2.down) z := by
          exact congrArg ULift.down hyz.symm
        have hab' :
            (⟨a.1, a.2.down⟩ : Σ n, Topology.CWComplex.cell (Set.univ : Set X) n) ≠
              ⟨b.1, b.2.down⟩ := by
          intro h
          apply hab
          exact congrArg (fun p : Σ n, Topology.CWComplex.cell (Set.univ : Set X) n ↦
            (⟨p.1, ULift.up p.2⟩ : Σ n, ULift.{u} (Topology.CWComplex.cell (Set.univ : Set X) n))) h
        exact Set.disjoint_left.1
          (Topology.CWComplex.pairwiseDisjoint' (Set.mem_univ _) (Set.mem_univ _) hab')
          ⟨x, hx, rfl⟩ ⟨z, hz, hyz'.symm⟩
      mapsTo' := by
        intro n i
        obtain ⟨I, hI⟩ := Topology.CWComplex.mapsTo n i.down
        refine ⟨fun m ↦ (I m).map ⟨ULift.up, ULift.up_injective⟩, ?_⟩
        intro x hx
        rcases Set.mem_iUnion.1 (hI hx) with ⟨m, hm⟩
        rcases Set.mem_iUnion.1 hm with ⟨hmn, hm⟩
        rcases Set.mem_iUnion.1 hm with ⟨j, hm⟩
        rcases Set.mem_iUnion.1 hm with ⟨hj, y, hy, hxy⟩
        refine Set.mem_iUnion.2 ⟨m, Set.mem_iUnion.2 ⟨hmn, ?_⟩⟩
        refine Set.mem_iUnion.2 ⟨ULift.up j, ?_⟩
        refine Set.mem_iUnion.2 ⟨by simpa using hj, ?_⟩
        exact ⟨y, hy, congrArg ULift.up hxy⟩
      closed' := by
        intro A hAC hA
        have hclosed : IsClosed (e.symm ⁻¹' A) := by
          apply Topology.CWComplex.closed' (e.symm ⁻¹' A) (Set.subset_univ _)
          intro n j
          have h := (hA n (ULift.up j)).preimage e.symm.continuous
          convert h using 1
          ext x
          simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_image]
          constructor
          · rintro ⟨hx, y, hy, hxy⟩
            exact ⟨hx, y, hy, congrArg ULift.up hxy⟩
          · rintro ⟨hx, y, hy, hxy⟩
            exact ⟨hx, y, hy, congrArg ULift.down hxy⟩
        simpa [Set.preimage_preimage, Function.comp_def] using
          hclosed.preimage e.continuous
      union' := by
        apply Set.eq_univ_of_forall
        intro x
        have hx : x.down ∈ ⋃ n, ⋃ j : Topology.CWComplex.cell (Set.univ : Set X) n,
            (Topology.CWComplex.map n j) '' Metric.closedBall 0 1 := by
          rw [Topology.CWComplex.union']
          trivial
        rcases Set.mem_iUnion.1 hx with ⟨n, hn⟩
        rcases Set.mem_iUnion.1 hn with ⟨j, y, hy, hxy⟩
        exact Set.mem_iUnion.2 ⟨n, Set.mem_iUnion.2
          ⟨ULift.up j, y, hy, congrArg ULift.up hxy⟩⟩ }
  exact ⟨inferInstance⟩
end HolomorphicAnosov
