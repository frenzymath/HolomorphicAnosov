import Mathlib.GroupTheory.Perm.Cycle.Concrete
import Mathlib.Logic.Equiv.Fintype

open Equiv Equiv.Perm
namespace HolomorphicAnosov.Analysis.Complex

/-- A finite directed edge family with equal incoming and outgoing counts at every
vertex and no loop edges partitions into nonempty cyclic edge lists. Each list has
no repeated edge, and the target of each edge equals the source of its cyclic successor.

Agent-written completion of the finite-cycle bookkeeping omitted in Conway,
Functions of One Complex Variable (1978), VIII Proposition1.1, p.196, equation(1.2).
This proof route is not attributed to Conway: choose a bijection from incoming to
outgoing edges at each vertex. Together these give a permutation of the edge type,
whose successor has the required source. A fixed edge would be a loop, so every edge
lies in a nontrivial permutation cycle. Mathlib's disjoint cycle factors and cyclic
lists then give the partition. The vertex type need not be finite; the empty edge
family gives no cycles. Vertices may repeat within a cycle, as Conway's polygonal
contours need not be simple. DAG node: `analysis.finite_balanced_edges_cycles_g19`. -/
theorem finite_balanced_edges_cycles {E V : Type*} [Fintype E] [DecidableEq E] [DecidableEq V]
    (src dst : E → V) (hn : ∀ e, src e ≠ dst e)
    (hbal : ∀ v, Fintype.card {e // dst e = v} = Fintype.card {e // src e = v}) :
    ∃ (n : ℕ) (cycles : Fin n → List E),
      (∀ j, (cycles j) ≠ [] ∧ (cycles j).Nodup ∧
        ∀ (e : E) (he : e ∈ cycles j), dst e = src ((cycles j).next e he)) ∧
      (∀ e : E, ∃! j : Fin n, e ∈ cycles j) := by
  classical
  let efib (v : V) : {e // dst e = v} ≃ {e // src e = v} :=
    Fintype.equivOfCardEq (hbal v)
  let σ : Equiv.Perm E := Equiv.ofFiberEquiv efib
  have hσ (e : E) : src (σ e) = dst e := Equiv.ofFiberEquiv_map efib e
  have hmove (e : E) : σ e ≠ e := by
    intro he
    exact hn e (by simpa only [he] using hσ e)
  let C := {c : Equiv.Perm E // c ∈ σ.cycleFactorsFinset}
  have hc (c : C) : c.1.IsCycle := (mem_cycleFactorsFinset_iff.mp c.2).1
  let x (c : C) : E := Classical.choose (hc c)
  have hx (c : C) : c.1 (x c) ≠ x c := (Classical.choose_spec (hc c)).1
  let l (c : C) := c.1.toList (x c)
  have hmem (c : C) (e : E) : e ∈ l c ↔ e ∈ c.1.support := by
    rw [mem_support]
    constructor
    · intro he
      have hs := (mem_toList_iff.mp he).1
      exact hs.apply_eq_self_iff.not.mp (hx c)
    · intro he
      exact mem_toList_iff.mpr ⟨(hc c).sameCycle (hx c) he, mem_support.mpr (hx c)⟩
  have hlist (c : C) : l c ≠ [] ∧ (l c).Nodup ∧
      ∀ (e : E) (he : e ∈ l c), dst e = src ((l c).next e he) := by
    refine ⟨?_, nodup_toList _ _, ?_⟩
    · exact List.ne_nil_of_mem ((hmem c (x c)).mpr (mem_support.mpr (hx c)))
    · intro e he
      rw [next_toList_eq_apply]
      rw [(mem_cycleFactorsFinset_iff.mp c.2).2 e ((hmem c e).mp he)]
      exact (hσ e).symm
  have hcover (e : E) : ∃! c : C, e ∈ l c := by
    obtain ⟨c, hc', hec⟩ := mem_support_iff_mem_support_of_mem_cycleFactorsFinset.mp
      (mem_support.mpr (hmove e))
    refine ⟨⟨c, hc'⟩, (hmem ⟨c, hc'⟩ e).mpr hec, ?_⟩
    intro d hd
    apply Subtype.ext
    by_contra hne
    have hdis := σ.cycleFactorsFinset_pairwise_disjoint d.2 hc' hne
    exact hdis.mem_imp ((hmem d e).mp hd) hec
  let ι : Fin (Fintype.card C) ≃ C := (Fintype.equivFin C).symm
  refine ⟨Fintype.card C, fun j ↦ l (ι j), fun j ↦ hlist (ι j), ?_⟩
  intro e
  obtain ⟨c, hec, huniq⟩ := hcover e
  refine ⟨ι.symm c, by simpa using hec, ?_⟩
  intro j hj
  apply ι.injective
  simpa using huniq (ι j) hj

end HolomorphicAnosov.Analysis.Complex
