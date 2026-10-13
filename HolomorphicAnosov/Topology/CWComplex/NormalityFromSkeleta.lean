import HolomorphicAnosov.Topology.CWComplex.CompatibleIntervalExtension
import HolomorphicAnosov.Topology.CWComplex.CompatibleSkeletalIntervalDescent
import HolomorphicAnosov.Topology.CWComplex.IntervalExtensionNormality
import Mathlib.Topology.CWComplex.Classical.Basic
import Mathlib.Topology.TietzeExtension
import Mathlib.Analysis.Complex.Tietze

/-! Normality of the weak-topology union of normal finite skeleta.
Source: Fritsch–Piccinini, Cellular Structures in Topology, Appendix A.5.1(iv),
p.274, the written compatible interval-extension proof. -/

namespace HolomorphicAnosov.Topology.CWComplex
universe u

/-- A Hausdorff classical CW complex is normal if all its finite skeleta are
normal in their induced topologies.

Source: Fritsch–Piccinini, Appendix A.5.1(iv), p.274. Given a continuous interval
map on a closed subset, extend it first over the zero skeleton by Tietze. At
each successor, prescribe the preceding extension on the previous skeleton
and the original map on the closed subset. These agree on their intersection;
closed-set pasting and Tietze give a common extension. Choose these extensions
recursively, preserving exact successor agreement. Their weak-topology descent
is a continuous extension on the whole CW space. The interval-extension
criterion gives normality. Skeleta and closed subsets may be empty; there is
no finiteness or countability condition on the cell sets. -/
theorem normalSpace_of_normal_skeleta
    {X : Type u} [TopologicalSpace X] [T2Space X]
    [_root_.Topology.CWComplex (Set.univ : Set X)]
    (hnormal : ∀ n : ℕ, NormalSpace
      ↥(_root_.Topology.RelCWComplex.skeleton (Set.univ : Set X) (n : ℕ∞) : Set X)) :
    NormalSpace X := by
  classical
  apply HolomorphicAnosov.Topology.normalSpace_of_unitInterval_extension
  intro A hA g
  let S (n : ℕ) : Set X :=
    (_root_.Topology.RelCWComplex.skeleton (Set.univ : Set X) (n : ℕ∞) : Set X)
  have hS (n : ℕ) : IsClosed (S n) :=
    (_root_.Topology.RelCWComplex.skeleton (Set.univ : Set X) (n : ℕ∞)).closed
  have hmono (n : ℕ) : S n ⊆ S (n + 1) :=
    _root_.Topology.RelCWComplex.skeleton_mono (by exact_mod_cast Nat.le_succ n)
  let D (n : ℕ) : Set (S n) := Subtype.val ⁻¹' A
  let data (n : ℕ) : C(D n, unitInterval) :=
    ⟨fun x ↦ g ⟨x.val.val, x.property⟩, by fun_prop⟩
  let E (n : ℕ) := {f : C(S n, unitInterval) //
    ∀ (x : S n) (hx : x.val ∈ A), f x = g ⟨x.val, hx⟩}
  have hbase : Nonempty (E 0) := by
    let : NormalSpace (S 0) := hnormal 0
    obtain ⟨F,hF⟩ := (data 0).exists_restrict_eq (hA.preimage continuous_subtype_val)
    refine ⟨⟨F, ?_⟩⟩
    intro x hx
    exact congrArg (fun q : C(D 0, unitInterval) ↦ q ⟨x,hx⟩) hF
  have hnext (n : ℕ) (e : E n) : ∃ e' : E (n + 1),
      ∀ x : S n, e'.val ⟨x.val,hmono n x.property⟩ = e.val x := by
    let : NormalSpace (S (n + 1)) := hnormal (n + 1)
    let P : Set (S (n + 1)) := Subtype.val ⁻¹' S n
    let old : C(P, unitInterval) :=
      ⟨fun x ↦ e.val ⟨x.val.val,x.property⟩,
        e.val.continuous.comp ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _)⟩
    obtain ⟨F,hF,hdata⟩ := HolomorphicAnosov.Topology.exists_compatible_unitInterval_extension
      P (D (n + 1)) ((hS n).preimage continuous_subtype_val)
      (hA.preimage continuous_subtype_val) old (data (n + 1))
      (by intro x hp hd; exact e.property ⟨x.val,hp⟩ hd)
    refine ⟨⟨F, ?_⟩, ?_⟩
    · intro x hx
      exact hdata ⟨x,hx⟩
    · intro x
      exact hF ⟨⟨x.val,hmono n x.property⟩,x.property⟩
  let f : ∀ n : ℕ, E n := fun n ↦ Nat.rec hbase.some
    (fun n e ↦ Classical.choose (hnext n e)) n
  apply exists_extension_of_compatible_skeletal_extensions A g (fun n ↦ (f n).val)
  · intro n x
    exact (Classical.choose_spec (hnext n (f n)) x).symm
  · intro n x hx
    exact (f n).property x hx

end HolomorphicAnosov.Topology.CWComplex
