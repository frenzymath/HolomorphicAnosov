import HolomorphicAnosov.Paper.Ghys.SurfaceGraphPatching
import HolomorphicAnosov.Paper.Ghys.SurfaceDevelopingSetTools
import HolomorphicAnosov.Paper.Ghys.SurfaceDevelopingGraphIntersection
import HolomorphicAnosov.Topology.SurfaceInjectivityKernel
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.Compactification.OnePoint.ProjectiveLine
import Mathlib.Tactic

noncomputable section
open Set _root_.Topology
namespace HolomorphicAnosov.Ghys

/-- A local homeomorphism with punctured graph images on open sets is injective on their
connected nonempty finite prefixes, provided each injective prefix image contains no full
vertical fibre. Each prefix image is a continuous graph complement with at most one
exceptional base point. -/
theorem onePoint_finite_prefix_induction
    {X : Type*} [TopologicalSpace X] [T2Space X]
    (D : X → OnePoint ℂ × OnePoint ℂ) (hD : IsLocalHomeomorph D)
    (s : ℕ → Set X) (hopen : ∀ i, IsOpen (s i))
    (hbase : ∀ i, Set.InjOn D (s i) ∧ ∃ (b : OnePoint ℂ)
      (v : C({p : OnePoint ℂ // p ∉ ({b} : Set (OnePoint ℂ))}, OnePoint ℂ)),
      (s i).Nonempty ∧ D '' s i =
        {z | ∃ hp : z.1 ∉ ({b} : Set (OnePoint ℂ)), z.2 ≠ v ⟨z.1, hp⟩})
    (hnofull : ∀ n, Set.InjOn D (⋃ i ∈ Finset.range n, s i) →
      ∀ p : OnePoint ℂ, ¬∀ q : OnePoint ℂ, (p, q) ∈ D '' (⋃ i ∈ Finset.range n, s i))
    (hconn : ∀ n, 1 ≤ n → IsConnected (⋃ i ∈ Finset.range n, s i)) :
    ∀ n, 1 ≤ n → Set.InjOn D (⋃ i ∈ Finset.range n, s i) ∧
      ∃ (F : Set (OnePoint ℂ)) (u : C({p : OnePoint ℂ // p ∉ F}, OnePoint ℂ)),
      (F = ∅ ∨ ∃ pole : OnePoint ℂ, F = {pole}) ∧
      D '' (⋃ i ∈ Finset.range n, s i) = {z | ∃ hp : z.1 ∉ F, z.2 ≠ u ⟨z.1, hp⟩} := by
  intro n hn
  induction n using Nat.case_strong_induction_on with
  | hz => omega
  | hi n ih =>
    by_cases hnzero : n = 0
    · subst n
      obtain ⟨hinj, b, v, hne, himage⟩ := hbase 0
      rw [prefix_succ s 0]
      have hz : (⋃ i ∈ Finset.range 0, s i) = ∅ := by
        ext z
        simp only [mem_iUnion, Finset.mem_range, Set.mem_empty_iff_false]
        constructor
        · rintro ⟨i, hi, _⟩
          omega
        · exact False.elim
      rw [hz, Set.empty_union]
      exact ⟨hinj, {b}, v, Or.inr ⟨b, rfl⟩, himage⟩
    · have hnpos : 1 ≤ n := by omega
      obtain ⟨hprev, F, u, hF, himage⟩ := ih n (Nat.le_refl n) hnpos
      obtain ⟨hnew, b, v, hne, hnewimage⟩ := hbase n
      let A := ⋃ i ∈ Finset.range n, s i
      have hA : IsOpen A := isOpen_iUnion (fun i ↦ isOpen_iUnion (fun _ ↦ hopen i))
      have hAne : A.Nonempty := (hconn n hnpos).nonempty
      have hnext : (⋃ i ∈ Finset.range (n + 1), s i) = A ∪ s n := prefix_succ s n
      have hoverlap : (A ∩ s n).Nonempty := source_overlap_of_connected_union hA
        (hopen n) hAne hne (hnext ▸ hconn (n + 1) (by omega))
      have hpath : IsPathConnected (D '' A ∩ D '' s n) := by
        rw [himage, hnewimage]
        exact two_graph_inter_pathConnected F hF b u v
      have hinj : Set.InjOn D (⋃ i ∈ Finset.range (n + 1), s i) := by
        rw [hnext]
        exact surface_injOn_union_of_pathConnected_image_inter hD hA (hopen n)
          hprev hnew hoverlap hpath
      have hFclosed : IsClosed F := by
        rcases hF with rfl | ⟨pole, rfl⟩ <;> simp
      have hnfull : ∀ p : OnePoint ℂ, ¬∀ q : OnePoint ℂ,
          (p, q) ∈ {z | ∃ hp : z.1 ∉ F, z.2 ≠ u ⟨z.1, hp⟩} ∪
            {z | ∃ hp : z.1 ∉ ({b} : Set (OnePoint ℂ)), z.2 ≠ v ⟨z.1, hp⟩} := by
        rw [← himage, ← hnewimage, ← Set.image_union, ← hnext]
        exact hnofull (n + 1) hinj
      obtain ⟨_, ⟨w, hw, _, _⟩, _⟩ :=
        GraphComplement.single_union_patch F {b} hFclosed isClosed_singleton u v hnfull
      refine ⟨hinj, F ∩ {b}, w, ?_, ?_⟩
      · rcases hF with rfl | ⟨pole, rfl⟩
        · exact Or.inl (empty_inter _)
        · by_cases hpb : pole = b
          · subst pole
            exact Or.inr ⟨b, inter_self _⟩
          · exact Or.inl (Set.inter_singleton_eq_empty.mpr (by simpa using Ne.symm hpb))
      · rw [hnext, Set.image_union, himage, hnewimage]
        exact hw


end HolomorphicAnosov.Ghys
