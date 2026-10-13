import HolomorphicAnosov.Topology.GraphComplementConnected
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.Compactification.OnePoint.ProjectiveLine
import Mathlib.Tactic

noncomputable section
open Set _root_.Topology
namespace HolomorphicAnosov.Ghys

/-- The intersection of two continuous graph complements in `OnePoint ℂ × OnePoint ℂ` is path
connected when their base exceptional sets are respectively empty or a singleton, and a
singleton. -/
theorem two_graph_inter_pathConnected
    (F : Set (OnePoint ℂ))
    (hF : F = ∅ ∨ ∃ pole : OnePoint ℂ, F = {pole}) (b : OnePoint ℂ)
    (u : C({p : OnePoint ℂ // p ∉ F}, OnePoint ℂ))
    (v : C({p : OnePoint ℂ // p ∉ ({b} : Set (OnePoint ℂ))}, OnePoint ℂ)) :
    IsPathConnected
      ({z : OnePoint ℂ × OnePoint ℂ | ∃ hp : z.1 ∉ F, z.2 ≠ u ⟨z.1, hp⟩} ∩
        {z : OnePoint ℂ × OnePoint ℂ | ∃ hp : z.1 ∉ ({b} : Set (OnePoint ℂ)),
          z.2 ≠ v ⟨z.1, hp⟩}) := by
  have hfinite : F.Finite := by
    rcases hF with rfl | ⟨pole, rfl⟩ <;> simp
  have hcard : F.ncard ≤ 1 := by
    rcases hF with rfl | ⟨pole, rfl⟩ <;> simp
  let G := F ∪ {b}
  have hGfinite : G.Finite := hfinite.union (finite_singleton b)
  have hGcard : G.ncard ≤ 2 := by
    have := Set.ncard_union_le F ({b} : Set (OnePoint ℂ))
    simp only [Set.ncard_singleton] at this
    exact this.trans (by omega)
  let ru : {p : OnePoint ℂ // p ∉ G} → {p : OnePoint ℂ // p ∉ F} :=
    fun p ↦ ⟨p.val, fun h ↦ p.property (Or.inl h)⟩
  let rv : {p : OnePoint ℂ // p ∉ G} →
      {p : OnePoint ℂ // p ∉ ({b} : Set (OnePoint ℂ))} :=
    fun p ↦ ⟨p.val, fun h ↦ p.property (Or.inr h)⟩
  let maps : Fin 2 → ({p : OnePoint ℂ // p ∉ G} → OnePoint ℂ) :=
    fun i ↦ if i = 0 then u ∘ ru else v ∘ rv
  have hmaps : ∀ i, Continuous (maps i) := by
    intro i
    dsimp only [maps]
    split_ifs
    · exact u.continuous.comp (continuous_subtype_val.subtype_mk _)
    · exact v.continuous.comp (continuous_subtype_val.subtype_mk _)
  have h := graph_complement_nonempty_isPathConnected G hGfinite hGcard 2 maps hmaps
  convert h using 1
  ext z
  constructor
  · rintro ⟨⟨hu, hqu⟩, ⟨hv, hqv⟩⟩
    refine ⟨fun hg ↦ hg.elim hu hv, ?_⟩
    intro i
    fin_cases i <;> simp_all [maps, ru, rv]
  · rintro ⟨hz, hq⟩
    have hu : z.1 ∉ F := fun h ↦ hz (Or.inl h)
    have hv : z.1 ∉ ({b} : Set (OnePoint ℂ)) := fun h ↦ hz (Or.inr h)
    refine ⟨⟨hu, ?_⟩, ⟨hv, ?_⟩⟩
    · simpa [maps, ru] using hq 0
    · simpa [maps, rv] using hq 1


end HolomorphicAnosov.Ghys
