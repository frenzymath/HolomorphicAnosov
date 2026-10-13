import HolomorphicAnosov.Topology.GraphComplementConnected
import Mathlib.Topology.Compactification.OnePoint.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.ContinuousMap.Basic

/-!
# Continuous missing-value graph patching on the projective line

This file proves the continuous patching lemma for missing-value maps on the projective line (Ghys, Lemma 5.2).
-/

namespace HolomorphicAnosov.GraphComplement

open Set

local notation "P" => (OnePoint ℂ)

/-- If two continuous missing-value maps have graph complements whose union contains no full vertical fibre, they agree where both are defined and patch continuously over the complement of the common exceptional set (Ghys, Lemma 5.2). -/
theorem single_union_patch
    (F G : Set P) (hF : IsClosed F) (hG : IsClosed G)
    (u : C({x : P // x ∉ F}, P)) (v : C({x : P // x ∉ G}, P)) :
    let single : (H : Set P) → C({x : P // x ∉ H}, P) → Set (P × P) :=
      fun H w ↦ {z | ∃ hx : z.1 ∉ H, z.2 ≠ w ⟨z.1, hx⟩}
    let combined := single F u ∪ single G v
    let patchedOn : Set P → Prop := fun H ↦
      ∃ w : C({x : P // x ∉ H}, P),
        combined = single H w ∧
        (∀ (x : {x : P // x ∉ F}) (hx : x.val ∉ H), w ⟨x.val, hx⟩ = u x) ∧
        (∀ (x : {x : P // x ∉ G}) (hx : x.val ∉ H), w ⟨x.val, hx⟩ = v x)
    (∀ x : P, ¬∀ y : P, (x, y) ∈ combined) →
      (∀ (x : P) (hxF : x ∉ F) (hxG : x ∉ G), u ⟨x, hxF⟩ = v ⟨x, hxG⟩) ∧
      patchedOn (F ∩ G) ∧
      ((F = ∅ ∨ G = ∅) → patchedOn ∅) ∧
      (∀ a : P, F = {a} → G = {a} → patchedOn {a}) ∧
      (∀ a b : P, a ≠ b → F = {a} → G = {b} → patchedOn ∅) := by
  classical
  intro single combined patchedOn hnofull
  have hagree : ∀ (x : P) (hxF : x ∉ F) (hxG : x ∉ G),
      u ⟨x, hxF⟩ = v ⟨x, hxG⟩ := by
    intro x hxF hxG
    by_contra hne
    apply hnofull x
    intro y
    by_cases hy : y = u ⟨x, hxF⟩
    · exact Or.inr ⟨hxG, by simpa only [hy] using hne⟩
    · exact Or.inl ⟨hxF, hy⟩
  let uf : P → P := fun x ↦ if hx : x ∉ F then u ⟨x, hx⟩ else OnePoint.infty
  let vf : P → P := fun x ↦ if hx : x ∉ G then v ⟨x, hx⟩ else OnePoint.infty
  have huf : ContinuousOn uf Fᶜ := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    have heq : Fᶜ.domRestrict uf = u := by
      funext x
      have hx : x.val ∉ F := x.property
      simp only [Set.domRestrict_apply, uf, dite_eq_left hx]
      rfl
    rw [heq]
    exact u.continuous
  have hvf : ContinuousOn vf Gᶜ := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    have heq : Gᶜ.domRestrict vf = v := by
      funext x
      have hx : x.val ∉ G := x.property
      simp only [Set.domRestrict_apply, vf, dite_eq_left hx]
      rfl
    rw [heq]
    exact v.continuous
  let ww : P → P := fun x ↦ if x ∉ F then uf x else vf x
  have hwF : ∀ x (hx : x ∉ F), ww x = u ⟨x, hx⟩ := by
    intro x hx
    simp [ww, uf, hx]
  have hwG : ∀ x (hx : x ∉ G), ww x = v ⟨x, hx⟩ := by
    intro x hx
    by_cases hxF : x ∉ F
    · simpa only [hwF x hxF] using hagree x hxF hx
    · simp [ww, vf, hxF, hx]
  have hww : ContinuousOn ww (F ∩ G)ᶜ := by
    rw [Set.compl_inter]
    apply ContinuousOn.union_of_isOpen
    · exact huf.congr fun x hx ↦ by
        change x ∉ F at hx
        simp only [ww, ite_eq_left hx]
    · exact hvf.congr fun x hx ↦ by
        change x ∉ G at hx
        simpa only [vf, dite_eq_left hx] using hwG x hx
    · exact hF.isOpen_compl
    · exact hG.isOpen_compl
  let w : C({x : P // x ∉ F ∩ G}, P) :=
    ⟨(F ∩ G)ᶜ.domRestrict ww, hww.domRestrict⟩
  have hpatch : patchedOn (F ∩ G) := by
    refine ⟨w, ?_, ?_, ?_⟩
    · ext z
      constructor
      · rintro (⟨hxF, hy⟩ | ⟨hxG, hy⟩)
        · refine ⟨fun hx ↦ hxF hx.1, ?_⟩
          simpa only [w, ContinuousMap.coe_mk, Set.domRestrict_apply, hwF z.1 hxF] using hy
        · refine ⟨fun hx ↦ hxG hx.2, ?_⟩
          simpa only [w, ContinuousMap.coe_mk, Set.domRestrict_apply, hwG z.1 hxG] using hy
      · rintro ⟨hxFG, hy⟩
        by_cases hxF : z.1 ∉ F
        · left
          refine ⟨hxF, ?_⟩
          simpa only [w, ContinuousMap.coe_mk, Set.domRestrict_apply, hwF z.1 hxF] using hy
        · right
          have hxG : z.1 ∉ G := fun hx ↦ hxFG ⟨not_not.mp hxF, hx⟩
          refine ⟨hxG, ?_⟩
          simpa only [w, ContinuousMap.coe_mk, Set.domRestrict_apply, hwG z.1 hxG] using hy
    · intro x hx
      exact hwF x.val x.property
    · intro x hx
      exact hwG x.val x.property
  refine ⟨hagree, hpatch, ?_, ?_, ?_⟩
  · rintro (hF0 | hG0)
    · simpa only [hF0, Set.empty_inter] using hpatch
    · simpa only [hG0, Set.inter_empty] using hpatch
  · intro a hFa hGa
    simpa only [hFa, hGa, Set.inter_self] using hpatch
  · intro a b hab hFa hGb
    have hinter : F ∩ G = ∅ := by
      rw [hFa, hGb]
      exact Set.inter_singleton_eq_empty.mpr (by simpa using hab.symm)
    simpa only [hinter] using hpatch


end HolomorphicAnosov.GraphComplement
