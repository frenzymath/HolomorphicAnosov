import Mathlib.Topology.UnitInterval
import Mathlib.Topology.Homotopy.Path
import HolomorphicAnosov.Topology.TwoArcsCircleEmbedding

namespace HolomorphicAnosov.Topology
open Set

/-- Concatenate two injective paths meeting only at their common endpoint.
The resulting embedded interval stays inside the two original ranges. -/
theorem embedded_path_trans_singleton_inter_exact
    {X : Type*} [TopologicalSpace X] [T2Space X]
    {x q y : X} (α : Path x q) (β : Path q y)
    (hα : Function.Injective (α : unitInterval → X))
    (hβ : Function.Injective (β : unitInterval → X))
    (hmeet : range (α : unitInterval → X) ∩ range (β : unitInterval → X) = {q}) :
    Topology.IsEmbedding (α.trans β) ∧
      (α.trans β) 0 = x ∧ (α.trans β) 1 = y ∧
      range (α.trans β) = range (α : unitInterval → X) ∪ range (β : unitInterval → X) := by
  let γ : unitInterval → X := α.trans β
  have hγinj : Function.Injective γ := by
    intro u v huv
    simp only [γ, Path.trans_apply] at huv
    split_ifs at huv with hu hv hv
    · let u2 : unitInterval := ⟨2 * (u : ℝ), by
        constructor <;> linarith [u.property.1, u.property.2, hu]⟩
      let v2 : unitInterval := ⟨2 * (v : ℝ), by
        constructor <;> linarith [v.property.1, v.property.2, hv]⟩
      have harg : u2 = v2 := hα huv
      apply Subtype.ext
      have harg' := congrArg (fun z : unitInterval => (z : ℝ)) harg
      dsimp [u2, v2] at harg'
      linarith
    · let u2 : unitInterval := ⟨2 * (u : ℝ), by
        constructor <;> linarith [u.property.1, u.property.2, hu]⟩
      let vminus : unitInterval := ⟨2 * (v : ℝ) - 1, by
        constructor <;> linarith [v.property.1, v.property.2, hv]⟩
      have hmem : α u2 ∈ range (β : unitInterval → X) := ⟨vminus, huv.symm⟩
      have hsingleton : α u2 ∈ ({q} : Set X) := by
        rw [← hmeet]
        exact ⟨⟨u2, rfl⟩, hmem⟩
      have hq : α u2 = q := Set.mem_singleton_iff.mp hsingleton
      have hu' : (u : ℝ) = 1 / 2 := by
        have harg : u2 = 1 := hα (hq.trans α.target.symm)
        have harg' := congrArg (fun z : unitInterval => (z : ℝ)) harg
        dsimp [u2] at harg'
        linarith
      have hv' : (v : ℝ) = 1 / 2 := by
        have hbarg : β vminus = β 0 := huv.symm.trans (hq.trans β.source.symm)
        have harg : vminus = 0 := hβ hbarg
        have harg' := congrArg (fun z : unitInterval => (z : ℝ)) harg
        dsimp [vminus] at harg'
        linarith
      apply Subtype.ext
      linarith
    · let v2 : unitInterval := ⟨2 * (v : ℝ), by
        constructor <;> linarith [v.property.1, v.property.2, hv]⟩
      let uminus : unitInterval := ⟨2 * (u : ℝ) - 1, by
        constructor <;> linarith [u.property.1, u.property.2, hu]⟩
      have hmem : α v2 ∈ range (β : unitInterval → X) := ⟨uminus, huv⟩
      have hsingleton : α v2 ∈ ({q} : Set X) := by
        rw [← hmeet]
        exact ⟨⟨v2, rfl⟩, hmem⟩
      have hq : α v2 = q := Set.mem_singleton_iff.mp hsingleton
      have hv' : (v : ℝ) = 1 / 2 := by
        have harg : v2 = 1 := hα (hq.trans α.target.symm)
        have harg' := congrArg (fun z : unitInterval => (z : ℝ)) harg
        dsimp [v2] at harg'
        linarith
      have hu' : (u : ℝ) = 1 / 2 := by
        have hbarg : β uminus = β 0 := huv.trans (hq.trans β.source.symm)
        have harg : uminus = 0 := hβ hbarg
        have harg' := congrArg (fun z : unitInterval => (z : ℝ)) harg
        dsimp [uminus] at harg'
        linarith
      apply Subtype.ext
      linarith
    · let uminus : unitInterval := ⟨2 * (u : ℝ) - 1, by
        constructor <;> linarith [u.property.1, u.property.2, hu]⟩
      let vminus : unitInterval := ⟨2 * (v : ℝ) - 1, by
        constructor <;> linarith [v.property.1, v.property.2, hv]⟩
      have harg : uminus = vminus := hβ huv
      apply Subtype.ext
      have harg' := congrArg (fun z : unitInterval => (z : ℝ)) harg
      dsimp [uminus, vminus] at harg'
      linarith
  refine ⟨(α.trans β).continuous.isClosedEmbedding hγinj |>.isEmbedding, ?_, ?_, ?_⟩
  · simp
  · simp
  · apply Set.Subset.antisymm
    · rintro z ⟨t, rfl⟩
      rw [Path.trans_apply]
      split_ifs
      · exact Or.inl ⟨_, rfl⟩
      · exact Or.inr ⟨_, rfl⟩
    · rintro z (⟨t, rfl⟩ | ⟨t, rfl⟩)
      · let u : unitInterval := ⟨(t : ℝ) / 2, by
          constructor <;> linarith [t.property.1, t.property.2]⟩
        refine ⟨u, ?_⟩
        rw [Path.trans_apply]
        simp only [u]
        split_ifs
        · have hu : (⟨2 * ((t : ℝ) / 2), by
              constructor <;> linarith [t.property.1, t.property.2]⟩ : unitInterval) = t := by
            apply Subtype.ext
            dsimp
            ring
          exact congrArg α hu
        · exfalso; linarith [t.property.2]
      · let u : unitInterval := ⟨((t : ℝ) + 1) / 2, by
          constructor <;> linarith [t.property.1, t.property.2]⟩
        refine ⟨u, ?_⟩
        rw [Path.trans_apply]
        simp only [u]
        split_ifs
        · have ht0 : (t : ℝ) = 0 := by linarith [t.property.1]
          have ht : t = (0 : unitInterval) := by exact Subtype.ext ht0
          subst t
          simp
        · have hu : (⟨2 * (((t : ℝ) + 1) / 2) - 1, by
              constructor <;> linarith [t.property.1, t.property.2]⟩ : unitInterval) = t := by
            apply Subtype.ext
            dsimp
            ring
          exact congrArg β hu



end HolomorphicAnosov.Topology
