import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Separation.Basic
import Mathlib.Topology.Instances.Real.Lemmas
open Set Filter Topology _root_.Topology
namespace HolomorphicAnosov

/-- A continuous path starting in an open set and ending outside it has a first exit time at which
it meets the frontier. (Hirsch–Pugh–Shub, Thm (6.7), p.86; Lee, §11, pp.275–279) -/
theorem exists_first_exit_time
    {X : Type*} [TopologicalSpace X]
    {S : Set X} (hS : IsOpen S)
    {γ : ℝ → X} {a b : ℝ} (hab : a < b)
    (hγ : ContinuousOn γ (Icc a b)) (hstart : γ a ∈ S)
    (hend : γ b ∉ S) :
    ∃ τ ∈ Icc a b, a < τ ∧ γ τ ∈ frontier S ∧
      ∀ t ∈ Icc a τ, t ≠ τ → γ t ∈ S := by
  let I : Set ℝ := Icc a b
  let : CompactSpace I := isCompact_iff_compactSpace.mp isCompact_Icc
  let γI : I → X := I.domRestrict γ
  have hγI : Continuous γI := continuousOn_iff_continuous_domRestrict.mp hγ
  let K : Set I := γI ⁻¹' Sᶜ
  have hKclosed : IsClosed K := IsClosed.preimage hγI hS.isClosed_compl
  have hKcompact : IsCompact K := hKclosed.isCompact
  have hEcompact : IsCompact (Subtype.val '' K) := hKcompact.image continuous_subtype_val
  have hEeq : Subtype.val '' K = {t ∈ Icc a b | γ t ∉ S} := by
    ext t
    constructor
    · rintro ⟨q, hq, rfl⟩
      exact ⟨q.property, hq⟩
    · rintro ⟨ht, hnot⟩
      exact ⟨⟨t, ht⟩, hnot, rfl⟩
  obtain ⟨τ, hτleast⟩ := hEcompact.exists_isLeast (by
    rw [hEeq]
    exact ⟨b, ⟨hab.le, le_rfl⟩, hend⟩)
  have hτimage : τ ∈ Subtype.val '' K := hτleast.1
  rw [hEeq] at hτimage
  have hτE : τ ∈ Icc a b := hτimage.1
  have hτout : γ τ ∉ S := hτimage.2
  have hτa : a ≤ τ := hτE.1
  have hτb : τ ≤ b := hτE.2
  have hτgt : a < τ := by
    by_contra hnot
    have hτeq : τ = a := le_antisymm (le_of_not_gt hnot) hτa
    exact (hτeq ▸ hτout) hstart
  have hleastE : ∀ t ∈ Icc a b, γ t ∉ S → τ ≤ t := by
    intro t ht hnot
    exact hτleast.2 (by rw [hEeq]; exact ⟨ht, hnot⟩)
  have hτclosure : γ τ ∈ closure S := by
    rw [mem_closure_iff_nhds]
    intro V hV
    have hpre : γ ⁻¹' V ∈ 𝓝[Icc a b] τ :=
      (hγ.continuousWithinAt hτE).preimage_mem_nhdsWithin hV
    obtain ⟨W, hW, hWsub⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hpre
    have hnotmin : ¬ IsMin τ := not_isMin_iff.mpr ⟨a, hτgt⟩
    have hW' : W ∩ Ioi a ∈ 𝓝 τ := inter_mem hW (Ioi_mem_nhds hτgt)
    obtain ⟨t, htW', htlt⟩ := nonempty_nhds_inter_Iio hW' hnotmin
    have htW : t ∈ W := htW'.1
    have htI : t ∈ Icc a b := ⟨le_of_lt htW'.2, le_trans (le_of_lt htlt) hτb⟩
    have htS : γ t ∈ S := by
      by_contra hnot
      exact (not_lt_of_ge (hleastE t htI hnot)) htlt
    exact ⟨γ t, hWsub ⟨htW, htI⟩, htS⟩
  refine ⟨τ, hτE, ?_, ?_, ?_⟩
  · exact hτgt
  · rw [frontier, hS.interior_eq]
    exact ⟨hτclosure, hτout⟩
  · intro t ht hteq
    by_contra hnotS
    exact (not_lt_of_ge (hleastE t ⟨ht.1, le_trans ht.2 hτb⟩ hnotS))
      (lt_of_le_of_ne ht.2 hteq)

end HolomorphicAnosov
