import HolomorphicAnosov.Topology.PathsHomotopicInSimplyConnectedMember
import Mathlib.Topology.Subpath

namespace HolomorphicAnosov
open Set

/-- Given two open cover sets with path-connected intersection and simply connected second set, a path in the first set can be replaced by a homotopic path in the first set. (Hatcher, Lemma 1.15) -/
theorem openCover_path_replacement
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsOpen A) (hBopen : IsOpen B) (hcover : A ∪ B = univ)
    (hAB : IsPathConnected (A ∩ B)) (hB : IsSimplyConnected B)
    {x y : X} (hx : x ∈ A) (hy : y ∈ A) (γ : Path x y) :
    ∃ δ : Path x y, (∀ t, δ t ∈ A) ∧ δ.Homotopic γ := by
  classical
  let U : Bool → Set X := fun b ↦ if b then A else B
  have hUopen : ∀ b, IsOpen (U b) := by intro b; cases b <;> assumption
  have hUcover : ∀ z, ∃ b, z ∈ U b := by
    intro z
    have hz : z ∈ A ∪ B := hcover.symm ▸ mem_univ z
    rcases hz with hz | hz
    · exact ⟨true, hz⟩
    · exact ⟨false, hz⟩
  obtain ⟨s, hs0, hsmono, ⟨N, hsN⟩, hsub⟩ :=
    exists_monotone_Icc_subset_open_cover_unitInterval
      (fun b ↦ (hUopen b).preimage γ.continuous)
      (fun t _ ↦ mem_iUnion.mpr (hUcover (γ t)))
  let Q := @Path.Homotopic.Quotient.mk X _
  have hmem {a b c : X} {S : Set X} (p : Path a b) (q : Path b c)
      (hp : ∀ t, p t ∈ S) (hq : ∀ t, q t ∈ S) : ∀ t, (p.trans q) t ∈ S := by
    apply range_subset_iff.mp
    rw [Path.trans_range]
    exact union_subset (range_subset_iff.mpr hp) (range_subset_iff.mpr hq)
  have hpart : ∀ k,
      (∃ δ : Path (γ (s 0)) (γ (s k)), (∀ t, δ t ∈ A) ∧
        Q δ = Q (γ.subpath (s 0) (s k))) ∨
      (∃ z ∈ A ∩ B, ∃ δ : Path (γ (s 0)) z, ∃ β : Path z (γ (s k)),
        (∀ t, δ t ∈ A) ∧ (∀ t, β t ∈ B) ∧
        (Q δ).trans (Q β) = Q (γ.subpath (s 0) (s k))) := by
    intro k
    induction k with
    | zero =>
        left
        refine ⟨Path.refl _, ?_, ?_⟩
        · intro t; simpa [hs0] using hx
        · simp [Q]
    | succ k ih =>
        obtain ⟨b, hb⟩ := hsub k
        let p := γ.subpath (s k) (s (k + 1))
        have hp : ∀ t, p t ∈ U b := by
          intro t
          have ht : p t ∈ γ '' Icc (s k) (s (k + 1)) := by
            rw [← γ.range_subpath_of_le _ _ (hsmono (Nat.le_succ k))]
            exact mem_range_self t
          rcases ht with ⟨a, ha, he⟩
          exact he ▸ hb ha
        have hjoin : (Q (γ.subpath (s 0) (s k))).trans (Q p) =
            Q (γ.subpath (s 0) (s (k + 1))) :=
          Path.Homotopic.mk_subpath_trans_mk_subpath γ _ _ _
        cases b with
        | true =>
          change ∀ t, p t ∈ A at hp
          left
          rcases ih with ⟨δ, hδ, he⟩ | ⟨z, hz, δ, β, hδ, hβ, he⟩
          · exact ⟨δ.trans p, hmem δ p hδ hp, by change (Q δ).trans (Q p) = _; rw [he]; exact hjoin⟩
          · have hk : γ (s k) ∈ A ∩ B := ⟨by simpa using hp 0, by simpa using hβ 1⟩
            obtain ⟨η, hη⟩ := hAB.joinedIn z hz (γ (s k)) hk
            have hηβ := sphere_paths_homotopic_in_member hB η β (fun t ↦ (hη t).2) hβ
            refine ⟨(δ.trans η).trans p, hmem _ _ (hmem _ _ hδ (fun t ↦ (hη t).1)) hp, ?_⟩
            change ((Q δ).trans (Q η)).trans (Q p) = _
            have heη : Q η = Q β := Path.Homotopic.Quotient.eq.mpr hηβ
            rw [heη, he]
            exact hjoin
        | false =>
          change ∀ t, p t ∈ B at hp
          right
          rcases ih with ⟨δ, hδ, he⟩ | ⟨z, hz, δ, β, hδ, hβ, he⟩
          · refine ⟨γ (s k), ⟨by simpa using hδ 1, by simpa using hp 0⟩, δ, p, hδ, hp, ?_⟩
            rw [he]; exact hjoin
          · refine ⟨z, hz, δ, β.trans p, hδ, hmem _ _ hβ hp, ?_⟩
            change (Q δ).trans ((Q β).trans (Q p)) = _
            rw [← Path.Homotopic.Quotient.trans_assoc, he]
            exact hjoin
  have hfinish : ∃ δ : Path (γ (s 0)) (γ (s N)), (∀ t, δ t ∈ A) ∧
      δ.Homotopic (γ.subpath (s 0) (s N)) := by
    rcases hpart N with ⟨δ, hδ, he⟩ | ⟨z, hz, δ, β, hδ, hβ, he⟩
    · exact ⟨δ, hδ, Path.Homotopic.Quotient.eq.mp he⟩
    · have hN : γ (s N) ∈ A ∩ B :=
        ⟨by simpa [hsN N le_rfl] using hy, by simpa using hβ 1⟩
      obtain ⟨η, hη⟩ := hAB.joinedIn z hz (γ (s N)) hN
      have hηβ := sphere_paths_homotopic_in_member hB η β (fun t ↦ (hη t).2) hβ
      refine ⟨δ.trans η, hmem _ _ hδ (fun t ↦ (hη t).1), ?_⟩
      apply Path.Homotopic.Quotient.eq.mp
      change (Q δ).trans (Q η) = _
      have heη : Q η = Q β := Path.Homotopic.Quotient.eq.mpr hηβ
      rw [heη]
      exact he
  rw [hs0, hsN N le_rfl, Path.subpath_zero_one] at hfinish
  obtain ⟨δ, hδ, he⟩ := hfinish
  refine ⟨δ.cast γ.source.symm γ.target.symm, hδ, ?_⟩
  convert he.pathCast γ.source.symm γ.target.symm using 1
  ext t
  rfl

end HolomorphicAnosov
