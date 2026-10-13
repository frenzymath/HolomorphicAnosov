import HolomorphicAnosov.Topology.BarycentricGeometry.FaceFlag
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Order.Interval.Finset.Fin

/-!
# Permutation enumeration of a maximal opposite-face flag

Node: `topo.maximal_face_flag_permutation_g13`.
Source: Schultz, UCR Mathematics 246A, §I.2 Proposition 3 proof, p.23.
The finite rank-counting proof is an agent-written expansion of the chain-extension
step used by `topo.maximal_cells_coned_eq_g7`.
-/

namespace HolomorphicAnosov.BarycentricGeometry

/-- An n-member flag avoiding one vertex consists of the proper prefixes of a permutation.
Source: Schultz §I.2 Proposition 3 proof, p.23; agent expansion of its finite enumeration.

Comparable faces of equal cardinality coincide. Their nonempty ranks lie between 1 and n,
so the rank map is a bijection onto these n ranks. Choose the face at each rank. These
faces are nested, and each successive difference is a singleton; the first face is also
a singleton. Choose the new vertex at each rank. It belongs to that face and to no lower
face, so the vertices are distinct. Appending the omitted vertex yields an injective
self-map of the finite index set and hence a permutation. Each proper prefix is contained
in its corresponding ranked face and has the same cardinality, so the two are equal.
All ranks occur, giving equality of the finite families. In dimension zero the flag
nonemptiness and the assumed zero cardinality are inconsistent; no extra premise is used. -/
theorem maximal_face_flag_permutation {n : ℕ} (C : FaceFlag n)
    (i : Fin (n + 1)) (hc : C.finset.card = n)
    (ha : ∀ F ∈ C.finset, i ∉ F.val) :
    ∃ σ : Equiv.Perm (Fin (n + 1)),
      C.finset.image Subtype.val =
        Finset.univ.image (fun k : Fin n => (Finset.Iic k.castSucc).image σ) := by
  classical
  have hci : Function.Injective (fun F : C.finset ↦ F.val.val.card) := by
    intro F G he
    apply Subtype.ext
    apply Subtype.ext
    rcases C.comparable F G with h | h
    · exact Finset.eq_of_subset_of_card_le h he.ge
    · exact (Finset.eq_of_subset_of_card_le h he.le).symm
  have hb (F : C.finset) : 1 ≤ F.val.val.card ∧ F.val.val.card ≤ n := by
    refine ⟨Finset.card_pos.mpr F.val.property, ?_⟩
    have hsub : F.val.val ⊆ Finset.univ.erase i := by
      intro x hx
      exact Finset.mem_erase.mpr ⟨fun h ↦ ha F.val F.property (h ▸ hx),
        Finset.mem_univ _⟩
    simpa using Finset.card_le_card hsub
  let r : C.finset → Fin n := fun F ↦ ⟨F.val.val.card - 1, by
    have := hb F
    omega⟩
  have hri : Function.Injective r := by
    intro F G he
    apply hci
    have := congrArg Fin.val he
    have := hb F
    have := hb G
    dsimp [r] at *
    omega
  let e : C.finset ≃ Fin n := Fintype.equivFinOfCardEq
    ((Fintype.card_coe C.finset).trans hc)
  have hrs : Function.Surjective r := by
    have hs := Finite.surjective_of_injective (hri.comp e.symm.injective)
    intro k
    obtain ⟨j, hj⟩ := hs k
    exact ⟨e.symm j, hj⟩
  let P : Fin n → C.finset := fun k ↦ Classical.choose (hrs k)
  have hrP (k : Fin n) : r (P k) = k := Classical.choose_spec (hrs k)
  have hPc (k : Fin n) : (P k).val.val.card = k.val + 1 := by
    have h := congrArg Fin.val (hrP k)
    have := hb (P k)
    dsimp [r] at h
    omega
  have hPs : Function.Surjective P := by
    intro F
    exact ⟨r F, hri (hrP (r F))⟩
  have hPm {k l : Fin n} (hkl : k ≤ l) : (P k).val.val ⊆ (P l).val.val := by
    rcases C.comparable (P k) (P l) with h | h
    · exact h
    · have he := Finset.eq_of_subset_of_card_le h (by
        rw [hPc, hPc]
        exact Nat.add_le_add_right hkl 1)
      exact he.symm.subset
  have hnew (k : Fin n) : ∃ v : Fin (n + 1), v ∈ (P k).val.val ∧
      ∀ j : Fin n, j < k → v ∉ (P j).val.val := by
    by_cases hk : k.val = 0
    · obtain ⟨v, hv⟩ := (P k).val.property
      refine ⟨v, hv, ?_⟩
      intro j hj
      have : j.val < k.val := hj
      omega
    · let j : Fin n := ⟨k.val - 1, by omega⟩
      have hjk : j ≤ k := by change k.val - 1 ≤ k.val; omega
      have hdiff : ((P k).val.val \ (P j).val.val).card = 1 := by
        rw [Finset.card_sdiff_of_subset (hPm hjk), hPc, hPc]
        dsimp [j]
        omega
      obtain ⟨v, hv⟩ := Finset.card_eq_one.mp hdiff
      have hvm : v ∈ (P k).val.val \ (P j).val.val := by rw [hv]; simp
      obtain ⟨hvk, hvj⟩ := Finset.mem_sdiff.mp hvm
      refine ⟨v, hvk, ?_⟩
      intro l hl hvl
      exact hvj (hPm (show l ≤ j by change l.val ≤ k.val - 1; have := hl; omega) hvl)
  choose v hvm hvlow using hnew
  have hvi : Function.Injective v := by
    intro j k he
    by_contra hn
    rcases lt_or_gt_of_ne hn with h | h
    · exact hvlow k j h (he ▸ hvm j)
    · exact hvlow j k h (he.symm ▸ hvm k)
  have hvi' (k : Fin n) : v k ≠ i := fun h ↦ ha (P k).val (P k).property (h ▸ hvm k)
  let f : Fin (n + 1) → Fin (n + 1) := Fin.lastCases i v
  have hfi : Function.Injective f := by
    intro x
    refine Fin.lastCases ?_ (fun x ↦ ?_) x
    · intro y
      refine Fin.lastCases ?_ (fun y ↦ ?_) y
      · intro _; rfl
      · intro h
        exact False.elim (hvi' y (by simpa [f] using h.symm))
    · intro y
      refine Fin.lastCases ?_ (fun y ↦ ?_) y
      · intro h
        exact False.elim (hvi' x (by simpa [f] using h))
      · intro h
        exact congrArg Fin.castSucc (hvi (by simpa [f] using h))
  let σ : Equiv.Perm (Fin (n + 1)) :=
    Equiv.ofBijective f ⟨hfi, Finite.surjective_of_injective hfi⟩
  have hσ (k : Fin n) : σ k.castSucc = v k := by change f k.castSucc = v k; simp [f]
  have hprefix (k : Fin n) : (Finset.Iic k.castSucc).image σ = (P k).val.val := by
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx
      have hjk : j.val ≤ k.val := (Finset.mem_Iic.mp hj : j ≤ k.castSucc)
      let j' : Fin n := ⟨j.val, lt_of_le_of_lt hjk k.isLt⟩
      have hj' : j = j'.castSucc := Fin.ext rfl
      rw [hj', hσ]
      exact hPm (show j' ≤ k from hjk) (hvm j')
    · rw [hPc, Finset.card_image_of_injective _ σ.injective, Fin.card_Iic]
      rfl
  refine ⟨σ, ?_⟩
  ext F
  constructor
  · intro hF
    obtain ⟨F, hFC, rfl⟩ := Finset.mem_image.mp hF
    obtain ⟨k, hk⟩ := hPs ⟨F, hFC⟩
    exact Finset.mem_image.mpr ⟨k, Finset.mem_univ _, (hprefix k).trans (congrArg
      (fun A : C.finset ↦ A.val.val) hk)⟩
  · intro hF
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hF
    exact Finset.mem_image.mpr ⟨(P k).val, (P k).property, (hprefix k).symm⟩

end HolomorphicAnosov.BarycentricGeometry

