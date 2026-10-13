import HolomorphicAnosov.Topology.Homology.CompactSupportUnionGluing
import Mathlib.Topology.Compactness.LocallyCompact

namespace HolomorphicAnosov
open CategoryTheory HolomorphicAnosov.Topology _root_.Topology
universe u

/-- Locally compatible point-supported classes glue over a compact support if point
restrictions detect classes on all its compact subsets.

Agent-written abstract gluing criterion, following Hatcher, *Algebraic Topology*,
the local section convention pp.233–234 and Lemma 3.27 steps (1) and (2), p.237.
The source does not state this general criterion separately.
Choose a finite compact cover of K subordinate
to neighborhoods carrying the prescribed classes. Restrict those neighborhood
classes to the pieces. For two partial unions their classes agree on the compact
intersection because every point restriction agrees and point restrictions detect
the difference. The support Mayer–Vietoris sequence therefore glues the two classes.
Induction gives a class on K; point detection on K proves uniqueness. Compact
neighborhoods are chosen in the compact Hausdorff subtype K, so ambient local
compactness, a manifold structure, positive degree and nonempty K are unnecessary.
-/
theorem compact_support_class_of_local_compatibility
    (X : TopCat.{u}) [T2Space X] (R : ModuleCat.{u} ℤ) (q : ℕ)
    (K : Set X) (hK : IsCompact K)
    (hdetect : ∀ A : Set X, A ⊆ K → IsCompact A →
      ∀ a : supportSingularHomology X A R q,
      (∀ (x : X) (hx : x ∈ A), supportSingularHomologyRestrict X R
        (Set.singleton_subset_iff.mpr hx) q a = 0) → a = 0)
    (α : ∀ x : X, supportSingularHomology X {x} R q)
    (hα : ∀ (x : X), x ∈ K → ∃ W : Set X, IsOpen W ∧ x ∈ W ∧
      ∃ aW : supportSingularHomology X W R q,
      ∀ (y : X) (hy : y ∈ W), supportSingularHomologyRestrict X R
        (Set.singleton_subset_iff.mpr hy) q aW = α y) :
    ∃! aK : supportSingularHomology X K R q, ∀ (x : X) (hx : x ∈ K),
      supportSingularHomologyRestrict X R (Set.singleton_subset_iff.mpr hx) q aK = α x := by
  classical
  let H (A : Set X) := supportSingularHomology X A R q
  let res {A B : Set X} (h : B ⊆ A) := supportSingularHomologyRestrict X R h q
  have comp {A B C : Set X} (hBA : B ⊆ A) (hCB : C ⊆ B) (a : H A) :
      res hCB (res hBA a) = res (hCB.trans hBA) a := by
    have hpair : supportSingularPairMap A B (𝟙 X) (fun _ hx hb ↦ hx (hBA hb)) ≫
        supportSingularPairMap B C (𝟙 X) (fun _ hx hc ↦ hx (hCB hc)) =
        supportSingularPairMap A C (𝟙 X) (fun _ hx hc ↦ hx (hBA (hCB hc))) := by
      ext <;> rfl
    have norm {B C : Set X} (h : C ⊆ B) : res h =
        (SSetPair.homologyMap
          (supportSingularPairMap B C (𝟙 X) (fun _ hx hc ↦ hx (h hc))) R q
          ).hom.toAddMonoidHom := by
      simp [res, supportSingularHomologyRestrict, supportSingularHomologyMap]
    rw [norm, norm, norm]
    change (SSetPair.homologyMap _ R q ≫ SSetPair.homologyMap _ R q) a = _
    rw [← SSetPair.homologyMap_comp, hpair]
    rfl
  let Good (A : Set X) := ∃ a : H A, ∀ (x : X) (hx : x ∈ A),
    res (Set.singleton_subset_iff.mpr hx) a = α x
  have union_good (A B : Set X) (hAK : A ⊆ K) (hBK : B ⊆ K)
      (hcA : IsCompact A) (hcB : IsCompact B) (ha : Good A) (hb : Good B) :
      Good (A ∪ B) := by
    obtain ⟨a, ha⟩ := ha
    obtain ⟨b, hb⟩ := hb
    have hab : res (A := A) Set.inter_subset_left a =
        res (A := B) Set.inter_subset_right b := by
      apply sub_eq_zero.mp
      apply hdetect (A ∩ B) (Set.inter_subset_left.trans hAK) (hcA.inter_right hcB.isClosed)
      intro x hx
      rw [map_sub, comp, comp]
      exact sub_eq_zero.mpr ((ha x hx.1).trans (hb x hx.2).symm)
    let D : CompactSupportMVData.{u} := ⟨X, inferInstance, A, B, hcA, hcB, R⟩
    obtain ⟨c, hcA, hcB⟩ := compact_support_union_classes_glue D q a b hab
    refine ⟨c, ?_⟩
    intro x hx
    rcases hx with hx | hx
    · rw [← comp Set.subset_union_left (Set.singleton_subset_iff.mpr hx) c, hcA]
      exact ha x hx
    · rw [← comp Set.subset_union_right (Set.singleton_subset_iff.mpr hx) c, hcB]
      exact hb x hx
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK
  choose W hW hxW aW haW using fun x : K ↦ hα x x.property
  have hn (x : K) : ∃ C : Set K, IsCompact C ∧ x ∈ interior C ∧
      C ⊆ Subtype.val ⁻¹' W x :=
    exists_compact_subset ((hW x).preimage continuous_subtype_val) (hxW x)
  choose C hC hxC hCW using hn
  obtain ⟨s, hs⟩ := (isCompact_univ : IsCompact (Set.univ : Set K)).elim_finite_subcover
    (fun x : K ↦ interior (C x)) (fun _ ↦ isOpen_interior)
    (fun x _ ↦ Set.mem_iUnion.mpr ⟨x, hxC x⟩)
  let F (x : K) : Set X := Subtype.val '' C x
  have hcF (x : K) : IsCompact (F x) := (hC x).image continuous_subtype_val
  have hFK (x : K) : F x ⊆ K := by
    rintro _ ⟨z, _, rfl⟩
    exact z.property
  have hFW (x : K) : F x ⊆ W x := by
    rintro _ ⟨z, hz, rfl⟩
    exact hCW x hz
  have goodF (x : K) : Good (F x) := by
    refine ⟨res (hFW x) (aW x), ?_⟩
    intro y hy
    rw [comp]
    exact haW x y (hFW x hy)
  have cover : (⋃ x ∈ s, F x) = K := by
    apply Set.Subset.antisymm
    · intro x hx
      obtain ⟨y, _, hy⟩ := Set.mem_iUnion₂.mp hx
      exact hFK y hy
    · intro x hx
      obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.mp (hs (Set.mem_univ (⟨x, hx⟩ : K)))
      exact Set.mem_iUnion₂.mpr ⟨y, hy, ⟨⟨x, hx⟩, interior_subset hxy, rfl⟩⟩
  have goodUnion : Good (⋃ x ∈ s, F x) := by
    clear cover hs
    induction s using Finset.induction_on with
    | empty =>
      simp only [Finset.notMem_empty, Set.iUnion_of_empty, Set.iUnion_empty]
      exact ⟨0, fun x hx ↦ hx.elim⟩
    | @insert x s hx ih =>
      have hsub : (⋃ y ∈ s, F y) ⊆ K := by
        intro z hz
        obtain ⟨y, _, hy⟩ := Set.mem_iUnion₂.mp hz
        exact hFK y hy
      have hcompact : IsCompact (⋃ y ∈ s, F y) := s.isCompact_biUnion (fun y _ ↦ hcF y)
      simpa only [Finset.set_biUnion_insert] using
        union_good (F x) (⋃ y ∈ s, F y) (hFK x) hsub (hcF x) hcompact (goodF x) ih
  rw [cover] at goodUnion
  obtain ⟨a, ha⟩ := goodUnion
  refine ⟨a, ha, ?_⟩
  intro b hb
  apply sub_eq_zero.mp
  apply hdetect K (Set.Subset.refl K) hK
  intro x hx
  rw [map_sub, hb x hx, ha x hx, sub_self]

end HolomorphicAnosov

