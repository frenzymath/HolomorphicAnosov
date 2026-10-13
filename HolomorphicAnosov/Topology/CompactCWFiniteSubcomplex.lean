import Mathlib.Topology.CWComplex.Classical.Subcomplex

/-!
# Compact subsets of CW complexes

This module states `topo.compact_cw_subset_finite_subcomplex`.
Source: A. Hatcher, *Algebraic Topology*, Appendix, Proposition A.1 and
its proof, printed p. 520 (`literature/hatcher-at.pdf`).

The CW structure is on the whole Hausdorff space, `Set.univ`. Cell indices,
open cells, and subcomplexes are Mathlib's native classical CW objects.
`CWComplex.Finite` says that the subcomplex has finitely many cells, not
that its underlying space has finitely many points. There is no bound on
the dimension or number of cells of the ambient complex.
-/

open Set Topology _root_.Topology

namespace HolomorphicAnosov.Topology

private theorem compact_finite_open_cells
    {X : Type*} [TopologicalSpace X] [T2Space X]
    [CWComplex (Set.univ : Set X)] (C : Set X) (hC : IsCompact C) :
    {c : (Σ n : ℕ, RelCWComplex.cell (Set.univ : Set X) n) |
      (C ∩ CWComplex.openCell (C := Set.univ) c.1 c.2).Nonempty}.Finite := by
  classical
  let I := {c : (Σ n : ℕ, RelCWComplex.cell (Set.univ : Set X) n) |
    (C ∩ CWComplex.openCell (C := Set.univ) c.1 c.2).Nonempty}
  choose f hf using fun c : I ↦ c.property
  have hfcell (c : I) : f c ∈ CWComplex.openCell (C := Set.univ) c.val.1 c.val.2 :=
    (hf c).2
  have same_cell {c : I} {n : ℕ} {j : RelCWComplex.cell (Set.univ : Set X) n}
      (h : f c ∈ CWComplex.openCell (C := Set.univ) n j) : c.val = ⟨n, j⟩ := by
    exact RelCWComplex.eq_of_not_disjoint_openCell
      (not_disjoint_iff.mpr ⟨f c, hfcell c, h⟩)
  have hinj : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    exact same_cell (hab.symm ▸ hfcell b)
  have hclosed (T : Set X) (hT : T ⊆ Set.range f) : IsClosed T := by
    apply CWComplex.isClosed_of_isClosed_inter_openCell_or_isClosed_inter_closedCell
      (subset_univ T)
    intro n _ j
    left
    apply Set.Subsingleton.isClosed
    intro x hx y hy
    obtain ⟨a, rfl⟩ := hT hx.1
    obtain ⟨b, rfl⟩ := hT hy.1
    have hab : a = b := Subtype.ext ((same_cell hx.2).trans (same_cell hy.2).symm)
    exact congrArg f hab
  have hcompact : IsCompact (Set.range f) :=
    hC.of_isClosed_subset (hclosed _ (subset_refl _)) (by
      rintro _ ⟨c, rfl⟩
      exact (hf c).1)
  have hdiscrete : IsDiscrete (Set.range f) := by
    apply isDiscrete_iff_forall_mem_exists_isClosed.mpr
    intro T hT
    exact ⟨T, hclosed T hT, inter_eq_left.mpr hT⟩
  have hfin : Finite I := (Set.finite_range_iff hinj).mp (hcompact.finite hdiscrete)
  exact Set.finite_coe_iff.mpr hfin

private theorem finite_cell_envelope
    {X : Type*} [TopologicalSpace X] [T2Space X]
    [CWComplex (Set.univ : Set X)] (n : ℕ)
    (i : RelCWComplex.cell (Set.univ : Set X) n) :
    ∃ S : Finset (Σ m : ℕ, RelCWComplex.cell (Set.univ : Set X) m),
      (⟨n, i⟩ : Σ m, RelCWComplex.cell (Set.univ : Set X) m) ∈ S ∧
      ∀ c ∈ S, CWComplex.closedCell (C := Set.univ) c.1 c.2 ⊆
        ⋃ d ∈ S, CWComplex.openCell (C := Set.univ) d.1 d.2 := by
  classical
  induction n using Nat.strong_induction_on with
  | h n ih =>
    obtain ⟨J, hJ⟩ := CWComplex.cellFrontier_subset_finite_openCell (C := Set.univ) n i
    let L := Σ m : Fin n, {j : RelCWComplex.cell (Set.univ : Set X) m.val // j ∈ J m.val}
    have lower (a : L) := ih a.1.val a.1.isLt a.2.val
    choose S hmem hS using lower
    let U := Finset.univ.biUnion (fun a : L ↦ S a)
    let V := insert (⟨n, i⟩ : Σ m, RelCWComplex.cell (Set.univ : Set X) m) U
    have hUV : U ⊆ V := Finset.subset_insert _ _
    have hSV (a : L) : S a ⊆ V := by
      intro c hc
      apply hUV
      exact Finset.mem_biUnion.mpr ⟨a, Finset.mem_univ a, hc⟩
    have hmono (a : L) :
        (⋃ d ∈ S a, CWComplex.openCell (C := Set.univ) d.1 d.2) ⊆
          ⋃ d ∈ V, CWComplex.openCell (C := Set.univ) d.1 d.2 := by
      exact iUnion₂_subset fun d hd ↦ subset_iUnion₂_of_subset d (hSV a hd) (subset_refl _)
    refine ⟨V, Finset.mem_insert_self _ _, ?_⟩
    intro c hc
    rcases Finset.mem_insert.mp hc with rfl | hc
    · rw [← CWComplex.cellFrontier_union_openCell_eq_closedCell]
      apply union_subset
      · intro x hx
        obtain ⟨m, hmn, j, hj, hxj⟩ := by
          simpa only [mem_iUnion, exists_prop] using hJ hx
        let a : L := ⟨⟨m, hmn⟩, ⟨j, hj⟩⟩
        exact hmono a ((hS a _ (hmem a)) (CWComplex.openCell_subset_closedCell _ _ hxj))
      · exact subset_iUnion₂_of_subset ⟨n, i⟩ (Finset.mem_insert_self _ _) (subset_refl _)
    · obtain ⟨a, _, hca⟩ := Finset.mem_biUnion.mp hc
      exact (hS a c hca).trans (hmono a)

private theorem subcomplex_of_finite_envelope
    {X : Type*} [TopologicalSpace X] [T2Space X]
    [CWComplex (Set.univ : Set X)]
    (S : Finset (Σ m : ℕ, RelCWComplex.cell (Set.univ : Set X) m))
    (hS : ∀ c ∈ S, CWComplex.closedCell (C := Set.univ) c.1 c.2 ⊆
      ⋃ d ∈ S, CWComplex.openCell (C := Set.univ) d.1 d.2) :
    ∃ A : CWComplex.Subcomplex (Set.univ : Set X),
      CWComplex.Finite (A : Set X) ∧
      (A : Set X) = ⋃ d ∈ S, CWComplex.openCell (C := Set.univ) d.1 d.2 := by
  classical
  let E := ⋃ d ∈ S, CWComplex.openCell (C := Set.univ) d.1 d.2
  let I (n : ℕ) := {i : RelCWComplex.cell (Set.univ : Set X) n | (⟨n, i⟩ : Σ m,
    RelCWComplex.cell (Set.univ : Set X) m) ∈ S}
  let A := CWComplex.Subcomplex.mk' (Set.univ : Set X) E I
    (fun n i ↦ hS ⟨n, i.val⟩ i.property) (by
      ext x
      simp only [mem_iUnion, Subtype.exists, mem_ofPred_eq, exists_prop, E, I]
      constructor
      · rintro ⟨n, i, hi, hx⟩
        exact ⟨⟨n, i⟩, hi, hx⟩
      · rintro ⟨⟨n, i⟩, hi, hx⟩
        exact ⟨n, i, hi, hx⟩)
  have hfinite : Finite (Σ n, RelCWComplex.cell (A : Set X) n) := by
    apply Finite.of_injective (fun c ↦ (⟨⟨c.1, c.2.val⟩, c.2.property⟩ : ↑S))
    intro a b hab
    exact Function.injective_id.sigma_map (fun _ ↦ Subtype.val_injective)
      (congrArg Subtype.val hab)
  exact ⟨A, CWComplex.finite_of_finite_cells hfinite, rfl⟩

private theorem finite_cells_subcomplex
    {X : Type*} [TopologicalSpace X] [T2Space X]
    [CWComplex (Set.univ : Set X)]
    (T : Finset (Σ n : ℕ, RelCWComplex.cell (Set.univ : Set X) n)) :
    ∃ A : CWComplex.Subcomplex (Set.univ : Set X),
      CWComplex.Finite (A : Set X) ∧
      ∀ c ∈ T, CWComplex.closedCell (C := Set.univ) c.1 c.2 ⊆ (A : Set X) := by
  classical
  choose S hmem hS using fun c : ↑T ↦ finite_cell_envelope c.val.1 c.val.2
  let U := T.attach.biUnion S
  have hSU (c : ↑T) : S c ⊆ U := by
    intro d hd
    exact Finset.mem_biUnion.mpr ⟨c, Finset.mem_attach _ _, hd⟩
  have hmono (c : ↑T) :
      (⋃ d ∈ S c, CWComplex.openCell (C := Set.univ) d.1 d.2) ⊆
        ⋃ d ∈ U, CWComplex.openCell (C := Set.univ) d.1 d.2 := by
    exact iUnion₂_subset fun d hd ↦ subset_iUnion₂_of_subset d (hSU c hd) (subset_refl _)
  obtain ⟨A, hA, hAU⟩ := subcomplex_of_finite_envelope U (by
    intro d hd
    obtain ⟨c, _, hdc⟩ := Finset.mem_biUnion.mp hd
    exact (hS c d hdc).trans (hmono c))
  refine ⟨A, hA, ?_⟩
  intro c hc
  rw [hAU]
  exact (hS ⟨c, hc⟩ c (hmem ⟨c, hc⟩)).trans (hmono ⟨c, hc⟩)

/-- A compact subset meets only finitely many original open cells and is
contained in a finite native subcomplex. Every original open cell, together
with its closure in the ambient space, is contained in a finite subcomplex.

Proof (Hatcher, Appendix Proposition A.1, printed p. 520): if a compact
set met infinitely many open cells, choose points `x_j` in pairwise distinct
cells and let `S` be their set. Every subset `T` of `S` is closed. Indeed,
induct on the skeleton dimension. The zero-skeleton is discrete. For a
characteristic map of an `n`-disk, the inverse image of `T` on its boundary
is closed by the induction hypothesis, and its inverse image in the
interior has at most one point. Their union is closed in the disk.
The characteristic quotient topology therefore makes `T` intersected
with each skeleton closed. Equivalently, each characteristic pullback
is closed; its image is the intersection of `T` with the corresponding
closed cell. This image is compact and hence closed in the Hausdorff
ambient space. The CW weak-topology criterion then makes `T` closed.
In particular `S` is closed in the compact set and is itself compact,
while the same argument for every subset makes `S` discrete. The cover
by singleton sets forces `S` finite, a contradiction. Thus the set of
cell indices meeting the compact set is finite, across all dimensions.

Induct on the dimension of a cell to contain it in a finite subcomplex.
A zero-cell is already such a subcomplex. In positive dimension the
attaching sphere has compact image in the lower skeleton. The first
part shows that this image meets only finitely many lower-dimensional
cells. By dimension induction these cells lie in finitely many finite
subcomplexes. Their union, with the given cell adjoined, is a finite
subcomplex because it contains the entire attaching image. A subcomplex
is closed, so it contains the closure of the open cell as well; in a
Hausdorff CW complex this is the compact characteristic-disk image.
Finally, take the union of finite subcomplexes for the finitely many
cells meeting the original compact set. Open cells partition the whole
space, so this union contains the compact set. For an empty compact set
take the empty subcomplex; for an empty ambient space the cell assertion
is vacuous. No local finiteness, countability, connectedness, or global
finite-dimensionality assumption enters the argument. -/
theorem compact_cw_subset_finite_subcomplex
    {X : Type*} [TopologicalSpace X] [T2Space X]
    [CWComplex (Set.univ : Set X)]
    (C : Set X) (hC : IsCompact C) :
    {c : (Σ n : ℕ, RelCWComplex.cell (Set.univ : Set X) n) |
      (C ∩ CWComplex.openCell (C := Set.univ) c.1 c.2).Nonempty}.Finite ∧
    (∃ A : CWComplex.Subcomplex (Set.univ : Set X),
      CWComplex.Finite (A : Set X) ∧ C ⊆ (A : Set X)) ∧
    (∀ (n : ℕ) (i : RelCWComplex.cell (Set.univ : Set X) n),
      ∃ A : CWComplex.Subcomplex (Set.univ : Set X),
        CWComplex.Finite (A : Set X) ∧
        CWComplex.openCell (C := Set.univ) n i ⊆ (A : Set X) ∧
        closure (CWComplex.openCell (C := Set.univ) n i) ⊆ (A : Set X)) := by
  classical
  have hfinite := compact_finite_open_cells C hC
  refine ⟨hfinite, ?_, ?_⟩
  · obtain ⟨A, hA, hcover⟩ := finite_cells_subcomplex hfinite.toFinset
    refine ⟨A, hA, ?_⟩
    intro x hx
    have hxuniv : x ∈ (Set.univ : Set X) := mem_univ x
    rw [← CWComplex.iUnion_openCell_eq_complex (C := Set.univ)] at hxuniv
    obtain ⟨n, i, hxi⟩ := by simpa only [mem_iUnion] using hxuniv
    exact hcover ⟨n, i⟩ (hfinite.mem_toFinset.mpr ⟨x, hx, hxi⟩)
      (CWComplex.openCell_subset_closedCell n i hxi)
  · intro n i
    obtain ⟨A, hA, hcover⟩ := finite_cells_subcomplex {⟨n, i⟩}
    have hcell := hcover ⟨n, i⟩ (Finset.mem_singleton_self _)
    refine ⟨A, hA, (CWComplex.openCell_subset_closedCell n i).trans hcell, ?_⟩
    rw [CWComplex.closure_openCell_eq_closedCell]
    exact hcell

end HolomorphicAnosov.Topology
