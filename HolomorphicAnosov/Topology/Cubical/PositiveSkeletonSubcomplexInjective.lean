import HolomorphicAnosov.Topology.Cubical.NativeSubcomplexHomologyMonoG15
import HolomorphicAnosov.Topology.Cubical.RationalSingularHomologyInclusion
import HolomorphicAnosov.Topology.Cubical.OpenCellPartition
import HolomorphicAnosov.Topology.Cubical.SkeletonCompat

/-!
# Positive-degree subcomplex-to-skeleton homology injectivity

Source: Hatcher, *Algebraic Topology*, Lemma 2.34(a), Theorem 2.35,
and the cellular boundary formula, pp.137–141.  In positive degree q, a
subcomplex contained in the q-skeleton has no (q+1)-cells; cellular exactness
therefore makes its q-homology inclusion into the ambient q-skeleton injective.
-/

noncomputable section
open CategoryTheory Set _root_.Topology
namespace HolomorphicAnosov.Cubical

/-- A cubical subcomplex contained in the q-skeleton injects on rational
q-homology when q is positive. -/
theorem cubical_positive_skeleton_subcomplex_injective
    (N : ℕ) (_hN : 1 ≤ N) (K : FiniteRectilinearSubdivision N)
    (q : ℕ) (_hq : q ≤ N) (hqpos : 0 < q)
    (D : CubicalSubcomplex K) (hD : D.carrier ⊆ K.skeleton q) :
    Function.Injective (rationalSingularHomologyInclusion hD q) := by
  classical
  obtain ⟨cw, hfinite, index, hcells⟩ := finiteSubdivision_cwStructure K
  let := cw
  let := hfinite
  let E : RelCWComplex.Subcomplex K.cube.carrier := {
    carrier := D.carrier
    I := fun n ↦ {i | ((index n).symm i).val ∈ D.cells}
    closed' := D.carrier_isClosed
    union' := by
      rw [empty_union]
      ext x
      simp only [Set.mem_iUnion]
      constructor
      · rintro ⟨n, ⟨i, hi⟩, hx⟩
        let c := (index n).symm i
        have hcell := (hcells n c).2
        rw [Equiv.apply_symm_apply] at hcell
        rw [hcell] at hx
        exact mem_iUnion.mpr ⟨c.val, mem_iUnion.mpr ⟨hi, hx.1⟩⟩
      · intro hx
        simp only [CubicalSubcomplex.carrier, mem_iUnion] at hx
        obtain ⟨c, hc, hx⟩ := hx
        obtain ⟨a, ha, hxa⟩ := c.exists_face_mem_openCarrier hx
        have ham : a ∈ D.cells := D.faces c hc a ha
        let ac : {b : ClosedCoordinateCell N // b ∈ K.cells ∧ b.dimension = a.dimension} :=
          ⟨a, D.subset_cells ham, rfl⟩
        refine ⟨a.dimension, ⟨(index a.dimension) ac, ?_⟩, ?_⟩
        · change ((index a.dimension).symm ((index a.dimension) ac)).val ∈ D.cells
          simpa only [Equiv.symm_apply_apply] using ham
        · rw [(hcells a.dimension ac).2]
          exact hxa }
  have hs : (CWComplex.skeleton K.cube.carrier q : Set (Fin N → ℝ)) = K.skeleton q := by
    ext x
    constructor
    · intro hx
      have hx' : x ∈ (CWComplex.skeleton K.cube.carrier (q : ℕ∞) : Set (Fin N → ℝ)) := hx
      obtain ⟨n, hnq, i, hxi⟩ := (CWComplex.mem_skeleton_iff (C := K.cube.carrier) (n := (q : ℕ∞)) (x := x)).mp hx'
      obtain ⟨csub, hi⟩ := (index n).surjective i
      rcases csub with ⟨c, hc, hdim⟩
      rw [← hi] at hxi
      have hbox := (hcells n ⟨c, hc, hdim⟩).2
      rw [hbox] at hxi
      rw [FiniteRectilinearSubdivision.skeleton]
      refine mem_iUnion.mpr ⟨c, ?_⟩
      refine mem_iUnion.mpr ⟨hc, ?_⟩
      exact mem_iUnion.mpr ⟨le_trans (le_of_eq hdim) (by exact_mod_cast hnq), hxi.1⟩
    · intro hx
      rw [FiniteRectilinearSubdivision.skeleton] at hx
      simp only [mem_iUnion, exists_prop] at hx
      obtain ⟨c, hc, hdim, hxi⟩ := hx
      obtain ⟨a, haface, hxa⟩ := c.exists_face_mem_openCarrier hxi
      have hadim : a.dimension ≤ q := le_trans (ClosedCoordinateCell.IsFace.dimension_le haface) hdim
      let i : RelCWComplex.cell K.cube.carrier a.dimension :=
        (index a.dimension) ⟨a, K.faces c hc a haface, rfl⟩
      have hbox := (hcells a.dimension ⟨a, K.faces c hc a haface, rfl⟩).2
      have hopen : x ∈ CWComplex.openCell a.dimension i := by
        rw [hbox]
        exact hxa
      exact (CWComplex.mem_skeleton_iff (C := K.cube.carrier) (n := (q : ℕ∞)) (x := x)).mpr
        ⟨a.dimension, by exact_mod_cast hadim, i, hopen⟩
  have he : (E : Set (Fin N → ℝ)) ⊆ CWComplex.skeleton K.cube.carrier q := by
    rw [hs]
    exact hD
  have hi := nativeSubcomplex_homology_mono K.cube.carrier E q hqpos he
  have hinj : Function.Injective (rationalSingularHomologyInclusion he q) :=
    (ModuleCat.mono_iff_injective _).mp hi
  have hex : ∃ h : D.carrier ⊆ (CWComplex.skeleton K.cube.carrier q : Set (Fin N → ℝ)),
      Function.Injective (rationalSingularHomologyInclusion h q) := ⟨he, hinj⟩
  rw [hs] at hex
  exact hex.choose_spec

end HolomorphicAnosov.Cubical

