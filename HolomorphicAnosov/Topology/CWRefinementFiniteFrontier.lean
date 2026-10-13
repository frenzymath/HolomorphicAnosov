import Mathlib.Topology.CWComplex.Classical.Basic

namespace HolomorphicAnosov
open Set _root_.Topology

/-- Finite subdivision of cells without increasing dimension preserves the
finite lower-dimensional support of every old attaching boundary.

Source context: Fritsch–Piccinini, *Cellular Structures in Topology*,
Lemma 2.3.7 p.67 and the higher-skeleton extension preceding Proposition 2.3.3,
p.65. This explicit carrier-indexed support argument expands the finite
replacement step. Choose a finite old open-cell cover of the boundary. Each
chosen old cell has only finitely many new cells over it. Their finite union
covers the old boundary, and every new dimension is bounded by its carrier's
dimension, which is strictly below the dimension of the old attaching cell.
The new sets need not yet carry a CW structure; this result supplies its
boundary-support axiom for unchanged higher characteristic maps. -/
theorem cw_refinement_finite_frontier
    {X : Type*} [TopologicalSpace X] {C : Set X} [CWComplex C]
    (newCell : ℕ → Type*) (newOpen : (m : ℕ) → newCell m → Set X)
    (carrier : (Σ m, newCell m) → (Σ m, RelCWComplex.cell C m))
    (hdim : ∀ e, e.1 ≤ (carrier e).1)
    (hcover : ∀ e : Σ m, RelCWComplex.cell C m,
      CWComplex.openCell e.1 e.2 =
        ⋃ (f : Σ m, newCell m) (_ : carrier f = e), newOpen f.1 f.2)
    (hfiber : ∀ e, Set.Finite {f | carrier f = e})
    (n : ℕ) (i : RelCWComplex.cell C n) :
    ∃ J : (m : ℕ) → Finset (newCell m),
      CWComplex.cellFrontier n i ⊆ ⋃ (m < n) (j ∈ J m), newOpen m j := by
  classical
  obtain ⟨I, hI⟩ := CWComplex.cellFrontier_subset_finite_openCell n i
  let T : Set (Σ m, newCell m) :=
    ⋃ k ∈ (Finset.range n : Set ℕ), ⋃ j ∈ (I k : Set (RelCWComplex.cell C k)),
      {f | carrier f = ⟨k, j⟩}
  have hT : T.Finite := by
    apply (Finset.finite_toSet (Finset.range n)).biUnion
    intro k hk
    exact (Finset.finite_toSet (I k)).biUnion (fun j hj ↦ hfiber ⟨k, j⟩)
  have hJ (m : ℕ) : (Sigma.mk m ⁻¹' T).Finite :=
    hT.preimage_embedding ⟨Sigma.mk m, sigma_mk_injective⟩
  refine ⟨fun m ↦ (hJ m).toFinset, ?_⟩
  intro x hx
  have hxI := hI hx
  simp only [mem_iUnion] at hxI
  obtain ⟨k, hk, j, hj, hxj⟩ := hxI
  rw [hcover ⟨k, j⟩] at hxj
  simp only [mem_iUnion] at hxj
  obtain ⟨f, hf, hxf⟩ := hxj
  have hfn : f.1 < n := (hdim f).trans_lt (by simpa [hf] using hk)
  have hfT : f ∈ T := by
    simp only [T, mem_iUnion, Finset.mem_coe, Finset.mem_range, mem_ofPred_eq]
    exact ⟨k, hk, j, hj, hf⟩
  simp only [mem_iUnion]
  exact ⟨f.1, hfn, f.2, (hJ f.1).mem_toFinset.mpr hfT, hxf⟩

end HolomorphicAnosov
