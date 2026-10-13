import HolomorphicAnosov.Topology.RelativeTriangleRealization.ClosedDiskPartialEquiv
import Mathlib.Topology.CWComplex.Classical.Finite
import Mathlib.Topology.Homeomorph.Lemmas

noncomputable section
open Set Topology _root_.Topology Metric
namespace HolomorphicAnosov
universe u

/-- Scratch conversion of a finite disk characteristic family to the native
classical CW structure, retaining its labels and maps exactly. This is the
concrete implementation of the characteristic-map definition in Hatcher,
Appendix p.519; the PartialEquiv packaging is an agent-written implementation
lemma and this theorem is not offered as a source-origin DAG node.

Proof: Package each characteristic disk map by closedDiskPartialEquiv.
Its source, continuity, inverse continuity, images, and boundary restrictions
are exactly those in the input. Apply Mathlib CWComplex.mkFinite to these
PartialEquivs. Its cell indices are definitionally the input indices. The
same-instance finite_mkFinite theorem supplies finiteness. -/
theorem finiteClassicalCWOfDisks {X : Type u} [TopologicalSpace X]
    (I : ℕ → Type u) (hfinite : ∀ n, Finite (I n))
    (heventual : ∀ᶠ n in Filter.atTop, IsEmpty (I n))
    (χ : (n : ℕ) → I n → C(closedBall (0 : Fin n → ℝ) 1, X))
    (hemb : ∀ n i, IsEmbedding (fun t : ball (0 : Fin n → ℝ) 1 ↦
      χ n i ⟨t.val, ball_subset_closedBall t.property⟩))
    (hdisjoint : (univ : Set (Σ n, I n)).PairwiseDisjoint
      (fun c ↦ range (fun t : ball (0 : Fin c.1 → ℝ) 1 ↦
        χ c.1 c.2 ⟨t.val, ball_subset_closedBall t.property⟩)))
    (hboundary : ∀ n i (t : sphere (0 : Fin n → ℝ) 1),
      χ n i ⟨t.val, sphere_subset_closedBall t.property⟩ ∈
        ⋃ (m < n) (j : I m), range (χ m j))
    (hcover : (⋃ (n : ℕ) (i : I n), range (χ n i)) = univ) :
    ∃ cw : CWComplex (univ : Set X),
      letI := cw
      RelCWComplex.Finite (univ : Set X) ∧
      ∃ indices : ∀ n, I n ≃ RelCWComplex.cell (univ : Set X) n,
        ∀ n i (t : closedBall (0 : Fin n → ℝ) 1),
          RelCWComplex.map n (indices n i) t.val = χ n i t := by
  classical
  choose e hsource hχ hcont hinv using fun n i ↦ closedDiskPartialEquiv n (χ n i) (hemb n i)
  have himage (n : ℕ) (i : I n) : e n i '' closedBall 0 1 = range (χ n i) := by
    ext x
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact ⟨⟨t,ht⟩, (hχ n i ⟨t,ht⟩).symm⟩
    · rintro ⟨t, rfl⟩
      exact ⟨t.val, t.property, hχ n i t⟩
  have hiimage (n : ℕ) (i : I n) : e n i '' ball 0 1 =
      range (fun t : ball (0 : Fin n → ℝ) 1 ↦
        χ n i ⟨t.val, ball_subset_closedBall t.property⟩) := by
    ext x
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact ⟨⟨t,ht⟩, (hχ n i ⟨t,ball_subset_closedBall ht⟩).symm⟩
    · rintro ⟨t, rfl⟩
      exact ⟨t.val, t.property, hχ n i ⟨t.val,ball_subset_closedBall t.property⟩⟩
  have hd : (univ : Set (Σ n, I n)).PairwiseDisjoint
      (fun c ↦ e c.1 c.2 '' ball 0 1) := by
    simpa only [hiimage] using hdisjoint
  have hb : ∀ n i, MapsTo (e n i) (sphere 0 1)
      (⋃ (m < n) (j : I m), e m j '' closedBall 0 1) := by
    intro n i t ht
    simp only [himage]
    rw [hχ n i ⟨t,sphere_subset_closedBall ht⟩]
    exact hboundary n i ⟨t,ht⟩
  have hc : (⋃ (n : ℕ) (i : I n), e n i '' closedBall 0 1) = univ := by
    simpa only [himage] using hcover
  let cw := CWComplex.mkFinite (univ : Set X) I e heventual hfinite
    hsource hcont hinv hd hb hc
  refine ⟨cw, ?_, fun n ↦ Equiv.refl (I n), ?_⟩
  · exact CWComplex.finite_mkFinite (univ : Set X) I e heventual hfinite
      hsource hcont hinv hd hb hc
  · exact hχ

end HolomorphicAnosov
