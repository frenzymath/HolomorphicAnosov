import HolomorphicAnosov.Topology.GoodPairCollapse
import Mathlib.Topology.CWComplex.Classical.Subcomplex
import Mathlib.Topology.Homeomorph.Lemmas

open Set Topology _root_.Topology

namespace HolomorphicAnosov

/-- The collapse of a subcomplex containing every vertex of a CW graph is
presented by one root point and the original closed characteristic intervals
of the complementary edges. The presentation map is a quotient map for the
original topology. Its root fibre is exactly the interval boundaries, and
distinct interior coordinates retain their original edge labels. It induces
a homeomorphism from the explicit weak wedge (the disjoint union of these
intervals and one point, with their boundaries collapsed together).

Source: Hatcher, Algebraic Topology, graph quotient/weak topology p.83 and
Proposition 1A.2 proof p.85, with the quotient definition of an arbitrary
wedge on p.10. Surjectivity follows from the original closed-cell
cover. For the quotient criterion, a closed pullback on the disjoint union
has closed pullback on every complementary interval. The other characteristic
disks map constantly to the root. Each closed-cell intersection is the image
of a closed subset of its compact disk, hence closed in the Hausdorff ambient
space. The CW closed-set criterion and the collapse quotient criterion give
the assertion. The boundary of every one-cell consists of zero-cells and is
therefore collapsed. The open-cell disjointness and characteristic-map
injectivity show that no other points are identified. Descending the
presentation gives an injective quotient map, hence a homeomorphism.
No finiteness or countability is imposed. -/
theorem cw_graph_collapse_presentation
    {X : Type*} [TopologicalSpace X] [T2Space X]
    [CWComplex (Set.univ : Set X)]
    (hdim : ∀ n : ℕ, 1 < n → IsEmpty (RelCWComplex.cell (Set.univ : Set X) n))
    (T : RelCWComplex.Subcomplex (Set.univ : Set X))
    (hT0 : T.I 0 = Set.univ) (a : (T : Set X)) :
    let E := {e : RelCWComplex.cell (Set.univ : Set X) 1 // e ∉ T.I 1}
    let D := Metric.closedBall (0 : Fin 1 → ℝ) 1
    let π : Unit ⊕ (Σ _ : E, D) → GoodPair.Collapsed (T : Set X) :=
      Sum.elim (fun _ => GoodPair.collapse (T : Set X) a.val)
        (fun p => GoodPair.collapse (T : Set X) (RelCWComplex.map 1 p.1.val p.2.val))
    let B : Set (Unit ⊕ (Σ _ : E, D)) :=
      {p | Sum.elim (fun _ => True) (fun p => ‖p.2.val‖ = 1) p}
    IsQuotientMap π ∧
      (∀ (e : E) (z : D), π (.inr ⟨e, z⟩) = π (.inl Unit.unit) ↔ ‖z.val‖ = 1) ∧
      (∀ (e f : E) (z w : D), ‖z.val‖ < 1 → ‖w.val‖ < 1 →
        (π (.inr ⟨e, z⟩) = π (.inr ⟨f, w⟩) ↔ e = f ∧ z = w)) ∧
      ∃ h : GoodPair.Collapsed B ≃ₜ GoodPair.Collapsed (T : Set X),
        ∀ p, h (GoodPair.collapse B p) = π p := by
  classical
  dsimp only
  let q := GoodPair.collapse (T : Set X)
  let E := {e : RelCWComplex.cell (Set.univ : Set X) 1 // e ∉ T.I 1}
  let D := Metric.closedBall (0 : Fin 1 → ℝ) 1
  let π : Unit ⊕ (Σ _ : E, D) → GoodPair.Collapsed (T : Set X) :=
    Sum.elim (fun _ => q a.val) (fun p => q (RelCWComplex.map 1 p.1.val p.2.val))
  let B : Set (Unit ⊕ (Σ _ : E, D)) :=
    {p | Sum.elim (fun _ => True) (fun p => ‖p.2.val‖ = 1) p}
  change IsQuotientMap π ∧ _
  have hcollapse : ∀ x ∈ (T : Set X), q x = q a.val := by
    intro x hx
    exact Quotient.sound (Or.inr ⟨hx, a.property⟩)
  have hzero : ∀ i : RelCWComplex.cell (Set.univ : Set X) 0,
      RelCWComplex.closedCell 0 i ⊆ (T : Set X) := by
    intro i
    exact T.closedCell_subset_of_mem (by rw [hT0]; trivial)
  have hπ : Continuous π := by
    apply continuous_sum_dom.mpr
    constructor
    · exact continuous_const
    · apply continuous_sigma
      intro e
      exact q.continuous.comp (RelCWComplex.continuousOn 1 e.val).domRestrict
  have hsurj : Function.Surjective π := by
    intro y
    induction y using Quotient.inductionOn with
    | h x =>
      by_cases hx : x ∈ (T : Set X)
      · exact ⟨.inl Unit.unit, (hcollapse x hx).symm⟩
      · have hcover : x ∈ ⋃ (n : ℕ) (i : RelCWComplex.cell (Set.univ : Set X) n),
            RelCWComplex.closedCell n i := by rw [CWComplex.union]; trivial
        obtain ⟨n, hn⟩ := mem_iUnion.mp hcover
        obtain ⟨i, z, hz, hzx⟩ := mem_iUnion.mp hn
        cases n with
        | zero => exact False.elim (hx (hzero i ⟨z, hz, hzx⟩))
        | succ n =>
          cases n with
          | zero =>
            have hi : i ∉ T.I 1 := by
              intro hi
              exact hx (T.closedCell_subset_of_mem hi ⟨z, hz, hzx⟩)
            exact ⟨.inr ⟨⟨i, hi⟩, ⟨z, hz⟩⟩, congrArg q hzx⟩
          | succ n =>
            have := hdim (n + 2) (by omega)
            exact isEmptyElim i
  have hquot : IsQuotientMap π := by
    apply isQuotientMap_iff_isClosed.mpr
    refine ⟨hsurj, fun B => ⟨fun hB => hB.preimage hπ, ?_⟩⟩
    intro hB
    apply isQuotientMap_quotient_mk'.isClosed_preimage.mp
    change IsClosed (q ⁻¹' B)
    apply (CWComplex.closed Set.univ _ (subset_univ _)).mpr
    intro n i
    let disk := Metric.closedBall (0 : Fin n → ℝ) 1
    let χ : C(disk, X) :=
      ⟨fun z => RelCWComplex.map n i z.val, (RelCWComplex.continuousOn n i).domRestrict⟩
    have hpre : IsClosed ((fun z : disk => q (χ z)) ⁻¹' B) := by
      cases n with
      | zero =>
        have hc : ∀ z : disk, q (χ z) = q a.val :=
          fun z => hcollapse _ (hzero i ⟨z.val, z.property, rfl⟩)
        by_cases ha : q a.val ∈ B
        · simp [Set.preimage, hc, ha]
        · simp [Set.preimage, hc, ha]
      | succ n =>
        cases n with
        | zero =>
          by_cases hi : i ∈ T.I 1
          · have hc : ∀ z : disk, q (χ z) = q a.val :=
              fun z => hcollapse _ (T.closedCell_subset_of_mem hi ⟨z.val, z.property, rfl⟩)
            by_cases ha : q a.val ∈ B
            · simp [Set.preimage, hc, ha]
            · simp [Set.preimage, hc, ha]
          · exact hB.preimage (continuous_inr.comp (continuous_sigmaMk (i := (⟨i, hi⟩ : E))))
        | succ n =>
          have := hdim (n + 2) (by omega)
          exact isEmptyElim i
    have : CompactSpace disk := isCompact_iff_compactSpace.mp (isCompact_closedBall _ _)
    have heq : q ⁻¹' B ∩ RelCWComplex.closedCell n i =
        χ '' ((fun z : disk => q (χ z)) ⁻¹' B) := by
      ext x
      constructor
      · rintro ⟨hx, z, hz, hzx⟩
        exact ⟨⟨z, hz⟩, by change q (RelCWComplex.map n i z) ∈ B; rw [hzx]; exact hx, hzx⟩
      · rintro ⟨z, hz, rfl⟩
        exact ⟨hz, ⟨z.val, z.property, rfl⟩⟩
    rw [heq]
    exact (hpre.isCompact.image χ.continuous).isClosed
  have hfib :
      (∀ (e : E) (z : D), π (.inr ⟨e, z⟩) = π (.inl Unit.unit) ↔ ‖z.val‖ = 1) ∧
      (∀ (e f : E) (z w : D), ‖z.val‖ < 1 → ‖w.val‖ < 1 →
        (π (.inr ⟨e, z⟩) = π (.inr ⟨f, w⟩) ↔ e = f ∧ z = w)) := by
    have hinterior : ∀ (e : E) (z : D), ‖z.val‖ < 1 →
        RelCWComplex.map 1 e.val z.val ∈ RelCWComplex.openCell 1 e.val := by
      intro e z hz
      exact ⟨z.val, by simpa only [Metric.mem_ball, dist_zero_right] using hz, rfl⟩
    have hout : ∀ (e : E) (z : D), ‖z.val‖ < 1 →
        RelCWComplex.map 1 e.val z.val ∉ (T : Set X) := by
      intro e z hz
      exact (T.disjoint_openCell_subcomplex_of_not_mem e.property).notMem_of_mem_left
        (hinterior e z hz)
    constructor
    · intro e z
      change q (RelCWComplex.map 1 e.val z.val) = q a.val ↔ ‖z.val‖ = 1
      constructor
      · intro heq
        have hmem : RelCWComplex.map 1 e.val z.val ∈ (T : Set X) := by
          rcases Quotient.exact heq with heq | ⟨hx, _⟩
          · exact heq.symm ▸ a.property
          · exact hx
        have hle : ‖z.val‖ ≤ 1 := by
          simpa only [D, Metric.mem_closedBall, dist_zero_right] using z.property
        exact le_antisymm hle (le_of_not_gt (fun hz => hout e z hz hmem))
      · intro hz
        apply hcollapse
        obtain ⟨u, v, huv⟩ := CWComplex.exists_cellFrontier_one_eq e.val
        have hfront : RelCWComplex.map 1 e.val z.val ∈ RelCWComplex.cellFrontier 1 e.val :=
          ⟨z.val, by simpa only [Metric.mem_sphere, dist_zero_right] using hz, rfl⟩
        rw [huv] at hfront
        rcases hfront with hu | hv
        · exact hzero u hu
        · exact hzero v hv
    · intro e f z w hz hw
      constructor
      · intro heq
        have heq' : RelCWComplex.map 1 e.val z.val = RelCWComplex.map 1 f.val w.val := by
          rcases Quotient.exact heq with heq | ⟨hx, _⟩
          · exact heq
          · exact False.elim (hout e z hz hx)
        have hedges : e = f := by
          apply Subtype.ext
          have hs := RelCWComplex.eq_of_not_disjoint_openCell
            (not_disjoint_iff.mpr ⟨RelCWComplex.map 1 e.val z.val,
              hinterior e z hz, heq'.symm ▸ hinterior f w hw⟩)
          exact Sigma.mk.inj_iff.mp hs |>.2 |> eq_of_heq
        subst f
        refine ⟨rfl, Subtype.ext ?_⟩
        apply (RelCWComplex.map 1 e.val).injOn _ _ heq'
        · simpa only [RelCWComplex.source_eq, Metric.mem_ball, dist_zero_right] using hz
        · simpa only [RelCWComplex.source_eq, Metric.mem_ball, dist_zero_right] using hw
      · rintro ⟨rfl, rfl⟩
        rfl
  have hB : ∀ p, p ∈ B ↔ π p = π (.inl Unit.unit) := by
    intro p
    rcases p with u | ⟨e, z⟩
    · simp [B, π]
    · exact (hfib.1 e z).symm
  have hsame : ∀ p p', π p = π p' ↔ (p = p' ∨ p ∈ B ∧ p' ∈ B) := by
    intro p p'
    constructor
    · intro heq
      by_cases hp : p ∈ B
      · exact Or.inr ⟨hp, (hB p').mpr (heq.symm.trans ((hB p).mp hp))⟩
      · left
        have hp' : p' ∉ B := by
          intro hp'
          exact hp ((hB p).mpr (heq.trans ((hB p').mp hp')))
        rcases p with u | ⟨e, z⟩
        · exact False.elim (hp (by trivial))
        rcases p' with u | ⟨f, w⟩
        · exact False.elim (hp' (by trivial))
        have hz : ‖z.val‖ < 1 := lt_of_le_of_ne
          (by simpa only [D, Metric.mem_closedBall, dist_zero_right] using z.property) hp
        have hw : ‖w.val‖ < 1 := lt_of_le_of_ne
          (by simpa only [D, Metric.mem_closedBall, dist_zero_right] using w.property) hp'
        obtain ⟨rfl, rfl⟩ := (hfib.2 e f z w hz hw).mp heq
        rfl
    · rintro (rfl | ⟨hp, hp'⟩)
      · rfl
      · exact ((hB p).mp hp).trans ((hB p').mp hp').symm
  let lift : GoodPair.Collapsed B → GoodPair.Collapsed (T : Set X) :=
    Quotient.lift π (fun _ _ h => (hsame _ _).mpr h)
  have hlift : IsQuotientMap lift :=
    IsQuotientMap.of_comp_of_isCoinducing (f := GoodPair.collapse B) (g := lift)
      hquot isQuotientMap_quotient_mk'.isCoinducing
  have hinj : Function.Injective lift := by
    intro x y
    induction x using Quotient.inductionOn with
    | h p =>
      induction y using Quotient.inductionOn with
      | h p' =>
        intro heq
        exact Quotient.sound ((hsame p p').mp heq)
  have hhomeo : IsHomeomorph lift :=
    isHomeomorph_iff_isQuotientMap_injective.mpr ⟨hlift, hinj⟩
  exact ⟨hquot, hfib.1, hfib.2, hhomeo.homeomorph, fun _ => rfl⟩

end HolomorphicAnosov
