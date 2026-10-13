import HolomorphicAnosov.Topology.CWRefinementFiniteFrontier
import Mathlib.Topology.MetricSpace.ProperSpace

/-!
# Finite open-cell refinements with the original topology

Source: Fritsch–Piccinini, Cellular Structures in Topology (1990), Theorem 2.3.1
and Example 3, printed pp.62–63, and Lemma 2.3.7, p.67. Finite carrier fibres
let the old weak-topology criterion verify the explicitly supplied new CW data.
The module also packages finite subdivisions and their composition.
-/

open Set _root_.Topology

namespace HolomorphicAnosov
universe u
noncomputable section

/-- A continuous characteristic disk has closed image equal to the closure of
its open image, whether or not the disk is embedded at its boundary. -/
theorem characteristic_closed_image {X : Type*} [TopologicalSpace X] [T2Space X]
    (n : ℕ) (f : (Fin n → ℝ) → X)
    (hf : ContinuousOn f (Metric.closedBall 0 1)) :
    closure (f '' Metric.ball 0 1) = f '' Metric.closedBall 0 1 := by
  apply subset_antisymm
  · exact ((isCompact_closedBall _ _).image_of_continuousOn hf).isClosed.closure_subset_iff.mpr
      (image_mono Metric.ball_subset_closedBall)
  · rw [← closure_ball 0 one_ne_zero]
    apply ContinuousOn.image_closure
    rwa [closure_ball 0 one_ne_zero]

/-- Finite carrier fibres turn an open-cell refinement cover into the closed
characteristic-disk covers used by the weak-topology axiom. -/
theorem finite_refinement_closed_cover
    {X : Type u} [TopologicalSpace X] [T2Space X]
    (old : CWComplex (Set.univ : Set X))
    (J : ℕ → Type u) (f : (n : ℕ) → J n → PartialEquiv (Fin n → ℝ) X)
    (hs : ∀ n j, (f n j).source = Metric.ball 0 1)
    (hc : ∀ n j, ContinuousOn (f n j) (Metric.closedBall 0 1))
    (carrier : (Σ n, J n) → (Σ n, @CWComplex.cell X _ Set.univ old n))
    (hcover : ∀ e : Σ n, @CWComplex.cell X _ Set.univ old n,
      (@CWComplex.map X _ Set.univ old e.1 e.2).target =
        ⋃ k : Σ n, J n, ⋃ (_ : carrier k = e), (f k.1 k.2).target)
    (hf : ∀ e, Set.Finite {k | carrier k = e})
    (e : Σ n, @CWComplex.cell X _ Set.univ old n) :
    (@CWComplex.map X _ Set.univ old e.1 e.2) '' Metric.closedBall 0 1 =
      ⋃ k : Σ n, J n, ⋃ (_ : carrier k = e),
        (f k.1 k.2) '' Metric.closedBall 0 1 := by
  let : CWComplex (Set.univ : Set X) := old
  have ho : (@CWComplex.map X _ Set.univ old e.1 e.2).target =
      CWComplex.openCell (C := (Set.univ : Set X)) e.1 e.2 := by
    rw [← PartialEquiv.image_source_eq_target, @CWComplex.source_eq X _ Set.univ old]
    rfl
  have hn (k : Σ n, J n) : closure ((f k.1 k.2).target) =
      (f k.1 k.2) '' Metric.closedBall 0 1 := by
    rw [← PartialEquiv.image_source_eq_target, hs]
    exact characteristic_closed_image _ _ (hc _ _)
  change CWComplex.closedCell (C := (Set.univ : Set X)) e.1 e.2 = _
  rw [← CWComplex.closure_openCell_eq_closedCell, ← ho, hcover e]
  simpa only [mem_ofPred_eq, hn] using
    (hf e).closure_biUnion (fun k ↦ (f k.1 k.2).target)

/-- Assemble native CW fields on the original topology from a finite refinement
of its open cells and the explicit new attaching maps. Source: Fritsch–Piccinini,
Theorem 2.3.1 pp.62–63 and Lemma 2.3.7 p.67, weak-topology verification.

Proof: each old open cell is the finite union of the new cells over it. Taking
closures commutes with this finite union. Every characteristic disk is compact,
so its image is closed and equals the closure of its open image. Thus the same
finite carrier fibre covers the old closed cell by new closed cells. If a set
intersects all new closed cells in closed sets, it consequently intersects every
old closed cell in a finite union of closed sets. The original CW criterion makes
it closed. The old open-cell cover and the carrier cover give coverage. All other
native CW fields are the supplied explicit characteristic data. -/
@[instance_reducible]
def cwComplexOfFiniteOpenRefinement
    {X : Type u} [TopologicalSpace X] [T2Space X]
    (old : CWComplex (Set.univ : Set X))
    (J : ℕ → Type u) (f : (n : ℕ) → J n → PartialEquiv (Fin n → ℝ) X)
    (hs : ∀ n j, (f n j).source = Metric.ball 0 1)
    (hc : ∀ n j, ContinuousOn (f n j) (Metric.closedBall 0 1))
    (hi : ∀ n j, ContinuousOn (f n j).symm (f n j).target)
    (hd : (Set.univ : Set (Σ n, J n)).PairwiseDisjoint
      (fun k ↦ (f k.1 k.2) '' Metric.ball 0 1))
    (hb : ∀ n j, ∃ I : (m : ℕ) → Finset (J m),
      MapsTo (f n j) (Metric.sphere 0 1)
        (⋃ (m < n) (k ∈ I m), (f m k) '' Metric.closedBall 0 1))
    (carrier : (Σ n, J n) → (Σ n, @CWComplex.cell X _ Set.univ old n))
    (hcover : ∀ e : Σ n, @CWComplex.cell X _ Set.univ old n,
      (@CWComplex.map X _ Set.univ old e.1 e.2).target =
        ⋃ k : Σ n, J n, ⋃ (_ : carrier k = e), (f k.1 k.2).target)
    (hf : ∀ e, Set.Finite {k | carrier k = e}) : CWComplex (Set.univ : Set X) := by
  classical
  letI : CWComplex (Set.univ : Set X) := old
  refine { cell := J
           map := f
           source_eq := hs
           continuousOn := hc
           continuousOn_symm := hi
           pairwiseDisjoint' := hd
           mapsTo' := hb
           closed' := ?_
           union' := ?_ }
  · intro B hB hclosed
    apply (CWComplex.closed Set.univ B hB).mpr
    intro n j
    change IsClosed (B ∩ (@CWComplex.map X _ Set.univ old n j) '' Metric.closedBall 0 1)
    rw [finite_refinement_closed_cover old J f hs hc carrier hcover hf ⟨n, j⟩]
    simp_rw [inter_iUnion]
    exact (hf ⟨n, j⟩).isClosed_biUnion (fun k _ ↦ hclosed k.1 k.2)
  · apply subset_antisymm (subset_univ _)
    intro x _
    have hx : x ∈ ⋃ (n : ℕ) (j : RelCWComplex.cell (Set.univ : Set X) n),
        CWComplex.openCell (C := (Set.univ : Set X)) n j := by
      rw [CWComplex.iUnion_openCell_eq_complex]
      trivial
    obtain ⟨n, j, hx⟩ := mem_iUnion.mp hx |>.imp fun _ h ↦ mem_iUnion.mp h
    have ho : CWComplex.openCell (C := (Set.univ : Set X)) n j = (@CWComplex.map X _ Set.univ old n j).target := by
      rw [← PartialEquiv.image_source_eq_target, @CWComplex.source_eq X _ Set.univ old]
      rfl
    rw [ho, hcover ⟨n, j⟩] at hx
    obtain ⟨k, hk, hx⟩ := mem_iUnion.mp hx |>.imp fun _ h ↦ mem_iUnion.mp h
    have hz := (f k.1 k.2).map_target hx
    rw [hs] at hz
    exact mem_iUnion.mpr ⟨k.1, mem_iUnion.mpr ⟨k.2,
      ⟨(f k.1 k.2).symm x, Metric.ball_subset_closedBall hz, (f k.1 k.2).right_inv hx⟩⟩⟩


/-- Finite subdivision with the literal characteristic maps retained off a finite set. -/
structure CWFiniteRefinement {X : Type u} [TopologicalSpace X]
    (old new : CWComplex (Set.univ : Set X)) where
  changed : Set (Σ n, @CWComplex.cell X _ Set.univ old n)
  carrier : (Σ n, @CWComplex.cell X _ Set.univ new n) →
    (Σ n, @CWComplex.cell X _ Set.univ old n)
  finite_changed : changed.Finite
  dimension : ∀ e, e.1 ≤ (carrier e).1
  subset : ∀ e, (@CWComplex.map X _ Set.univ new e.1 e.2).target ⊆
    (@CWComplex.map X _ Set.univ old (carrier e).1 (carrier e).2).target
  cover : ∀ e : Σ n, @CWComplex.cell X _ Set.univ old n,
    (@CWComplex.map X _ Set.univ old e.1 e.2).target =
      ⋃ f, ⋃ (_ : carrier f = e), (@CWComplex.map X _ Set.univ new f.1 f.2).target
  finite_fiber : ∀ e, Set.Finite {f | carrier f = e}
  unchanged : ∀ n (i : @CWComplex.cell X _ Set.univ old n),
    (⟨n, i⟩ : Σ n, @CWComplex.cell X _ Set.univ old n) ∉ changed →
    ∃ j : @CWComplex.cell X _ Set.univ new n, carrier ⟨n, j⟩ = ⟨n, i⟩ ∧
      Set.EqOn (@CWComplex.map X _ Set.univ new n j) (@CWComplex.map X _ Set.univ old n i)
        (Metric.closedBall 0 1)

def CWFiniteRefinement.refl {X : Type u} [TopologicalSpace X]
    (old : CWComplex (Set.univ : Set X)) : CWFiniteRefinement old old where
  changed := ∅
  carrier := id
  finite_changed := finite_empty
  dimension := fun _ ↦ le_rfl
  subset := fun _ ↦ Subset.rfl
  cover := by
    intro e
    ext x
    simp only [mem_iUnion, id_eq]
    exact ⟨fun h ↦ ⟨e, rfl, h⟩, fun ⟨f, h, hx⟩ ↦ h ▸ hx⟩
  finite_fiber := fun e ↦ by
    simpa only [id_eq, Set.ofPred_eq_eq_singleton] using Set.finite_singleton e
  unchanged := fun n i _ ↦ ⟨i, rfl, Set.eqOn_refl _ _⟩

/-- Compose finite cell subdivisions. Both finite change support and literal
characteristic-map preservation are stable under composition. -/
def CWFiniteRefinement.trans {X : Type u} [TopologicalSpace X]
    {old middle new : CWComplex (Set.univ : Set X)}
    (R : CWFiniteRefinement old middle) (S : CWFiniteRefinement middle new) :
    CWFiniteRefinement old new where
  changed := R.changed ∪ R.carrier '' S.changed
  carrier := R.carrier ∘ S.carrier
  finite_changed := R.finite_changed.union (S.finite_changed.image R.carrier)
  dimension := fun e ↦ (S.dimension e).trans (R.dimension (S.carrier e))
  subset := fun e ↦ (S.subset e).trans (R.subset (S.carrier e))
  cover := by
    intro e
    ext x
    rw [R.cover e]
    simp only [mem_iUnion, Function.comp_apply]
    constructor
    · rintro ⟨g, hg, hx⟩
      rw [S.cover g] at hx
      obtain ⟨f, hf, hx⟩ := mem_iUnion.mp hx |>.imp fun _ h ↦ mem_iUnion.mp h
      exact ⟨f, by rw [hf, hg], hx⟩
    · rintro ⟨f, hf, hx⟩
      refine ⟨S.carrier f, hf, ?_⟩
      rw [S.cover]
      exact mem_iUnion.mpr ⟨f, mem_iUnion.mpr ⟨rfl, hx⟩⟩
  finite_fiber := by
    intro e
    apply ((R.finite_fiber e).biUnion (fun g _ ↦ S.finite_fiber g)).subset
    intro f hf
    exact mem_iUnion.mpr ⟨S.carrier f, mem_iUnion.mpr ⟨hf, rfl⟩⟩
  unchanged := by
    intro n i hi
    have hiR : (⟨n, i⟩ : Σ n, @CWComplex.cell X _ Set.univ old n) ∉ R.changed :=
      fun h ↦ hi (Or.inl h)
    obtain ⟨j, hj, hmapj⟩ := R.unchanged n i hiR
    have hjS : (⟨n, j⟩ : Σ n, @CWComplex.cell X _ Set.univ middle n) ∉ S.changed := by
      intro h
      exact hi (Or.inr ⟨⟨n, j⟩, h, hj⟩)
    obtain ⟨k, hk, hmapk⟩ := S.unchanged n j hjS
    exact ⟨k, by simp only [Function.comp_apply, hk, hj], hmapk.trans hmapj⟩


/-- The raw label family after replacing one original open cell. -/
def cellReplacementLabels {X : Type u} [TopologicalSpace X]
    (old : CWComplex (Set.univ : Set X))
    (e : Σ n, @CWComplex.cell X _ Set.univ old n) (P : ℕ → Type u) (d : ℕ) : Type u :=
  {j : @CWComplex.cell X _ Set.univ old d | (⟨d, j⟩ : Σ n, @CWComplex.cell X _ Set.univ old n) ≠ e}
    ⊕ P d

def cellReplacementMap {X : Type u} [TopologicalSpace X]
    (old : CWComplex (Set.univ : Set X))
    (e : Σ n, @CWComplex.cell X _ Set.univ old n) (P : ℕ → Type u)
    (g : (d : ℕ) → P d → PartialEquiv (Fin d → ℝ) X)
    (d : ℕ) : cellReplacementLabels old e P d → PartialEquiv (Fin d → ℝ) X
  | .inl j => @CWComplex.map X _ Set.univ old d j.val
  | .inr j => g d j

def cellReplacementCarrier {X : Type u} [TopologicalSpace X]
    (old : CWComplex (Set.univ : Set X))
    (e : Σ n, @CWComplex.cell X _ Set.univ old n) (P : ℕ → Type u) :
    (Σ d, cellReplacementLabels old e P d) → (Σ n, @CWComplex.cell X _ Set.univ old n)
  | ⟨d, .inl j⟩ => ⟨d, j.val⟩
  | ⟨_, .inr _⟩ => e

theorem cellReplacementCover {X : Type u} [TopologicalSpace X]
    (old : CWComplex (Set.univ : Set X))
    (e : Σ n, @CWComplex.cell X _ Set.univ old n) (P : ℕ → Type u)
    (g : (d : ℕ) → P d → PartialEquiv (Fin d → ℝ) X)
    (hcover : (@CWComplex.map X _ Set.univ old e.1 e.2).target =
      ⋃ d, ⋃ p : P d, (g d p).target) :
    ∀ a : Σ n, @CWComplex.cell X _ Set.univ old n,
      (@CWComplex.map X _ Set.univ old a.1 a.2).target =
        ⋃ b, ⋃ (_ : cellReplacementCarrier old e P b = a),
          (cellReplacementMap old e P g b.1 b.2).target := by
  intro a
  ext x
  constructor
  · intro hx
    by_cases h : a = e
    · subst a
      rw [hcover] at hx
      obtain ⟨d, p, hx⟩ := mem_iUnion.mp hx |>.imp fun _ h ↦ mem_iUnion.mp h
      exact mem_iUnion.mpr ⟨⟨d, Sum.inr p⟩, mem_iUnion.mpr ⟨rfl, hx⟩⟩
    · exact mem_iUnion.mpr ⟨⟨a.1, Sum.inl ⟨a.2, h⟩⟩, mem_iUnion.mpr ⟨rfl, hx⟩⟩
  · intro hx
    obtain ⟨⟨d, b⟩, hba, hxb⟩ := mem_iUnion.mp hx |>.imp fun _ h ↦ mem_iUnion.mp h
    cases b with
    | inl b =>
      change (⟨d, b.val⟩ : Σ n, @CWComplex.cell X _ Set.univ old n) = a at hba
      cases hba
      exact hxb
    | inr p =>
      change e = a at hba
      cases hba
      rw [hcover]
      exact mem_iUnion.mpr ⟨d, mem_iUnion.mpr ⟨p, hxb⟩⟩

theorem cellReplacementFiniteFibers {X : Type u} [TopologicalSpace X]
    (old : CWComplex (Set.univ : Set X))
    (e : Σ n, @CWComplex.cell X _ Set.univ old n) (P : ℕ → Type u)
    [Finite (Σ n, P n)] :
    ∀ a, Set.Finite {b | cellReplacementCarrier old e P b = a} := by
  classical
  intro a
  let fresh : (Σ n, P n) → (Σ n, cellReplacementLabels old e P n) :=
    fun b ↦ ⟨b.1, Sum.inr b.2⟩
  let keep : Set (Σ n, cellReplacementLabels old e P n) :=
    {b | ∃ h : a ≠ e, b = ⟨a.1, Sum.inl ⟨a.2, h⟩⟩}
  have hkeep : keep.Subsingleton := by
    rintro b ⟨h, rfl⟩ c ⟨h', rfl⟩
    rfl
  apply (hkeep.finite.union (Set.finite_range fresh)).subset
  rintro ⟨d, b⟩ hb
  cases b with
  | inl b =>
    left
    change (⟨d, b.val⟩ : Σ n, @CWComplex.cell X _ Set.univ old n) = a at hb
    subst a
    exact ⟨b.property, rfl⟩
  | inr p =>
    exact Or.inr ⟨⟨d, p⟩, rfl⟩

theorem cellReplacementDimension {X : Type u} [TopologicalSpace X]
    (old : CWComplex (Set.univ : Set X))
    (e : Σ n, @CWComplex.cell X _ Set.univ old n) (P : ℕ → Type u)
    (hp : ∀ d, P d → d ≤ e.1) :
    ∀ b : Σ n, cellReplacementLabels old e P n,
      b.1 ≤ (cellReplacementCarrier old e P b).1 := by
  rintro ⟨d, b⟩
  cases b with
  | inl b => exact le_rfl
  | inr b => exact hp d b


theorem cellReplacementDisjoint {X : Type u} [TopologicalSpace X]
    (old : CWComplex (Set.univ : Set X))
    (e : Σ n, @CWComplex.cell X _ Set.univ old n) (P : ℕ → Type u)
    (g : (d : ℕ) → P d → PartialEquiv (Fin d → ℝ) X)
    (hs : ∀ d p, (g d p).source = Metric.ball 0 1)
    (hsub : ∀ d p, (g d p).target ⊆ (@CWComplex.map X _ Set.univ old e.1 e.2).target)
    (hd : (Set.univ : Set (Σ d, P d)).PairwiseDisjoint (fun p ↦ (g p.1 p.2).target)) :
    (Set.univ : Set (Σ d, cellReplacementLabels old e P d)).PairwiseDisjoint
      (fun p ↦ cellReplacementMap old e P g p.1 p.2 '' Metric.ball 0 1) := by
  let : CWComplex (Set.univ : Set X) := old
  have ho (a : Σ n, @CWComplex.cell X _ Set.univ old n) :
      (@CWComplex.map X _ Set.univ old a.1 a.2).target =
        CWComplex.openCell (C := (Set.univ : Set X)) a.1 a.2 := by
    rw [← PartialEquiv.image_source_eq_target, @CWComplex.source_eq X _ Set.univ old]
    rfl
  have hg (d : ℕ) (p : P d) : g d p '' Metric.ball 0 1 = (g d p).target := by
    rw [← hs, PartialEquiv.image_source_eq_target]
  rintro ⟨m, a⟩ _ ⟨n, b⟩ _ hne
  cases a with
  | inl a =>
    cases b with
    | inl b =>
      change Disjoint (CWComplex.openCell (C := (Set.univ : Set X)) m a.val)
        (CWComplex.openCell (C := (Set.univ : Set X)) n b.val)
      apply CWComplex.disjoint_openCell_of_ne
      intro heq
      apply hne
      obtain ⟨av, ha⟩ := a
      obtain ⟨bv, hb⟩ := b
      cases heq
      rfl
    | inr b =>
      change Disjoint (CWComplex.openCell (C := (Set.univ : Set X)) m a.val)
        (g n b '' Metric.ball 0 1)
      rw [hg]
      exact (CWComplex.disjoint_openCell_of_ne (C := (Set.univ : Set X)) (i := a.val) (j := e.2) a.property).mono_right (by simpa [ho] using hsub n b)
  | inr a =>
    cases b with
    | inl b =>
      change Disjoint (g m a '' Metric.ball 0 1)
        (CWComplex.openCell (C := (Set.univ : Set X)) n b.val)
      rw [hg]
      exact ((CWComplex.disjoint_openCell_of_ne (C := (Set.univ : Set X)) (i := b.val) (j := e.2) b.property).mono_right
        (by simpa [ho] using hsub m a)).symm
    | inr b =>
      change Disjoint (g m a '' Metric.ball 0 1) (g n b '' Metric.ball 0 1)
      rw [hg, hg]
      apply hd (x := ⟨m, a⟩) (y := ⟨n, b⟩) (mem_univ _) (mem_univ _)
      intro heq
      apply hne
      cases heq
      rfl

theorem cellReplacementSource {X : Type u} [TopologicalSpace X]
    (old : CWComplex (Set.univ : Set X))
    (e : Σ n, @CWComplex.cell X _ Set.univ old n) (P : ℕ → Type u)
    (g : (d : ℕ) → P d → PartialEquiv (Fin d → ℝ) X)
    (hs : ∀ d p, (g d p).source = Metric.ball 0 1) :
    ∀ d p, (cellReplacementMap old e P g d p).source = Metric.ball 0 1 := by
  intro d p
  cases p with
  | inl j => exact @CWComplex.source_eq X _ Set.univ old d j.val
  | inr j => exact hs d j

theorem cellReplacementOldFrontier {X : Type u} [TopologicalSpace X]
    (old : CWComplex (Set.univ : Set X))
    (e : Σ n, @CWComplex.cell X _ Set.univ old n) (P : ℕ → Type u)
    [Finite (Σ n, P n)]
    (g : (d : ℕ) → P d → PartialEquiv (Fin d → ℝ) X)
    (hs : ∀ d p, (g d p).source = Metric.ball 0 1)
    (hcover : (@CWComplex.map X _ Set.univ old e.1 e.2).target =
      ⋃ d, ⋃ p : P d, (g d p).target)
    (hp : ∀ d, P d → d ≤ e.1)
    (d : ℕ) (j : @CWComplex.cell X _ Set.univ old d) :
    ∃ I : (m : ℕ) → Finset (cellReplacementLabels old e P m),
      MapsTo (@CWComplex.map X _ Set.univ old d j) (Metric.sphere 0 1)
        (⋃ (m < d) (p ∈ I m), cellReplacementMap old e P g m p '' Metric.closedBall 0 1) := by
  let : CWComplex (Set.univ : Set X) := old
  have hh : ∀ a : Σ n, RelCWComplex.cell (Set.univ : Set X) n,
      CWComplex.openCell a.1 a.2 =
        ⋃ b, ⋃ (_ : cellReplacementCarrier old e P b = a),
          (cellReplacementMap old e P g b.1 b.2).target := by
    intro a
    have h := cellReplacementCover old e P g hcover a
    rw [← PartialEquiv.image_source_eq_target, @CWComplex.source_eq X _ Set.univ old] at h
    exact h
  obtain ⟨I, hI⟩ := cw_refinement_finite_frontier
    (cellReplacementLabels old e P) (fun m p ↦ (cellReplacementMap old e P g m p).target)
    (cellReplacementCarrier old e P) (cellReplacementDimension old e P hp) hh
    (cellReplacementFiniteFibers old e P) d j
  refine ⟨I, ?_⟩
  intro v hv
  have hh := hI ⟨v, hv, rfl⟩
  simp only [mem_iUnion] at hh ⊢
  obtain ⟨m, hm, p, hp, hx⟩ := hh
  refine ⟨m, hm, p, hp, ?_⟩
  let f := cellReplacementMap old e P g m p
  have hsource := cellReplacementSource old e P g hs m p
  have hz := f.map_target hx
  rw [hsource] at hz
  exact ⟨f.symm ((@CWComplex.map X _ Set.univ old d j) v),
    Metric.ball_subset_closedBall hz, f.right_inv hx⟩

/-- A finite family of replacement disks, with their boundary certificates,
produces a subdivision of one original cell and preserves every other map. -/
theorem cw_single_cell_replacement
    {X : Type u} [TopologicalSpace X] [T2Space X]
    (old : CWComplex (Set.univ : Set X))
    (e : Σ n, @CWComplex.cell X _ Set.univ old n) (P : ℕ → Type u)
    [Finite (Σ n, P n)]
    (g : (d : ℕ) → P d → PartialEquiv (Fin d → ℝ) X)
    (hs : ∀ d p, (g d p).source = Metric.ball 0 1)
    (hc : ∀ d p, ContinuousOn (g d p) (Metric.closedBall 0 1))
    (hi : ∀ d p, ContinuousOn (g d p).symm (g d p).target)
    (hsub : ∀ d p, (g d p).target ⊆ (@CWComplex.map X _ Set.univ old e.1 e.2).target)
    (hd : (Set.univ : Set (Σ d, P d)).PairwiseDisjoint (fun p ↦ (g p.1 p.2).target))
    (hcover : (@CWComplex.map X _ Set.univ old e.1 e.2).target =
      ⋃ d, ⋃ p : P d, (g d p).target)
    (hp : ∀ d, P d → d ≤ e.1)
    (hb : ∀ d (j : P d), ∃ I : (m : ℕ) → Finset (cellReplacementLabels old e P m),
      MapsTo (g d j) (Metric.sphere 0 1)
        (⋃ (m < d) (p ∈ I m), cellReplacementMap old e P g m p '' Metric.closedBall 0 1)) :
    ∃ new : CWComplex (Set.univ : Set X), ∃ R : CWFiniteRefinement old new,
      R.changed = {e} ∧
      ∀ d p, ∃ j : @CWComplex.cell X _ Set.univ new d,
        (@CWComplex.map X _ Set.univ new d j) = g d p := by
  classical
  let J := cellReplacementLabels old e P
  let f := cellReplacementMap old e P g
  have hcont : ∀ d p, ContinuousOn (f d p) (Metric.closedBall 0 1) := by
    intro d p
    cases p with
    | inl j => exact @CWComplex.continuousOn X _ Set.univ old d j.val
    | inr j => exact hc d j
  have hinv : ∀ d p, ContinuousOn (f d p).symm (f d p).target := by
    intro d p
    cases p with
    | inl j => exact @CWComplex.continuousOn_symm X _ Set.univ old d j.val
    | inr j => exact hi d j
  have hfront : ∀ d p, ∃ I : (m : ℕ) → Finset (J m),
      MapsTo (f d p) (Metric.sphere 0 1)
        (⋃ (m < d) (q ∈ I m), f m q '' Metric.closedBall 0 1) := by
    intro d p
    cases p with
    | inl j => exact cellReplacementOldFrontier old e P g hs hcover hp d j.val
    | inr j => exact hb d j
  let new := cwComplexOfFiniteOpenRefinement old J f (cellReplacementSource old e P g hs)
    hcont hinv (cellReplacementDisjoint old e P g hs hsub hd) hfront
    (cellReplacementCarrier old e P) (cellReplacementCover old e P g hcover)
    (cellReplacementFiniteFibers old e P)
  let R : CWFiniteRefinement old new := {
    changed := {e}
    carrier := cellReplacementCarrier old e P
    finite_changed := finite_singleton e
    dimension := cellReplacementDimension old e P hp
    subset := by
      rintro ⟨d, p⟩
      cases p with
      | inl j => exact Subset.rfl
      | inr j => exact hsub d j
    cover := cellReplacementCover old e P g hcover
    finite_fiber := cellReplacementFiniteFibers old e P
    unchanged := by
      intro d j hj
      exact ⟨Sum.inl ⟨j, hj⟩, rfl, Set.eqOn_refl _ _⟩ }
  refine ⟨new, R, rfl, ?_⟩
  intro d p
  exact ⟨Sum.inr p, rfl⟩



end
end HolomorphicAnosov

