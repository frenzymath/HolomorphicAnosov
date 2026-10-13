import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Topology.MetricSpace.Thickening

/-! # Finite injectivity covers and compact receiving buffers

Source: Ghys Proposition 4.1, §4 pp.594–597, compact local-cover assembly;
the compact finite-subcover theorem, measurable disjoint ownership, and
positive distance on compact disjoint fibers. Compact source cores correct
the false inference that locally injective maps on arbitrary open domains
have finite fibers. No regularity stronger than each theorem states is used.
-/


open Set
namespace HolomorphicAnosov

/-- A compact core on which a function is locally injective has a finite open
injectivity cover, contained in the prescribed open domain.

Agent-written compact-core correction to the roots step of the Markov-free
Ghys Proposition 4.1 argument. An open domain alone does not give such a finite
cover: exp(1/z)=1 has infinitely many roots accumulating at the excluded point
zero. Select an injectivity neighborhood at each core point, take a finite
subcover by compactness, and enumerate its indices. No continuity of the
function is needed for this purely local-injectivity conclusion. -/
theorem compact_local_injective_cover
    {X Y : Type*} [TopologicalSpace X] (K U : Set X) (f : X → Y)
    (hK : IsCompact K)
    (hlocal : ∀ x ∈ K, ∃ V, IsOpen V ∧ x ∈ V ∧ V ⊆ U ∧ V.InjOn f) :
    ∃ n : ℕ, ∃ V : Fin n → Set X,
      (∀ i, IsOpen (V i) ∧ V i ⊆ U ∧ (V i).InjOn f) ∧ K ⊆ ⋃ i, V i := by
  classical
  choose V hVo hxV hVU hinj using fun x : K ↦ hlocal x x.property
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover V hVo (fun x hx ↦ mem_iUnion.mpr ⟨⟨x, hx⟩, hxV _⟩)
  let e := Fintype.equivFin t
  refine ⟨Fintype.card t, fun i ↦ V (e.symm i).val, ?_, ?_⟩
  · intro i
    exact ⟨hVo _, hVU _, hinj _⟩
  · intro x hx
    obtain ⟨j, hj, hxj⟩ := mem_iUnion₂.mp (ht hx)
    exact mem_iUnion.mpr ⟨e ⟨j, hj⟩, by simpa using hxj⟩

/-- Every fibre of a map locally injective near a compact core is finite on
that core. Each member of its finite injectivity cover contains at most one
point of the fibre. Take the finite union of these singleton-or-empty pieces.
This is the corrected root-finiteness step of the preceding theorem. -/
theorem compact_local_injective_fiber_finite
    {X Y : Type*} [TopologicalSpace X] (K U : Set X) (f : X → Y)
    (hK : IsCompact K)
    (hlocal : ∀ x ∈ K, ∃ V, IsOpen V ∧ x ∈ V ∧ V ⊆ U ∧ V.InjOn f)
    (y : Y) : (K ∩ f ⁻¹' {y}).Finite := by
  obtain ⟨n, V, hV, hcover⟩ := compact_local_injective_cover K U f hK hlocal
  have hpiece (i : Fin n) : (V i ∩ f ⁻¹' {y}).Subsingleton := by
    intro x hx z hz
    exact (hV i).2.2 hx.1 hz.1 (hx.2.trans hz.2.symm)
  apply (Set.finite_iUnion (fun i ↦ (hpiece i).finite)).subset
  intro x hx
  obtain ⟨i, hi⟩ := mem_iUnion.mp (hcover hx.1)
  exact mem_iUnion.mpr ⟨i, hi, hx.2⟩

/-- A finite measurable cover admits a disjoint measurable ownership partition
of a measurable core. The i-th piece consists of core points in V_i that lie
in none of the earlier V_j. Each piece remains in its original injectivity
neighborhood, and its union is exactly the core.

This is the branch-ownership correction for the inverse-Jacobian budget in
Ghys Proposition 4.1. It does not assert a finite branch cover of an arbitrary
open domain. -/
theorem finite_measurable_cover_ownership
    {X : Type*} [MeasurableSpace X] (K : Set X) (hK : MeasurableSet K)
    {n : ℕ} (V : Fin n → Set X) (hV : ∀ i, MeasurableSet (V i))
    (hcover : K ⊆ ⋃ i, V i) :
    ∃ P : Fin n → Set X,
      (∀ i, MeasurableSet (P i) ∧ P i ⊆ K ∩ V i) ∧
      Pairwise (fun i j ↦ Disjoint (P i) (P j)) ∧ ⋃ i, P i = K := by
  let P := fun i ↦ K ∩ disjointed V i
  refine ⟨P, ?_, ?_, ?_⟩
  · intro i
    refine ⟨hK.inter ?_, fun x hx ↦ ⟨hx.1, disjointed_subset V i hx.2⟩⟩
    rw [disjointed_eq_inter_compl]
    exact (hV i).inter (MeasurableSet.iInter (fun j ↦ MeasurableSet.iInter (fun _ ↦ (hV j).compl)))
  · intro i j hij
    exact (disjoint_disjointed V hij).mono inter_subset_right inter_subset_right
  · simp only [P, ← inter_iUnion, iUnion_disjointed]
    exact inter_eq_left.mpr hcover

/-- Two continuously varying compact sets that are disjoint in every fibre
over a compact parameter core have one positive uniform separation.

Apply the extreme value theorem to the distance on the compact product of the
parameter core and the two source cores. Its minimum is positive since equality
of the two image points is excluded. Half that minimum gives a strict uniform
margin. An empty product makes the conclusion vacuous. This is the exact
uniformity needed between each pair of parallel stable paths. -/
theorem compact_fiberwise_uniform_separation
    {T X Y Z : Type*} [TopologicalSpace T] [TopologicalSpace X]
    [TopologicalSpace Y] [MetricSpace Z]
    (K : Set T) (A : Set X) (B : Set Y)
    (hK : IsCompact K) (hA : IsCompact A) (hB : IsCompact B)
    (F : T × X → Z) (G : T × Y → Z)
    (hF : ContinuousOn F (K ×ˢ A)) (hG : ContinuousOn G (K ×ˢ B))
    (hne : ∀ t ∈ K, ∀ x ∈ A, ∀ y ∈ B, F (t,x) ≠ G (t,y)) :
    ∃ r : ℝ, 0 < r ∧ ∀ t ∈ K, ∀ x ∈ A, ∀ y ∈ B,
      r < dist (F (t,x)) (G (t,y)) := by
  let S := K ×ˢ (A ×ˢ B)
  let D : T × (X × Y) → ℝ := fun p ↦ dist (F (p.1,p.2.1)) (G (p.1,p.2.2))
  have hS : IsCompact S := hK.prod (hA.prod hB)
  have hD : ContinuousOn D S := by
    change ContinuousOn ((fun p : Z × Z ↦ dist p.1 p.2) ∘
      (fun p : T × (X × Y) ↦ (F (p.1,p.2.1), G (p.1,p.2.2)))) S
    apply continuous_dist.comp_continuousOn
    apply ContinuousOn.prodMk
    · exact hF.comp (continuous_fst.prodMk (continuous_fst.comp continuous_snd)).continuousOn
        (fun p hp ↦ ⟨hp.1, hp.2.1⟩)
    · exact hG.comp (continuous_fst.prodMk (continuous_snd.comp continuous_snd)).continuousOn
        (fun p hp ↦ ⟨hp.1, hp.2.2⟩)
  rcases S.eq_empty_or_nonempty with he | hn
  · refine ⟨1, zero_lt_one, ?_⟩
    intro t ht x hx y hy
    have : (t,(x,y)) ∈ S := ⟨ht,hx,hy⟩
    simp [he] at this
  obtain ⟨p, hp, hmin⟩ := hS.exists_isMinOn hn hD
  have hpos : 0 < D p := dist_pos.mpr (hne p.1 hp.1 p.2.1 hp.2.1 p.2.2 hp.2.2)
  refine ⟨D p / 2, half_pos hpos, ?_⟩
  intro t ht x hx y hy
  exact (half_lt_self hpos).trans_le (hmin (show (t,(x,y)) ∈ S from ⟨ht,hx,hy⟩))

/-- Compact source plaques whose images are uniformly small cover each target
fiber using finitely many compact root pieces. There are TWO buffers: a point
of K0 brings its plaque anchor into K1, and an anchor in K1 keeps its entire
plaque image in the outer box Omega. Restrict the root source to the compact
preimage of K1 before applying local injectivity. A receiving-box projection
constant on each transported plaque then assigns exactly the correct root.

The statement retains the source cover, contraction bound, and plaque-label
law explicitly. In the Anosov application they come respectively from the
finite source cores, the stable derivative estimate, and
`stable_connected_range_in_box`. It does not infer finite fibers from isolated
roots in an open set. Empty target fibers and empty source cores are allowed. -/
theorem compact_contracted_plaque_root_cover
    {ι M Z : Type*} {X Y : ι → Type*} [Fintype ι]
    [∀ a, TopologicalSpace (X a)] [∀ a, TopologicalSpace (Y a)]
    [∀ a, CompactSpace (Y a)] [MetricSpace M]
    [TopologicalSpace Z] [T2Space Z]
    (U : ∀ a, Set (X a)) (hU : ∀ a, IsCompact (U a))
    (Φ : ∀ a, X a × Y a → M) (hΦ : ∀ a, Continuous (Φ a)) (y₀ : ∀ a, Y a)
    (hcover : ∀ z : M, ∃ a u, u ∈ U a ∧ ∃ v, Φ a (u,v) = z)
    (f : M ≃ₜ M) (proj : M → Z) (Ω K₀ K₁ : Set M)
    (hK₀ : IsCompact K₀) (hK₁ : IsCompact K₁) (hKΩ : K₀ ⊆ Ω)
    (hπ : ContinuousOn proj Ω) (ε : ℝ)
    (hbuffer₀ : ∀ z ∈ K₀, ∀ w, dist w z < ε → w ∈ K₁)
    (hbuffer₁ : ∀ z ∈ K₁, ∀ w, dist w z < ε → w ∈ Ω)
    (hsmall : ∀ a u, u ∈ U a → ∀ v,
      dist (f (Φ a (u,v))) (f (Φ a (u,y₀ a))) < ε)
    (hlabel : ∀ a u, u ∈ U a →
      (∀ v, f (Φ a (u,v)) ∈ Ω) →
      ∀ v, proj (f (Φ a (u,v))) = proj (f (Φ a (u,y₀ a))))
    (hlocal : ∀ a u, u ∈ U a → f (Φ a (u,y₀ a)) ∈ K₁ →
      ∃ V, IsOpen V ∧ u ∈ V ∧ V.InjOn (fun w ↦ proj (f (Φ a (w,y₀ a))))) :
    ∀ x : Z,
      (∀ a, {u | u ∈ U a ∧ f (Φ a (u,y₀ a)) ∈ K₁ ∧
        proj (f (Φ a (u,y₀ a))) = x}.Finite) ∧
      (∀ a u, u ∈ U a → f (Φ a (u,y₀ a)) ∈ K₁ →
        (∀ v, f (Φ a (u,v)) ∈ Ω) ∧
        IsCompact ({z ∈ K₀ | proj z = x} ∩ range (fun v ↦ f (Φ a (u,v))))) ∧
      (∀ z ∈ K₀, proj z = x → ∃ a u,
        (u ∈ U a ∧ f (Φ a (u,y₀ a)) ∈ K₁ ∧ proj (f (Φ a (u,y₀ a))) = x) ∧
        z ∈ range (fun v ↦ f (Φ a (u,v)))) := by
  intro x
  have hroot (a : ι) : IsCompact {u | u ∈ U a ∧ f (Φ a (u,y₀ a)) ∈ K₁} :=
    (hU a).inter_right (hK₁.isClosed.preimage
      (f.continuous.comp ((hΦ a).comp (continuous_id.prodMk continuous_const))))
  have hfinite (a : ι) := compact_local_injective_fiber_finite
    {u | u ∈ U a ∧ f (Φ a (u,y₀ a)) ∈ K₁} univ
    (fun u ↦ proj (f (Φ a (u,y₀ a)))) (hroot a) (by
      intro u hu
      obtain ⟨V, hVo, huV, hVi⟩ := hlocal a u hu.1 hu.2
      exact ⟨V, hVo, huV, subset_univ _, hVi⟩) x
  have hfiber : IsCompact {z ∈ K₀ | proj z = x} :=
    hK₀.of_isClosed_subset (hK₀.isClosed.isClosed_eq (hπ.mono hKΩ) continuousOn_const)
      (fun _ hz ↦ hz.1)
  have hin (a : ι) (u : X a) (hu : u ∈ U a) (hk : f (Φ a (u,y₀ a)) ∈ K₁) :
      ∀ v, f (Φ a (u,v)) ∈ Ω :=
    fun v ↦ hbuffer₁ _ hk _ (hsmall a u hu v)
  refine ⟨?_, ?_, ?_⟩
  · intro a
    convert hfinite a using 1
    ext u
    simp only [mem_inter_iff, mem_ofPred_eq, mem_preimage, mem_singleton_iff, and_assoc]
  · intro a u hu hk
    refine ⟨hin a u hu hk, hfiber.inter_right ?_⟩
    exact (isCompact_range (f.continuous.comp
      ((hΦ a).comp (continuous_const.prodMk continuous_id)))).isClosed
  · intro z hz hx
    obtain ⟨a,u,hu,v,hv⟩ := hcover (f.symm z)
    have hfv : f (Φ a (u,v)) = z := by rw [hv, f.apply_symm_apply]
    have hk : f (Φ a (u,y₀ a)) ∈ K₁ := hbuffer₀ z hz _ (by
      rw [← hfv, dist_comm]
      exact hsmall a u hu v)
    refine ⟨a,u,⟨hu,hk,?_⟩,v,hfv⟩
    rw [← hlabel a u hu (hin a u hu hk) v, hfv, hx]

/-- Three nested receiving regions give one positive radius for both required
buffer implications. Compactness supplies a positive thickening inside each
open neighborhood; the minimum of the two radii works simultaneously. -/
theorem compact_nested_receiving_buffers
    {M : Type*} [MetricSpace M] (K₀ K₁ Ω : Set M)
    (hK₀ : IsCompact K₀) (hK₁ : IsCompact K₁) (hΩ : IsOpen Ω)
    (h₀ : K₀ ⊆ interior K₁) (h₁ : K₁ ⊆ Ω) :
    ∃ ε : ℝ, 0 < ε ∧
      (∀ z ∈ K₀, ∀ w, dist w z < ε → w ∈ K₁) ∧
      (∀ z ∈ K₁, ∀ w, dist w z < ε → w ∈ Ω) := by
  obtain ⟨δ₀,hδ₀,hth₀⟩ := hK₀.exists_thickening_subset_open isOpen_interior h₀
  obtain ⟨δ₁,hδ₁,hth₁⟩ := hK₁.exists_thickening_subset_open hΩ h₁
  refine ⟨min δ₀ δ₁, lt_min hδ₀ hδ₁, ?_, ?_⟩
  · intro z hz w hw
    exact interior_subset (hth₀ (Metric.mem_thickening_iff.mpr
      ⟨z,hz,hw.trans_le (min_le_left _ _)⟩))
  · intro z hz w hw
    exact hth₁ (Metric.mem_thickening_iff.mpr ⟨z,hz,hw.trans_le (min_le_right _ _)⟩)

end HolomorphicAnosov
