import HolomorphicAnosov.Topology.CWComplex.PrismClosedDiskCharacteristic
import HolomorphicAnosov.Topology.CWComplex.PrismPartialEquivData
import HolomorphicAnosov.Topology.CWComplex.IntervalProductClosedCriterion
import HolomorphicAnosov.Topology.CellularTelescopeHausdorff
import HolomorphicAnosov.Topology.CompactCWFiniteSubcomplex

namespace HolomorphicAnosov
open MappingTelescope.Sequence

private theorem local_bottom_identification {X : ℕ → Type*} [∀ n, TopologicalSpace (X n)]
    (c : ∀ n, C(X n, X (n + 1))) (n : ℕ) (x : X n) :
    Quot.mk (CellularTelescopeAdjunction.relation c) (Sum.inr ⟨n, (x, 0)⟩) =
      Quot.mk (CellularTelescopeAdjunction.relation c) (Sum.inl ⟨n, x⟩) := by
  apply Quot.sound
  refine ⟨⟨⟨n, (x, 0)⟩, Or.inl rfl⟩, rfl, ?_⟩
  simp [CellularTelescopeAdjunction.attach]

private theorem local_top_identification {X : ℕ → Type*} [∀ n, TopologicalSpace (X n)]
    (c : ∀ n, C(X n, X (n + 1))) (n : ℕ) (x : X n) :
    Quot.mk (CellularTelescopeAdjunction.relation c) (Sum.inr ⟨n, (x, 1)⟩) =
      Quot.mk (CellularTelescopeAdjunction.relation c) (Sum.inl ⟨n + 1, c n x⟩) := by
  apply Quot.sound
  refine ⟨⟨⟨n, (x, 1)⟩, Or.inr rfl⟩, rfl, ?_⟩
  have h : (1 : unitInterval) ≠ 0 := fun h ↦ one_ne_zero (congrArg Subtype.val h)
  simp [CellularTelescopeAdjunction.attach, h]

private theorem local_cylinder_respects {X : ℕ → Type*} [∀ n, TopologicalSpace (X n)]
    (c : ∀ n, C(X n, X (n + 1))) (p q : MappingTelescope.Sequence.Cylinder X)
    (hpq : MappingTelescope.Sequence.setoid c p q) :
    Quot.mk (CellularTelescopeAdjunction.relation c) (Sum.inr p) =
      Quot.mk (CellularTelescopeAdjunction.relation c) (Sum.inr q) := by
  change Relation.EqvGen (MappingTelescope.Sequence.edge c) p q at hpq
  induction hpq with
  | rel p q h =>
      obtain ⟨n, x, h | h⟩ := h
      · rcases h with ⟨rfl, rfl⟩
        exact (local_top_identification c n x).trans
          (local_bottom_identification c (n + 1) (c n x)).symm
      · rcases h with ⟨rfl, rfl⟩
        exact (local_bottom_identification c (n + 1) (c n x)).trans
          (local_top_identification c n x).symm
  | refl => rfl
  | symm _ _ _ h => exact h.symm
  | trans _ _ _ _ _ h h' => exact h.trans h'

theorem CellularTelescopeAdjunction.attach_mapsTo_summand_skeleton
    {X : ℕ → Type u} [∀ n, TopologicalSpace (X n)]
    [∀ n, T2Space (X n)]
    [∀ n, Topology.CWComplex (Set.univ : Set (X n))]
    (c : ∀ n, C(X n, X (n + 1)))
    (hc : ∀ n d : ℕ, Set.MapsTo (c n)
      (Topology.CWComplex.skeleton (Set.univ : Set (X n)) d : Set (X n))
      (Topology.CWComplex.skeleton (Set.univ : Set (X (n + 1))) d : Set (X (n + 1))))
    (d : ℕ) (z : CellularTelescopeAdjunction.endpoints X)
    (hz : z.val.2.1 ∈ Topology.CWComplex.skeleton
      (Set.univ : Set (X z.val.1)) d) :
    CellularTelescopeAdjunction.attach c z ∈ {p : (Σ n, X n) |
      p.2 ∈ Topology.CWComplex.skeleton (Set.univ : Set (X p.1)) d} := by
  rcases z with ⟨⟨n, x, t⟩, ht⟩
  change t = 0 ∨ t = 1 at ht
  rcases ht with rfl | rfl
  · simpa [CellularTelescopeAdjunction.attach] using hz
  · have hc' := hc n d hz
    simpa [CellularTelescopeAdjunction.attach] using hc'


/-- The endpoint carrier is exactly the union of the two endpoint slices.

Source: Fritsch–Piccinini Theorem 2.3.1 p.62. This is a set-level identity in
the original cylinder carrier; the topology remains the native coproduct
subspace topology supplied by `endpoints_isClosed`. -/
theorem CellularTelescopeAdjunction.endpoints_eq_sigma_endpoint_copies
    {X : ℕ → Type u} [∀ n, TopologicalSpace (X n)] :
    CellularTelescopeAdjunction.endpoints X =
      {z : MappingTelescope.Sequence.Cylinder X | z.2.2 = 0} ∪
        {z : MappingTelescope.Sequence.Cylinder X | z.2.2 = 1} := by
  ext z
  rfl

/-- The endpoint carrier is the sigma union of native product endpoint slices.

Source: Fritsch–Piccinini Theorem 2.3.1 p.62 and the reviewed interval-product
provider. The equality is only set-theoretic and introduces no alternate
topology or CW instance. -/
theorem CellularTelescopeAdjunction.endpoints_eq_sigma_product_slices
    {X : ℕ → Type u} [∀ n, TopologicalSpace (X n)] :
    CellularTelescopeAdjunction.endpoints X = ⋃ n : ℕ,
      Sigma.mk n '' ((Set.univ : Set (X n)).prod ({0, 1} : Set unitInterval)) := by
  ext z
  constructor
  · intro hz
    rcases z with ⟨n, x, t⟩
    change t = 0 ∨ t = 1 at hz
    rcases hz with rfl | rfl
    · refine Set.mem_iUnion.2 ⟨n, ?_⟩
      exact ⟨(x, 0), ⟨Set.mem_univ _, by simp⟩, rfl⟩
    · refine Set.mem_iUnion.2 ⟨n, ?_⟩
      exact ⟨(x, 1), ⟨Set.mem_univ _, by simp⟩, rfl⟩
  · intro hz
    rcases Set.mem_iUnion.1 hz with ⟨n, hz⟩
    rcases hz with ⟨y, hy, hEq⟩
    have htime := congrArg (fun z : MappingTelescope.Sequence.Cylinder X ↦ z.2.2) hEq
    have htime' : y.2 = z.2.2 := by simpa using htime
    have hends : y.2 = 0 ∨ y.2 = 1 := by
      simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using hy.2
    change z.2.2 = 0 ∨ z.2.2 = 1
    simpa [htime'] using hends



/-- The inverse image of all canonical levels is exactly the cylinder endpoints.
Source: the endpoint-adjunction carrier calculation in Fritsch–Piccinini A.4.8(ii),
p.260, specialized to the concrete telescope. Every generating seam has endpoints
on both sides, so equivalence closure preserves endpoint membership. Conversely
bottom endpoints lie in their own level and top endpoints in the receiving level.
No injectivity, CW structure, or nonempty-layer assumption is used. -/
theorem CellularTelescopeAdjunction.preimage_levels_eq_endpoints
    {X : ℕ → Type*} [∀ n, TopologicalSpace (X n)]
    (c : ∀ n, C(X n, X (n + 1))) :
    (quotient c) ⁻¹' (⋃ n, Set.range (level c n)) =
      CellularTelescopeAdjunction.endpoints X := by
  have hinvariant (a b : Cylinder X) (hab : setoid c a b) :
      a ∈ CellularTelescopeAdjunction.endpoints X ↔
        b ∈ CellularTelescopeAdjunction.endpoints X := by
    change Relation.EqvGen (edge c) a b at hab
    induction hab with
    | rel a b hab =>
        rcases hab with ⟨n, x, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ <;>
          simp [CellularTelescopeAdjunction.endpoints]
    | refl => exact Iff.rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  ext z
  constructor
  · intro hz
    rcases Set.mem_iUnion.mp hz with ⟨n, x, hx⟩
    have hrel : setoid c (⟨n, (x, 0)⟩ : Cylinder X) z := Quotient.exact hx
    exact (hinvariant _ _ hrel).mp (Or.inl rfl)
  · rcases z with ⟨n, x, t⟩
    intro hz
    change t = 0 ∨ t = 1 at hz
    rcases hz with rfl | rfl
    · exact Set.mem_iUnion.mpr ⟨n, x, rfl⟩
    · exact Set.mem_iUnion.mpr ⟨n + 1, c n x, (levelTop_eq c n x).symm⟩

/-- All canonical level copies form a closed subset of the original telescope.
Source: Fritsch–Piccinini A.4.8(ii), p.260: the level part of a closed adjunction
is closed. Its quotient preimage is the closed union of cylinder endpoints. -/
theorem CellularTelescopeAdjunction.levels_isClosed
    {X : ℕ → Type*} [∀ n, TopologicalSpace (X n)]
    (c : ∀ n, C(X n, X (n + 1))) :
    IsClosed (⋃ n, Set.range (level c n)) := by
  have hq : Topology.IsQuotientMap (quotient c) := isQuotientMap_quotient_mk'
  apply (Topology.isQuotientMap_iff_isClosed.mp hq).2 _ |>.mpr
  rw [CellularTelescopeAdjunction.preimage_levels_eq_endpoints]
  exact CellularTelescopeAdjunction.endpoints_isClosed


/-- The complement of the level carrier has exactly the cylinder-interior
preimage. Source: Fritsch–Piccinini Theorem 2.3.1 pp.62–63; the open prism
region is the complement of the two endpoint slices. -/
theorem CellularTelescopeAdjunction.preimage_off_levels_eq_cylinder_interiors
    {X : ℕ → Type*} [∀ n, TopologicalSpace (X n)]
    (c : ∀ n, C(X n, X (n + 1))) :
    (quotient c) ⁻¹' (⋃ n, Set.range (level c n))ᶜ =
      {z : MappingTelescope.Sequence.Cylinder X |
        z.2.2 ≠ 0 ∧ z.2.2 ≠ 1} := by
  rw [Set.preimage_compl]
  rw [CellularTelescopeAdjunction.preimage_levels_eq_endpoints]
  ext z
  simp [CellularTelescopeAdjunction.endpoints]

/-- The complement of the union of all canonical level copies is open in the
original telescope. Source: Fritsch–Piccinini Theorem 2.3.1 pp.62–63. -/
theorem CellularTelescopeAdjunction.off_levels_isOpen
    {X : ℕ → Type*} [∀ n, TopologicalSpace (X n)]
    (c : ∀ n, C(X n, X (n + 1))) :
    IsOpen (⋃ n, Set.range (level c n))ᶜ := by
  exact isOpen_compl_iff.mpr (CellularTelescopeAdjunction.levels_isClosed c)


/-- The telescope quotient remains a quotient map after restricting to the
off-level open region. This is the final-topology input for the prism charts:
the restricted domain is exactly the preimage of the open complement of the
canonical level carrier, so Mathlib's restriction theorem applies directly to
the original quotient projection. -/
theorem CellularTelescopeAdjunction.off_levels_restrict_isQuotientMap
    {X : ℕ → Type*} [∀ n, TopologicalSpace (X n)]
    (c : ∀ n, C(X n, X (n + 1))) :
    Topology.IsQuotientMap
      ((⋃ n, Set.range (level c n))ᶜ.restrictPreimage (quotient c)) := by
  exact (isQuotientMap_quotient_mk').restrictPreimage_isOpen
    (CellularTelescopeAdjunction.off_levels_isOpen c)


/-- Continuity on the off-level part of the telescope is tested on the open
cylinder interiors. This is the quotient-topology criterion specialized to the
actual telescope projection, with the preimage converted by the endpoint
calculation above. -/
theorem CellularTelescopeAdjunction.continuousOn_off_levels_iff
    {X : ℕ → Type*} [∀ n, TopologicalSpace (X n)] {W : Type*} [TopologicalSpace W]
    (c : ∀ n, C(X n, X (n + 1))) (g : telescope c → W) :
    ContinuousOn g (⋃ n, Set.range (level c n))ᶜ ↔
      ContinuousOn (g ∘ quotient c)
        {z : MappingTelescope.Sequence.Cylinder X |
          z.2.2 ≠ 0 ∧ z.2.2 ≠ 1} := by
  have h := Topology.IsQuotientMap.continuousOn_isOpen_iff
    (f := quotient c) (g := g) isQuotientMap_quotient_mk'
      (CellularTelescopeAdjunction.off_levels_isOpen c)
  rw [CellularTelescopeAdjunction.preimage_off_levels_eq_cylinder_interiors c] at h
  exact h


/-- Interior cylinder representatives have singleton telescope quotient fibres.
The generated relation only moves endpoint representatives, so an equivalence
between two representatives whose times avoid both endpoints must be reflexive.
This is the injectivity input for transporting prism charts through the
telescope quotient. -/
theorem CellularTelescopeAdjunction.quotient_cylinderInterior_injective
    {X : ℕ → Type*} [∀ n, TopologicalSpace (X n)]
    (c : ∀ n, C(X n, X (n + 1))) :
    Function.Injective
      (fun z : {z : MappingTelescope.Sequence.Cylinder X |
        z.2.2 ≠ 0 ∧ z.2.2 ≠ 1} ↦ quotient c z.1) := by
  have hinvariant : ∀ (p q : MappingTelescope.Sequence.Cylinder X),
      setoid c p q →
        (p.2.2 ≠ 0 ∧ p.2.2 ≠ 1 ↔ q.2.2 ≠ 0 ∧ q.2.2 ≠ 1) := by
    intro p q hpq
    change Relation.EqvGen (edge c) p q at hpq
    induction hpq with
    | rel p q h =>
        rcases h with ⟨n, x, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ <;>
          simp
    | refl => exact Iff.rfl
    | symm p q _ ih => exact ih.symm
    | trans p q r _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  have huniq : ∀ (p q : MappingTelescope.Sequence.Cylinder X),
      setoid c p q →
        (p.2.2 ≠ 0 ∧ p.2.2 ≠ 1) →
        (q.2.2 ≠ 0 ∧ q.2.2 ≠ 1) → p = q := by
    intro p q hpq
    change Relation.EqvGen (edge c) p q at hpq
    induction hpq with
    | rel p q h =>
        rcases h with ⟨n, x, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ <;>
          intro hp hq <;> simp_all
    | refl => intro _ _; rfl
    | symm p q _ ih =>
        intro hp hq
        exact (ih hq hp).symm
    | trans p q r _ _ ih₁ ih₂ =>
        intro hp hr
        have hq : q.2.2 ≠ 0 ∧ q.2.2 ≠ 1 := (hinvariant p q ‹_›).mp hp
        exact (ih₁ hp hq).trans (ih₂ hq hr)
  intro a b hab
  apply Subtype.ext
  exact huniq a.1 b.1 (Quotient.exact hab) a.2 b.2


/-- The quotient over the off-level region is an open embedding in the original
subspace topologies. Source: Fritsch–Piccinini A.4.8(iii), p.260, specialized to
the telescope. The endpoint-preimage identity places every restricted source
point in a cylinder interior, where quotient fibres are singletons. For any
open source set, injectivity identifies its image's full preimage with that
set; the restricted quotient criterion therefore makes the image open. -/
theorem CellularTelescopeAdjunction.off_levels_restrict_isOpenEmbedding
    {X : ℕ → Type*} [∀ n, TopologicalSpace (X n)]
    (c : ∀ n, C(X n, X (n + 1))) :
    Topology.IsOpenEmbedding
      ((⋃ n, Set.range (level c n))ᶜ.restrictPreimage (quotient c)) := by
  let U : Set (telescope c) := (⋃ n, Set.range (level c n))ᶜ
  have hq : Topology.IsQuotientMap (U.restrictPreimage (quotient c)) :=
    CellularTelescopeAdjunction.off_levels_restrict_isQuotientMap c
  have hinj : Function.Injective (U.restrictPreimage (quotient c)) := by
    intro a b hab
    have ha : a.val.2.2 ≠ 0 ∧ a.val.2.2 ≠ 1 := by
      have h : a.val ∈ (quotient c) ⁻¹' ((⋃ n, Set.range (level c n))ᶜ) := by
        simpa [U] using a.prop
      have hEq := congrArg (fun s : Set (MappingTelescope.Sequence.Cylinder X) => a.val ∈ s)
        (CellularTelescopeAdjunction.preimage_off_levels_eq_cylinder_interiors c)
      exact hEq.mp h
    have hb : b.val.2.2 ≠ 0 ∧ b.val.2.2 ≠ 1 := by
      have h : b.val ∈ (quotient c) ⁻¹' ((⋃ n, Set.range (level c n))ᶜ) := by
        simpa [U] using b.prop
      have hEq := congrArg (fun s : Set (MappingTelescope.Sequence.Cylinder X) => b.val ∈ s)
        (CellularTelescopeAdjunction.preimage_off_levels_eq_cylinder_interiors c)
      exact hEq.mp h
    have he := CellularTelescopeAdjunction.quotient_cylinderInterior_injective c
      (a₁ := ⟨a.val, ha⟩) (a₂ := ⟨b.val, hb⟩) (congrArg Subtype.val hab)
    exact Subtype.ext (congrArg
      (fun z : {z : MappingTelescope.Sequence.Cylinder X |
        z.2.2 ≠ 0 ∧ z.2.2 ≠ 1} ↦ z.val) he)
  refine Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap hq.continuous hinj ?_
  intro V hV
  apply hq.isCoinducing.isOpen_preimage.mp
  rwa [Set.preimage_image_eq _ hinj]


/-- The range of the restricted quotient is exactly the complement of the
canonical level carrier. This makes the prism region an actual open subspace
of the telescope, rather than merely an abstract restricted codomain. -/
theorem CellularTelescopeAdjunction.off_levels_restrict_range
    {X : ℕ → Type*} [∀ n, TopologicalSpace (X n)]
    (c : ∀ n, C(X n, X (n + 1))) :
    Set.range ((⋃ n, Set.range (level c n))ᶜ.restrictPreimage (quotient c)) =
      (⋃ n, Set.range (level c n))ᶜ := by
  rw [Set.range_restrictPreimage]
  have hr : Set.range (quotient c) = (Set.univ : Set (telescope c)) :=
    Set.range_eq_univ.mpr
      (isQuotientMap_quotient_mk' :
        Topology.IsQuotientMap (quotient c)).surjective
  rw [hr]
  ext y
  simp


/-- The original cylinder interiors are homeomorphic to the off-level region
of the original telescope. Source: Fritsch–Piccinini A.4.8(iii), p.260. Rewrite
the cylinder-interior carrier as the preimage of the off-level region, then
use the already proved restricted embedding and quotient surjectivity. Both
subspaces retain their native topologies; the forward map is the original
quotient projection and the inverse selects its unique interior representative. -/
noncomputable def CellularTelescopeAdjunction.cylinderInteriorsHomeomorph
    {X : ℕ → Type*} [∀ n, TopologicalSpace (X n)]
    (c : ∀ n, C(X n, X (n + 1))) :
    {z : MappingTelescope.Sequence.Cylinder X | z.2.2 ≠ 0 ∧ z.2.2 ≠ 1} ≃ₜ
      ↥((⋃ n, Set.range (level c n))ᶜ) :=
  (Homeomorph.setCongr
    (CellularTelescopeAdjunction.preimage_off_levels_eq_cylinder_interiors c).symm).trans
    ((CellularTelescopeAdjunction.off_levels_restrict_isOpenEmbedding c).isEmbedding.toHomeomorphOfSurjective
      (CellularTelescopeAdjunction.off_levels_restrict_isQuotientMap c).surjective)


/-- The interior homeomorphism sends a cylinder representative to its original
quotient class, viewed in the off-level subtype. -/
theorem CellularTelescopeAdjunction.cylinderInteriorsHomeomorph_apply
    {X : ℕ → Type*} [∀ n, TopologicalSpace (X n)]
    (c : ∀ n, C(X n, X (n + 1)))
    (z : {z : MappingTelescope.Sequence.Cylinder X |
      z.2.2 ≠ 0 ∧ z.2.2 ≠ 1}) :
    CellularTelescopeAdjunction.cylinderInteriorsHomeomorph c z =
      ⟨quotient c z.1, by
        change z.1 ∈ (quotient c) ⁻¹' (⋃ n, Set.range (level c n))ᶜ
        rw [CellularTelescopeAdjunction.preimage_off_levels_eq_cylinder_interiors c]
        exact z.2⟩ := by
  rfl


/-- The cylinder-interior quotient map is an open embedding into the full
telescope. It factors through the homeomorphism onto the off-level subtype and
the open-subspace inclusion of that subtype into the telescope. -/
theorem CellularTelescopeAdjunction.cylinderInteriors_isOpenEmbedding
    {X : ℕ → Type*} [∀ n, TopologicalSpace (X n)]
    (c : ∀ n, C(X n, X (n + 1))) :
    Topology.IsOpenEmbedding
      (fun z : {z : MappingTelescope.Sequence.Cylinder X |
        z.2.2 ≠ 0 ∧ z.2.2 ≠ 1} ↦ quotient c z.1) := by
  let U : Set (telescope c) := (⋃ n, Set.range (level c n))ᶜ
  have hi : Topology.IsOpenEmbedding (fun y : U ↦ (y : telescope c)) :=
    (CellularTelescopeAdjunction.off_levels_isOpen c).isOpenEmbedding_subtypeVal
  have hc := (CellularTelescopeAdjunction.cylinderInteriorsHomeomorph c).isOpenEmbedding
  have hcomp : Topology.IsOpenEmbedding
      (fun z : {z : MappingTelescope.Sequence.Cylinder X |
        z.2.2 ≠ 0 ∧ z.2.2 ≠ 1} ↦
        (CellularTelescopeAdjunction.cylinderInteriorsHomeomorph c z : telescope c)) :=
    hi.comp hc
  simpa [CellularTelescopeAdjunction.cylinderInteriorsHomeomorph_apply, U] using hcomp


/-- Disjoint raw prism regions retain disjoint images in the telescope.
Source: the cell-disjointness step of Fritsch–Piccinini Theorem 2.3.1, pp.62–63.
If an image point belonged to both regions, its two interior representatives
would coincide by interior injectivity, contradicting disjointness upstairs.
The regions may span different cylinder summands and require no openness. -/
theorem CellularTelescopeAdjunction.disjoint_quotient_images_of_interior
    {X : ℕ → Type*} [∀ n, TopologicalSpace (X n)]
    (c : ∀ n, C(X n, X (n + 1))) {S T : Set (Cylinder X)}
    (hS : S ⊆ {z : Cylinder X | z.2.2 ≠ 0 ∧ z.2.2 ≠ 1})
    (hT : T ⊆ {z : Cylinder X | z.2.2 ≠ 0 ∧ z.2.2 ≠ 1})
    (hST : Disjoint S T) : Disjoint (quotient c '' S) (quotient c '' T) := by
  apply Set.disjoint_left.mpr
  rintro y ⟨a, ha, hay⟩ ⟨b, hb, hby⟩
  have he := CellularTelescopeAdjunction.quotient_cylinderInterior_injective c
    (a₁ := ⟨a, hS ha⟩) (a₂ := ⟨b, hT hb⟩) (hay.trans hby.symm)
  have hab : a = b := congrArg
    (fun z : {z : Cylinder X | z.2.2 ≠ 0 ∧ z.2.2 ≠ 1} ↦ z.val) he
  exact Set.disjoint_left.mp hST ha (hab.symm ▸ hb)


/-- The proposed level and prism open cells cover the actual telescope.
Source: Fritsch–Piccinini Theorem 2.3.1, pp.62–63, cell-covering step.
Choose a cylinder representative. At its bottom choose a source open cell;
at its top use the seam equation and choose a receiving open cell. At all
other times the interval bounds are strict, and a source open cell gives the
required prism. This allows empty layers and noninjective bonding maps. -/
theorem CellularTelescopeAdjunction.level_and_prism_cells_cover
    {X : ℕ → Type*} [∀ n, TopologicalSpace (X n)] [∀ n, T2Space (X n)]
    [∀ n, Topology.CWComplex (Set.univ : Set (X n))]
    (c : ∀ n, C(X n, X (n + 1))) (y : telescope c) :
    (∃ (n d : ℕ) (e : Topology.CWComplex.cell (Set.univ : Set (X n)) d),
      y ∈ level c n '' Topology.CWComplex.openCell (C := (Set.univ : Set (X n))) d e) ∨
    (∃ (n d : ℕ) (e : Topology.CWComplex.cell (Set.univ : Set (X n)) d),
      y ∈ cylinder c n ''
        ((Topology.CWComplex.openCell (C := (Set.univ : Set (X n))) d e).prod
          {t : unitInterval | (0 : ℝ) < (t : ℝ) ∧ (t : ℝ) < 1})) := by
  have hcell (n : ℕ) (x : X n) :
      ∃ (d : ℕ) (e : Topology.CWComplex.cell (Set.univ : Set (X n)) d),
        x ∈ Topology.CWComplex.openCell (C := (Set.univ : Set (X n))) d e := by
    have hx : x ∈ ⋃ (d : ℕ) (e : Topology.CWComplex.cell (Set.univ : Set (X n)) d),
        Topology.CWComplex.openCell (C := (Set.univ : Set (X n))) d e := by
      exact (Topology.CWComplex.iUnion_openCell_eq_complex
        (C := (Set.univ : Set (X n)))).symm ▸ Set.mem_univ x
    simpa only [Set.mem_iUnion] using hx
  refine Quotient.inductionOn y ?_
  rintro ⟨n, x, t⟩
  by_cases ht0 : t = 0
  · subst t
    obtain ⟨d, e, he⟩ := hcell n x
    exact Or.inl ⟨n, d, e, x, he, rfl⟩
  by_cases ht1 : t = 1
  · subst t
    obtain ⟨d, e, he⟩ := hcell (n + 1) (c n x)
    exact Or.inl ⟨n + 1, d, e, c n x, he, (levelTop_eq c n x).symm⟩
  · obtain ⟨d, e, he⟩ := hcell n x
    refine Or.inr ⟨n, d, e, (x, t), ⟨he, ?_, ?_⟩, rfl⟩
    · exact lt_of_le_of_ne t.prop.1 (fun h ↦ ht0 (Subtype.ext h.symm))
    · exact lt_of_le_of_ne t.prop.2 (fun h ↦ ht1 (Subtype.ext h))


/-- Distinct points in the coproduct of original levels remain distinct in the
telescope. Source: Fritsch–Piccinini A.4.8(ii), p.260, specialized to the endpoint
adjunction. Assign every top representative to its receiving level point and
every other representative to its own level point. This set map agrees across
every generating seam, hence across its equivalence closure. On bottom
representatives it is the identity, so equal bottom classes have equal level
labels and points. No inverse or injectivity of a bonding map is used. -/
theorem CellularTelescopeAdjunction.levels_injective
    {X : ℕ → Type*} [∀ n, TopologicalSpace (X n)]
    (c : ∀ n, C(X n, X (n + 1))) :
    Function.Injective (fun z : Σ n, X n ↦ level c z.1 z.2) := by
  classical
  let normalize : Cylinder X → Σ n, X n := fun z ↦
    if z.2.2 = 1 then ⟨z.1 + 1, c z.1 z.2.1⟩ else ⟨z.1, z.2.1⟩
  have hnormalize (p q : Cylinder X) (hpq : setoid c p q) :
      normalize p = normalize q := by
    change Relation.EqvGen (edge c) p q at hpq
    induction hpq with
    | rel p q h =>
        rcases h with ⟨n, x, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ <;>
          simp [normalize]
    | refl => rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  rintro ⟨n, x⟩ ⟨m, y⟩ h
  have hr : setoid c (⟨n, (x, 0)⟩ : Cylinder X) ⟨m, (y, 0)⟩ :=
    Quotient.exact h
  simpa [normalize] using hnormalize _ _ hr


/-- Distinct level open cells have disjoint images in the telescope.
Source: Fritsch–Piccinini Theorem 2.3.1, pp.62–63, cell-partition step.
An intersection would give equal points in the level coproduct by its proved
injectivity. Their level indices therefore agree, and the source CW open-cell
disjointness forces the dimension and cell indices to agree as well. -/
theorem CellularTelescopeAdjunction.level_cells_disjoint
    {X : ℕ → Type*} [∀ n, TopologicalSpace (X n)]
    [∀ n, Topology.CWComplex (Set.univ : Set (X n))]
    (c : ∀ n, C(X n, X (n + 1))) {n m d k : ℕ}
    (e : Topology.CWComplex.cell (Set.univ : Set (X n)) d)
    (f : Topology.CWComplex.cell (Set.univ : Set (X m)) k)
    (hne : (⟨n, d, e⟩ : Σ n, Σ d, Topology.CWComplex.cell (Set.univ : Set (X n)) d)
      ≠ ⟨m, k, f⟩) :
    Disjoint (level c n '' Topology.CWComplex.openCell (C := Set.univ) d e)
      (level c m '' Topology.CWComplex.openCell (C := Set.univ) k f) := by
  apply Set.disjoint_left.mpr
  rintro z ⟨x, hx, hxz⟩ ⟨y, hy, hyz⟩
  have hxy := CellularTelescopeAdjunction.levels_injective c
    (a₁ := ⟨n, x⟩) (a₂ := ⟨m, y⟩) (hxz.trans hyz.symm)
  have hnm : n = m := congrArg Sigma.fst hxy
  subst m
  have hpoints : x = y := sigma_mk_injective hxy
  subst y
  have hcells : (⟨d, e⟩ : Σ d, Topology.CWComplex.cell (Set.univ : Set (X n)) d)
      ≠ ⟨k, f⟩ := by
    intro h
    apply hne
    exact congrArg (Sigma.mk n) h
  exact Set.disjoint_left.mp
    (Topology.CWComplex.disjoint_openCell_of_ne hcells) hx hy


/-- Distinct prism labels have disjoint open images in the telescope.
Source: Fritsch–Piccinini Theorem 2.3.1, pp.62–63. A common point gives two
interior cylinder representatives; quotient interior injectivity identifies
their summand and point coordinates. Source CW open-cell disjointness then
identifies the cell labels, contradicting the assumed distinct prism labels. -/
theorem CellularTelescopeAdjunction.prism_cells_disjoint
    {X : ℕ → Type*} [∀ n, TopologicalSpace (X n)]
    [∀ n, Topology.CWComplex (Set.univ : Set (X n))]
    (c : ∀ n, C(X n, X (n + 1))) {n m d k : ℕ}
    (e : Topology.CWComplex.cell (Set.univ : Set (X n)) d)
    (f : Topology.CWComplex.cell (Set.univ : Set (X m)) k)
    (hne : (⟨n, d, e⟩ : Σ n, Σ d, Topology.CWComplex.cell (Set.univ : Set (X n)) d)
      ≠ ⟨m, k, f⟩) :
    Disjoint
      (cylinder c n ''
        ((Topology.CWComplex.openCell (C := Set.univ) d e).prod
          {t : unitInterval | (0 : ℝ) < (t : ℝ) ∧ (t : ℝ) < 1}))
      (cylinder c m ''
        ((Topology.CWComplex.openCell (C := Set.univ) k f).prod
          {t : unitInterval | (0 : ℝ) < (t : ℝ) ∧ (t : ℝ) < 1})) := by
  apply Set.disjoint_left.mpr
  rintro y ⟨z, hz, hzy⟩ ⟨w, hw, hwy⟩
  rcases hz with ⟨hxe, htz⟩
  rcases hw with ⟨hxf, htw⟩
  have hzint : z.2 ≠ 0 ∧ z.2 ≠ 1 := by
    constructor <;> intro h
    · simpa [h] using htz.1
    · simpa [h] using htz.2
  have hwint : w.2 ≠ 0 ∧ w.2 ≠ 1 := by
    constructor <;> intro h
    · simpa [h] using htw.1
    · simpa [h] using htw.2
  have he := CellularTelescopeAdjunction.quotient_cylinderInterior_injective c
    (a₁ := ⟨⟨n, z⟩, hzint⟩) (a₂ := ⟨⟨m, w⟩, hwint⟩)
      (hzy.trans hwy.symm)
  have hraw : (⟨n, z⟩ : Cylinder X) = ⟨m, w⟩ :=
    congrArg (fun q : {q : Cylinder X | q.2.2 ≠ 0 ∧ q.2.2 ≠ 1} ↦ q.val) he
  have hnm : n = m := congrArg Sigma.fst hraw
  subst m
  have hzw : z = w :=
    (Sigma.mk.inj_iff.mp hraw).2 |> eq_of_heq
  subst w
  by_cases hef : (⟨d, e⟩ : Σ d, Topology.CWComplex.cell (Set.univ : Set (X n)) d) = ⟨k, f⟩
  · apply hne
    exact congrArg (Sigma.mk n) hef
  · exact Set.disjoint_left.mp (Topology.CWComplex.disjoint_openCell_of_ne hef) hxe hxf


/-- Every level open cell is disjoint from every open prism image.
Source: Fritsch–Piccinini Theorem 2.3.1, pp.62–63, mixed cell-partition step.
A point of a level image belongs to the full level carrier. Its cylinder
representative must therefore be an endpoint by the proved preimage identity,
which contradicts the strict time inequalities of an open prism. -/
theorem CellularTelescopeAdjunction.level_prism_cells_disjoint
    {X : ℕ → Type*} [∀ n, TopologicalSpace (X n)]
    [∀ n, Topology.CWComplex (Set.univ : Set (X n))]
    (c : ∀ n, C(X n, X (n + 1))) (n m d k : ℕ)
    (e : Topology.CWComplex.cell (Set.univ : Set (X n)) d)
    (f : Topology.CWComplex.cell (Set.univ : Set (X m)) k) :
    Disjoint (level c n '' Topology.CWComplex.openCell (C := Set.univ) d e)
      (cylinder c m ''
        ((Topology.CWComplex.openCell (C := Set.univ) k f).prod
          {t : unitInterval | (0 : ℝ) < (t : ℝ) ∧ (t : ℝ) < 1})) := by
  apply Set.disjoint_left.mpr
  rintro y ⟨x, _, hxy⟩ ⟨z, hz, hzy⟩
  have hlevel : quotient c (⟨m, z⟩ : Cylinder X) ∈ ⋃ j, Set.range (level c j) := by
    exact Set.mem_iUnion.mpr ⟨n, x, hxy.trans hzy.symm⟩
  have hend : (⟨m, z⟩ : Cylinder X) ∈ CellularTelescopeAdjunction.endpoints X := by
    change (⟨m, z⟩ : Cylinder X) ∈ (quotient c) ⁻¹' (⋃ j, Set.range (level c j)) at hlevel
    rw [CellularTelescopeAdjunction.preimage_levels_eq_endpoints c] at hlevel
    exact hlevel
  change z.2 = 0 ∨ z.2 = 1 at hend
  rcases hend with h | h
  · simpa [h] using hz.2.1
  · simpa [h] using hz.2.2


/-- The preimage of any subset of the original level coproduct consists of
its bottom copies and the top copies whose bonded points belong to that subset.
Source: Fritsch–Piccinini A.4.8(ii), p.260, level-inclusion topology guard.
Every representative above a level point is an endpoint. At the bottom the
level label is unchanged; at the top the seam identifies its receiving level.
Injectivity of the level coproduct rules out any further level identifications.
This formula also applies to nonclosed subsets and noninjective bonds. -/
theorem CellularTelescopeAdjunction.preimage_level_image
    {X : ℕ → Type*} [∀ n, TopologicalSpace (X n)]
    (c : ∀ n, C(X n, X (n + 1))) (S : Set (Σ n, X n)) :
    (quotient c) ⁻¹' ((fun z : Σ n, X n ↦ level c z.1 z.2) '' S) =
      {z : Cylinder X | z.2.2 = 0 ∧ (⟨z.1, z.2.1⟩ : Σ n, X n) ∈ S} ∪
      {z : Cylinder X | z.2.2 = 1 ∧ (⟨z.1 + 1, c z.1 z.2.1⟩ : Σ n, X n) ∈ S} := by
  ext z
  rcases z with ⟨n, x, t⟩
  constructor
  · rintro ⟨a, ha, haq⟩
    have hlevels : quotient c ⟨n, (x, t)⟩ ∈ ⋃ j, Set.range (level c j) :=
      Set.mem_iUnion.mpr ⟨a.1, a.2, haq⟩
    have hend : (⟨n, (x, t)⟩ : Cylinder X) ∈ CellularTelescopeAdjunction.endpoints X := by
      change (⟨n, (x, t)⟩ : Cylinder X) ∈
        (quotient c) ⁻¹' (⋃ j, Set.range (level c j)) at hlevels
      rw [CellularTelescopeAdjunction.preimage_levels_eq_endpoints c] at hlevels
      exact hlevels
    change t = 0 ∨ t = 1 at hend
    rcases hend with rfl | rfl
    · have he : a = ⟨n, x⟩ := CellularTelescopeAdjunction.levels_injective c haq
      exact Or.inl ⟨rfl, he ▸ ha⟩
    · have he : a = ⟨n + 1, c n x⟩ :=
        CellularTelescopeAdjunction.levels_injective c (haq.trans (levelTop_eq c n x))
      exact Or.inr ⟨rfl, he ▸ ha⟩
  · rintro (⟨ht, hS⟩ | ⟨ht, hS⟩)
    · change t = 0 at ht
      subst t
      exact ⟨⟨n, x⟩, hS, rfl⟩
    · change t = 1 at ht
      subst t
      exact ⟨⟨n + 1, c n x⟩, hS, (levelTop_eq c n x).symm⟩


/-- The inclusion of the full level coproduct into the telescope is closed.
Source: Fritsch–Piccinini A.4.8(ii), p.260, level-inclusion topology guard.
The preimage of the image of a closed level subset is the union of its bottom
copies and the top copies pulled back along the bonds. Both are closed: time
is continuous, the endpoint singletons are closed, and the bonds are continuous.
The original quotient topology then makes the image closed. No injectivity of
the bonds or separation hypothesis on the level spaces is required. -/
theorem CellularTelescopeAdjunction.levels_isClosedMap
    {X : ℕ → Type*} [∀ n, TopologicalSpace (X n)]
    (c : ∀ n, C(X n, X (n + 1))) :
    IsClosedMap (fun z : Σ n, X n ↦ level c z.1 z.2) := by
  intro S hS
  have hq : Topology.IsQuotientMap (quotient c) := isQuotientMap_quotient_mk'
  apply (Topology.isQuotientMap_iff_isClosed.mp hq).2 _ |>.mpr
  rw [CellularTelescopeAdjunction.preimage_level_image c S]
  have htime : Continuous (fun z : Cylinder X ↦ z.2.2) :=
    continuous_sigma fun _ ↦ continuous_snd
  have hbottom : Continuous (fun z : Cylinder X ↦ (⟨z.1, z.2.1⟩ : Σ n, X n)) :=
    continuous_sigma fun _ ↦ continuous_sigmaMk.comp continuous_fst
  have htop : Continuous
      (fun z : Cylinder X ↦ (⟨z.1 + 1, c z.1 z.2.1⟩ : Σ n, X n)) :=
    continuous_sigma fun n ↦ continuous_sigmaMk.comp ((c n).continuous.comp continuous_fst)
  have h0 : IsClosed {z : Cylinder X | z.2.2 = 0} :=
    isClosed_eq htime continuous_const
  have h1 : IsClosed {z : Cylinder X | z.2.2 = 1} :=
    isClosed_eq htime continuous_const
  exact (h0.inter (hS.preimage hbottom)).union (h1.inter (hS.preimage htop))


/-- The level coproduct has its original topology as a closed subspace of the
mapping telescope. Source: Fritsch–Piccinini A.4.8(ii), p.260, level-inclusion
topology guard. Its map is continuous on each summand, is injective by the
endpoint equivalence calculation, and takes closed sets to closed sets by the
explicit quotient-preimage calculation. The closed embedding criterion applies
without any injectivity assumption on the bonding maps. -/
theorem CellularTelescopeAdjunction.levels_isClosedEmbedding
    {X : ℕ → Type*} [∀ n, TopologicalSpace (X n)]
    (c : ∀ n, C(X n, X (n + 1))) :
    Topology.IsClosedEmbedding (fun z : Σ n, X n ↦ level c z.1 z.2) := by
  exact .of_continuous_injective_isClosedMap
    (continuous_sigma fun n ↦ (level c n).continuous)
    (CellularTelescopeAdjunction.levels_injective c)
    (CellularTelescopeAdjunction.levels_isClosedMap c)


/-- The closure of a level open cell is its original closed-cell image.
Source: Fritsch–Piccinini Theorem 2.3.1, pp.62–63, specialized to the unchanged
cells in the level coproduct. The individual level inclusion is the composite
of the closed summand embedding with the closed level-coproduct embedding.
It therefore commutes with closure; in the original Hausdorff CW complex the
closure of an open cell is its closed cell. This argument requires no separation
assumption on the telescope and makes no regular-cell assumption. -/
theorem CellularTelescopeAdjunction.level_cell_closure
    {X : ℕ → Type*} [∀ n, TopologicalSpace (X n)] [∀ n, T2Space (X n)]
    [∀ n, Topology.CWComplex (Set.univ : Set (X n))]
    (c : ∀ n, C(X n, X (n + 1))) (n d : ℕ)
    (e : Topology.CWComplex.cell (Set.univ : Set (X n)) d) :
    closure (level c n '' Topology.CWComplex.openCell (C := Set.univ) d e) =
      level c n '' Topology.CWComplex.closedCell (C := Set.univ) d e := by
  have hlevel : Topology.IsClosedEmbedding (level c n) :=
    (CellularTelescopeAdjunction.levels_isClosedEmbedding c).comp
      (Topology.IsClosedEmbedding.sigmaMk (i := n))
  rw [hlevel.closure_image_eq, Topology.RelCWComplex.closure_openCell_eq_closedCell]


/-- Finite frontier control transfers from a source cell to its telescope level
copy. Source: the finite-frontier clause of the source CW complex, together
with the level inclusion. The inclusion preserves the finite indexing family
and sends every frontier point into the corresponding lower-dimensional level
closed cell; this is the lower-frontier input for the telescope CW structure. -/
theorem CellularTelescopeAdjunction.level_cell_frontier_subset_finite_closedCell
    {X : ℕ → Type*} [∀ n, TopologicalSpace (X n)] [∀ n, T2Space (X n)]
    [∀ n, Topology.CWComplex (Set.univ : Set (X n))]
    (c : ∀ n, C(X n, X (n + 1))) (n d : ℕ)
    (e : Topology.CWComplex.cell (Set.univ : Set (X n)) d) :
    ∃ I : Π m, Finset (Topology.CWComplex.cell (Set.univ : Set (X n)) m),
      level c n '' Topology.CWComplex.cellFrontier (C := Set.univ) d e ⊆
        ⋃ (m < d) (j ∈ I m),
          level c n '' Topology.CWComplex.closedCell (C := Set.univ) m j := by
  obtain ⟨I, hI⟩ :=
    Topology.CWComplex.cellFrontier_subset_finite_closedCell (C := (Set.univ : Set (X n))) d e
  refine ⟨I, ?_⟩
  rintro y ⟨x, hx, rfl⟩
  have hx' : x ∈ ⋃ (m < d) (j ∈ I m),
      Topology.CWComplex.closedCell (C := Set.univ) m j := hI hx
  rcases Set.mem_iUnion.mp hx' with ⟨m, hx'⟩
  rcases Set.mem_iUnion.mp hx' with ⟨hm, hx'⟩
  rcases Set.mem_iUnion.mp hx' with ⟨j, hx'⟩
  rcases Set.mem_iUnion.mp hx' with ⟨hj, hx'⟩
  exact Set.mem_iUnion.mpr ⟨m, Set.mem_iUnion.mpr ⟨hm,
    Set.mem_iUnion.mpr ⟨j, Set.mem_iUnion.mpr ⟨hj, ⟨x, hx', rfl⟩⟩⟩⟩⟩


/-- The lateral face of a prism is covered by finitely many lower-dimensional
closed prism images in the original telescope. Source: Fritsch–Piccinini
Theorem 2.3.1, pp.62–63, with the source CW finite-frontier field.
Choose the finite lower-cell frontier cover in the source, take its product
with the whole interval, and pass to the cylinder image. Each covering prism
has dimension `m + 1 < d + 1`. The argument includes both endpoint faces of
the lateral part and remains valid when the top bonding map is noninjective. -/
theorem CellularTelescopeAdjunction.prism_lateral_subset_finite_closedPrisms
    {X : ℕ → Type*} [∀ n, TopologicalSpace (X n)]
    [∀ n, Topology.CWComplex (Set.univ : Set (X n))]
    (c : ∀ n, C(X n, X (n + 1))) (n d : ℕ)
    (e : Topology.CWComplex.cell (Set.univ : Set (X n)) d) :
    ∃ I : Π m, Finset (Topology.CWComplex.cell (Set.univ : Set (X n)) m),
      cylinder c n '' ((Topology.CWComplex.cellFrontier (C := Set.univ) d e).prod
        (Set.univ : Set unitInterval)) ⊆
      ⋃ (m : ℕ) (_ : m + 1 < d + 1) (j ∈ I m),
        cylinder c n '' ((Topology.CWComplex.closedCell (C := Set.univ) m j).prod
          (Set.univ : Set unitInterval)) := by
  obtain ⟨I, hI⟩ :=
    Topology.CWComplex.cellFrontier_subset_finite_closedCell (C := (Set.univ : Set (X n))) d e
  refine ⟨I, ?_⟩
  rintro y ⟨⟨x, t⟩, hx, rfl⟩
  have hx' : x ∈ ⋃ (m < d) (j ∈ I m),
      Topology.CWComplex.closedCell (C := Set.univ) m j := hI hx.1
  rcases Set.mem_iUnion.mp hx' with ⟨m, hx'⟩
  rcases Set.mem_iUnion.mp hx' with ⟨hm, hx'⟩
  rcases Set.mem_iUnion.mp hx' with ⟨j, hx'⟩
  rcases Set.mem_iUnion.mp hx' with ⟨hj, hx'⟩
  exact Set.mem_iUnion.mpr ⟨m, Set.mem_iUnion.mpr ⟨Nat.add_lt_add_right hm 1,
    Set.mem_iUnion.mpr ⟨j, Set.mem_iUnion.mpr ⟨hj, ⟨(x, t), ⟨hx', hx.2⟩, rfl⟩⟩⟩⟩⟩


/-- The prism boundary image splits into its bottom, bonded top, and lateral
faces in the original telescope quotient. Source: Fritsch–Piccinini Theorem
2.3.1, pp.62–63, specialized to the cylinder attachment. At time zero the
cylinder is the original level inclusion; at time one the quotient seam is
exactly the next level after the supplied bond. Taking images commutes with
the union of endpoint and lateral faces. No regularity or bond injectivity
is used, so the formula retains all possible top-face identifications. -/
theorem CellularTelescopeAdjunction.prism_boundary_image
    {X : ℕ → Type*} [∀ n, TopologicalSpace (X n)]
    [∀ n, Topology.CWComplex (Set.univ : Set (X n))]
    (c : ∀ n, C(X n, X (n + 1))) (n d : ℕ)
    (e : Topology.CWComplex.cell (Set.univ : Set (X n)) d) :
    cylinder c n ''
        (((Topology.CWComplex.closedCell (C := Set.univ) d e).prod
            {t : unitInterval | t = 0 ∨ t = 1}) ∪
          ((Topology.CWComplex.cellFrontier (C := Set.univ) d e).prod
            (Set.univ : Set unitInterval))) =
      (level c n '' Topology.CWComplex.closedCell (C := Set.univ) d e ∪
        level c (n + 1) '' (c n '' Topology.CWComplex.closedCell (C := Set.univ) d e)) ∪
      cylinder c n '' ((Topology.CWComplex.cellFrontier (C := Set.univ) d e).prod
        (Set.univ : Set unitInterval)) := by
  rw [Set.image_union]
  congr 1
  ext y
  constructor
  · rintro ⟨⟨x, t⟩, ⟨hx, ht⟩, rfl⟩
    rcases ht with rfl | rfl
    · exact Or.inl ⟨x, hx, rfl⟩
    · exact Or.inr ⟨c n x, ⟨x, hx, rfl⟩, (levelTop_eq c n x).symm⟩
  · rintro (⟨x, hx, rfl⟩ | ⟨z, ⟨x, hx, rfl⟩, rfl⟩)
    · exact ⟨(x, 0), ⟨hx, Or.inl rfl⟩, rfl⟩
    · exact ⟨(x, 1), ⟨hx, Or.inr rfl⟩, levelTop_eq c n x⟩


/-- The bonded top of each closed prism is covered by finitely many receiving
level closed cells of dimension at most the source cell dimension.
Source: Hatcher, Proposition A.1, p.520 (finitely many open cells meeting a
compact set), and Fritsch–Piccinini Theorem 2.3.1, pp.62–63 (cellular attachment).
The bonded closed cell is compact. Take its finite set of meeting open cells
and retain only dimensions at most `d`. Cellularity places the whole image
in the receiving `d`-skeleton, whose open-cell decomposition proves that this
filtered finite family still covers it. Enlarge those open cells to closed
cells and apply the receiving level inclusion. Thus the dimension bound comes
from cellularity, not from an unbounded finite-subcomplex cover. -/
theorem CellularTelescopeAdjunction.prism_top_subset_finite_level_cells
    {X : ℕ → Type*} [∀ n, TopologicalSpace (X n)] [∀ n, T2Space (X n)]
    [∀ n, Topology.CWComplex (Set.univ : Set (X n))]
    (c : ∀ n, C(X n, X (n + 1)))
    (hc : ∀ n d : ℕ, Set.MapsTo (c n)
      (Topology.CWComplex.skeleton (Set.univ : Set (X n)) d : Set (X n))
      (Topology.CWComplex.skeleton (Set.univ : Set (X (n + 1))) d : Set (X (n + 1))))
    (n d : ℕ) (e : Topology.CWComplex.cell (Set.univ : Set (X n)) d) :
    ∃ I : Finset (Σ m, Topology.CWComplex.cell (Set.univ : Set (X (n + 1))) m),
      (∀ a ∈ I, a.1 ≤ d) ∧
      level c (n + 1) '' (c n '' Topology.CWComplex.closedCell (C := Set.univ) d e) ⊆
        ⋃ a ∈ I, level c (n + 1) ''
          Topology.CWComplex.closedCell (C := Set.univ) a.1 a.2 := by
  classical
  let K := c n '' Topology.CWComplex.closedCell (C := Set.univ) d e
  have hK : IsCompact K :=
    Topology.CWComplex.isCompact_closedCell.image (c n).continuous
  have hfin := (HolomorphicAnosov.Topology.compact_cw_subset_finite_subcomplex K hK).1
  let I := hfin.toFinset.filter (fun a ↦ a.1 ≤ d)
  refine ⟨I, ?_, ?_⟩
  · intro a ha
    exact (Finset.mem_filter.mp ha).2
  · rintro y ⟨z, hz, rfl⟩
    have hzsk : z ∈ Topology.CWComplex.skeleton (Set.univ : Set (X (n + 1))) d := by
      rcases hz with ⟨x, hx, rfl⟩
      exact hc n d (Topology.CWComplex.closedCell_subset_skeleton d e hx)
    obtain ⟨m, hm, j, hzj⟩ := Topology.CWComplex.mem_skeleton_iff.mp hzsk
    have hmd : m ≤ d := by exact_mod_cast hm
    have ha : (⟨m, j⟩ : Σ m, Topology.CWComplex.cell (Set.univ : Set (X (n + 1))) m) ∈ I :=
      Finset.mem_filter.mpr ⟨hfin.mem_toFinset.mpr ⟨z, hz, hzj⟩, hmd⟩
    exact Set.mem_iUnion.mpr ⟨⟨m, j⟩, Set.mem_iUnion.mpr ⟨ha,
      ⟨z, Topology.CWComplex.openCell_subset_closedCell m j hzj, rfl⟩⟩⟩


/-- A whole prism boundary has a finite cover by lower-dimensional level and
prism images. Source: Fritsch–Piccinini Theorem 2.3.1, pp.62–63, and Hatcher
Proposition A.1, p.520. The bottom is the single original level closed cell.
For the top use the finite receiving-cell cover with dimension at most `d`.
For the lateral face package the source frontier cover over `m < d` into one
finite sigma-index set. The corresponding prisms have dimension `m + 1`,
strictly less than `d + 1`; the level dimensions are also strictly smaller.
Combine these covers using the exact three-face boundary-image identity. -/
theorem CellularTelescopeAdjunction.prism_boundary_subset_finite_cells
    {X : ℕ → Type*} [∀ n, TopologicalSpace (X n)] [∀ n, T2Space (X n)]
    [∀ n, Topology.CWComplex (Set.univ : Set (X n))]
    (c : ∀ n, C(X n, X (n + 1)))
    (hc : ∀ n d : ℕ, Set.MapsTo (c n)
      (Topology.CWComplex.skeleton (Set.univ : Set (X n)) d : Set (X n))
      (Topology.CWComplex.skeleton (Set.univ : Set (X (n + 1))) d : Set (X (n + 1))))
    (n d : ℕ) (e : Topology.CWComplex.cell (Set.univ : Set (X n)) d) :
    ∃ (I : Finset (Σ m, Topology.CWComplex.cell (Set.univ : Set (X (n + 1))) m))
      (J : Finset (Σ m, Topology.CWComplex.cell (Set.univ : Set (X n)) m)),
      (∀ a ∈ I, a.1 < d + 1) ∧ (∀ a ∈ J, a.1 + 1 < d + 1) ∧
      cylinder c n ''
        (((Topology.CWComplex.closedCell (C := Set.univ) d e).prod
            {t : unitInterval | t = 0 ∨ t = 1}) ∪
          ((Topology.CWComplex.cellFrontier (C := Set.univ) d e).prod
            (Set.univ : Set unitInterval))) ⊆
      (level c n '' Topology.CWComplex.closedCell (C := Set.univ) d e ∪
        ⋃ a ∈ I, level c (n + 1) ''
          Topology.CWComplex.closedCell (C := Set.univ) a.1 a.2) ∪
        ⋃ a ∈ J, cylinder c n ''
          ((Topology.CWComplex.closedCell (C := Set.univ) a.1 a.2).prod
            (Set.univ : Set unitInterval)) := by
  classical
  obtain ⟨I, hIdim, hI⟩ :=
    CellularTelescopeAdjunction.prism_top_subset_finite_level_cells c hc n d e
  obtain ⟨F, hF⟩ :=
    CellularTelescopeAdjunction.prism_lateral_subset_finite_closedPrisms c n d e
  let J := (Finset.range d).sigma F
  refine ⟨I, J, fun a ha ↦ Nat.lt_succ_of_le (hIdim a ha), ?_, ?_⟩
  · intro a ha
    exact Nat.add_lt_add_right (Finset.mem_range.mp (Finset.mem_sigma.mp ha).1) 1
  · rw [CellularTelescopeAdjunction.prism_boundary_image c n d e]
    apply Set.union_subset_union (Set.union_subset_union_right _ hI)
    intro y hy
    obtain ⟨m, hm, j, hj, hyj⟩ := by
      simpa only [Set.mem_iUnion, exists_prop] using hF hy
    have hjJ : (⟨m, j⟩ : Σ m, Topology.CWComplex.cell (Set.univ : Set (X n)) m) ∈ J :=
      Finset.mem_sigma.mpr ⟨Finset.mem_range.mpr (Nat.lt_of_add_lt_add_right hm), hj⟩
    exact Set.mem_iUnion.mpr ⟨⟨m, j⟩, Set.mem_iUnion.mpr ⟨hjJ, hyj⟩⟩


/-- The native cylinder interior region is open in the coproduct cylinder.
Source: Fritsch–Piccinini Theorem 2.3.1 pp.62–63; the open prism uses the open
interval after removing both endpoint slices. -/
theorem CellularTelescopeAdjunction.cylinder_interiors_isOpen
    {X : ℕ → Type u} [∀ n, TopologicalSpace (X n)] :
    IsOpen {z : MappingTelescope.Sequence.Cylinder X |
      z.2.2 ≠ 0 ∧ z.2.2 ≠ 1} := by
  have htime : Continuous
      (fun z : MappingTelescope.Sequence.Cylinder X ↦ z.2.2) :=
    continuous_sigma fun _ ↦ continuous_snd
  have hopen0 : IsOpen {t : unitInterval | t ≠ 0} := by
    exact isOpen_compl_iff.mpr (isClosed_singleton : IsClosed ({0} : Set unitInterval))
  have hopen1 : IsOpen {t : unitInterval | t ≠ 1} := by
    exact isOpen_compl_iff.mpr (isClosed_singleton : IsClosed ({1} : Set unitInterval))
  have h0 : IsOpen {z : MappingTelescope.Sequence.Cylinder X | z.2.2 ≠ 0} :=
    hopen0.preimage htime
  have h1 : IsOpen {z : MappingTelescope.Sequence.Cylinder X | z.2.2 ≠ 1} :=
    hopen1.preimage htime
  exact h0.inter h1


/-- The endpoint attachment remains continuous on the original level-d endpoint
subspace. Source: Fritsch–Piccinini Theorem 2.3.1 pp.62–63; restriction to a
closed skeletal endpoint carrier is by the native subtype topology. -/
theorem CellularTelescopeAdjunction.attach_skeleton_continuous
    {X : ℕ → Type u} [∀ n, TopologicalSpace (X n)]
    [∀ n, T2Space (X n)] [∀ n, Topology.CWComplex (Set.univ : Set (X n))]
    (c : ∀ n, C(X n, X (n + 1))) (d : ℕ) :
    Continuous (fun z : {z : CellularTelescopeAdjunction.endpoints X //
      z.val.2.1 ∈ Topology.CWComplex.skeleton
        (Set.univ : Set (X z.val.1)) d} ↦
      CellularTelescopeAdjunction.attach c z.1) := by
  exact (CellularTelescopeAdjunction.attach_continuous c).comp continuous_subtype_val


/-- The skeletal endpoint attachment maps the native endpoint-skeleton subtype
into the corresponding summand skeleton. Source: Fritsch–Piccinini Theorem
2.3.1, pp.62–63, in the `Set.MapsTo` form used by cellular subcomplex maps. -/
theorem CellularTelescopeAdjunction.attach_skeleton_mapsTo
    {X : ℕ → Type u} [∀ n, TopologicalSpace (X n)]
    [∀ n, T2Space (X n)] [∀ n, Topology.CWComplex (Set.univ : Set (X n))]
    (c : ∀ n, C(X n, X (n + 1)))
    (hc : ∀ n d : ℕ, Set.MapsTo (c n)
      (Topology.CWComplex.skeleton (Set.univ : Set (X n)) d : Set (X n))
      (Topology.CWComplex.skeleton (Set.univ : Set (X (n + 1))) d : Set (X (n + 1))))
    (d : ℕ) :
    Set.MapsTo
      (fun z : {z : CellularTelescopeAdjunction.endpoints X //
        z.val.2.1 ∈ Topology.CWComplex.skeleton
          (Set.univ : Set (X z.val.1)) d} ↦
        CellularTelescopeAdjunction.attach c z.1)
      Set.univ
      {p : (Σ n, X n) |
        p.2 ∈ Topology.CWComplex.skeleton (Set.univ : Set (X p.1)) d} := by
  intro z hz
  exact CellularTelescopeAdjunction.attach_mapsTo_summand_skeleton c hc d z.1 z.2


/-- The endpoint-skeleton carrier is closed in the native endpoint subspace.
Source: Fritsch–Piccinini Theorem 2.3.1, pp.62–63; closedness is inherited from
the source CW skeleton and the endpoint subspace topology. -/
theorem CellularTelescopeAdjunction.endpoint_skeleton_isClosed
    {X : ℕ → Type u} [∀ n, TopologicalSpace (X n)]
    [∀ n, T2Space (X n)] [∀ n, Topology.CWComplex (Set.univ : Set (X n))]
    (d : ℕ) :
    IsClosed {z : CellularTelescopeAdjunction.endpoints X |
      z.val.2.1 ∈ Topology.CWComplex.skeleton
        (Set.univ : Set (X z.val.1)) d} := by
  have hRaw : Continuous
      (fun z : MappingTelescope.Sequence.Cylinder X ↦
        (⟨z.1, z.2.1⟩ : Σ n, X n)) := by
    apply continuous_sigma
    intro n
    exact (continuous_sigmaMk (σ := X) (i := n)).comp continuous_fst
  have h : Continuous
      (fun z : CellularTelescopeAdjunction.endpoints X ↦
        (⟨z.val.1, z.val.2.1⟩ : Σ n, X n)) :=
    hRaw.comp continuous_subtype_val
  have hclosed : IsClosed {p : (Σ n, X n) |
      p.2 ∈ Topology.CWComplex.skeleton (Set.univ : Set (X p.1)) d} := by
    apply isClosed_sigma_iff.mpr
    intro n
    exact (Topology.CWComplex.skeleton (Set.univ : Set (X n)) d).closed
  exact IsClosed.preimage h hclosed


/-- The dependent sigma union of source level-d skeletons is closed in the
native coproduct. Source: Fritsch–Piccinini Proposition 2.2.1 p.57, with the
source CW skeleton closed-set criterion applied summandwise. -/
theorem CellularTelescopeAdjunction.summand_skeleton_isClosed
    {X : ℕ → Type u} [∀ n, TopologicalSpace (X n)]
    [∀ n, T2Space (X n)] [∀ n, Topology.CWComplex (Set.univ : Set (X n))]
    (d : ℕ) :
    IsClosed {p : (Σ n, X n) |
      p.2 ∈ Topology.CWComplex.skeleton (Set.univ : Set (X p.1)) d} := by
  apply isClosed_sigma_iff.mpr
  intro n
  exact (Topology.CWComplex.skeleton (Set.univ : Set (X n)) d).closed


/-- The explicit adjunction/telescope homeomorphism has continuous forward map.
Source: Fritsch–Piccinini Appendix A.4, pp.258–259, via the original quotient
topologies in the comparison construction. -/
theorem CellularTelescopeAdjunction.homeomorph_continuous_toFun
    {X : ℕ → Type*} [∀ n, TopologicalSpace (X n)]
    (c : ∀ n, C(X n, X (n + 1))) :
    Continuous (CellularTelescopeAdjunction.homeomorph c) := by
  exact (CellularTelescopeAdjunction.homeomorph c).continuous_toFun


/-- The explicit adjunction/telescope homeomorphism has continuous inverse map.
Source: Fritsch–Piccinini Appendix A.4, pp.258–259, via the original quotient
topologies in the comparison construction. -/
theorem CellularTelescopeAdjunction.homeomorph_continuous_invFun
    {X : ℕ → Type*} [∀ n, TopologicalSpace (X n)]
    (c : ∀ n, C(X n, X (n + 1))) :
    Continuous ((CellularTelescopeAdjunction.homeomorph c).symm) := by
  exact (CellularTelescopeAdjunction.homeomorph c).continuous_invFun


/-- The inverse comparison homeomorphism sends an original cylinder point to
its ordinary-adjunction cylinder class. Source: the explicit comparison step
in Fritsch–Piccinini Theorem 2.3.1, pp.62–63. -/
theorem CellularTelescopeAdjunction.homeomorph_invFun_cylinder
    {X : ℕ → Type*} [∀ n, TopologicalSpace (X n)]
    (c : ∀ n, C(X n, X (n + 1))) (n : ℕ) (z : X n × unitInterval) :
    (CellularTelescopeAdjunction.homeomorph c).symm
        (MappingTelescope.Sequence.cylinder c n z) =
      Quot.mk (CellularTelescopeAdjunction.relation c)
        (Sum.inr ⟨n, z⟩) := rfl


/-- The inverse comparison homeomorphism sends an original level point to its
bottom cylinder class in the ordinary adjunction. Source: the endpoint
comparison in Fritsch–Piccinini Theorem 2.3.1, pp.62–63. -/
theorem CellularTelescopeAdjunction.homeomorph_invFun_level
    {X : ℕ → Type*} [∀ n, TopologicalSpace (X n)]
    (c : ∀ n, C(X n, X (n + 1))) (n : ℕ) (x : X n) :
    (CellularTelescopeAdjunction.homeomorph c).symm
        (MappingTelescope.Sequence.level c n x) =
      Quot.mk (CellularTelescopeAdjunction.relation c)
        (Sum.inr ⟨n, (x, 0)⟩) := rfl


/-- The native coproduct inclusion of one level into the raw adjunction carrier.
Source: Fritsch–Piccinini Proposition 2.2.1 p.57. It uses the original sigma
topology and makes no quotient or CW assertion. -/
def CellularTelescopeAdjunction.levelRaw
    {X : ℕ → Type*} [∀ n, TopologicalSpace (X n)] (n : ℕ) : X n →
      (Σ m, X m) ⊕ MappingTelescope.Sequence.Cylinder X :=
  fun x ↦ Sum.inl ⟨n, x⟩

theorem CellularTelescopeAdjunction.levelRaw_continuous
    {X : ℕ → Type*} [∀ n, TopologicalSpace (X n)] (n : ℕ) :
    Continuous (CellularTelescopeAdjunction.levelRaw n (X := X)) :=
  continuous_inl.comp (continuous_sigmaMk (σ := X) (i := n))

/-- The level inclusion preserves the original source skeleton predicate.
Source: Fritsch–Piccinini Proposition 2.2.1 and Theorem 2.3.1 pp.57,62–63. -/
theorem CellularTelescopeAdjunction.levelRaw_mapsTo_summand_skeleton
    {X : ℕ → Type*} [∀ n, TopologicalSpace (X n)]
    [∀ n, T2Space (X n)] [∀ n, Topology.CWComplex (Set.univ : Set (X n))]
    (n d : ℕ) :
    Set.MapsTo (CellularTelescopeAdjunction.levelRaw n (X := X))
      (Topology.CWComplex.skeleton (Set.univ : Set (X n)) d : Set (X n))
      {p : (Σ m, X m) ⊕ MappingTelescope.Sequence.Cylinder X |
        ∃ k, ∃ x : X k, p = Sum.inl ⟨k, x⟩ ∧
          x ∈ Topology.CWComplex.skeleton (Set.univ : Set (X k)) d} := by
  intro x hx
  exact ⟨n, x, rfl, hx⟩


/-- The raw level summand and the bottom of its cylinder represent the same
quotient point. Source: Fritsch–Piccinini Appendix A.4, pp.258–259, specialized
to the endpoint adjunction used in Theorem 2.3.1. -/
theorem CellularTelescopeAdjunction.levelRaw_quotient_bottom
    {X : ℕ → Type*} [∀ n, TopologicalSpace (X n)]
    (c : ∀ n, C(X n, X (n + 1))) (n : ℕ) (x : X n) :
    Quot.mk (CellularTelescopeAdjunction.relation c) (Sum.inl ⟨n, x⟩) =
      Quot.mk (CellularTelescopeAdjunction.relation c)
        (Sum.inr ⟨n, (x, 0)⟩) := by
  exact (local_bottom_identification c n x).symm

/-- The raw receiving level and the top of the preceding cylinder represent
the same quotient point. Source: Fritsch–Piccinini Appendix A.4, pp.258–259,
specialized to the endpoint adjunction used in Theorem 2.3.1. -/
theorem CellularTelescopeAdjunction.levelRaw_quotient_top
    {X : ℕ → Type*} [∀ n, TopologicalSpace (X n)]
    (c : ∀ n, C(X n, X (n + 1))) (n : ℕ) (x : X n) :
    Quot.mk (CellularTelescopeAdjunction.relation c)
        (Sum.inl ⟨n + 1, c n x⟩) =
      Quot.mk (CellularTelescopeAdjunction.relation c)
        (Sum.inr ⟨n, (x, 1)⟩) := by
  exact (local_top_identification c n x).symm


/-- Closed subsets of the ordinary adjunction quotient are detected on the raw
coproduct. Source: Fritsch–Piccinini Appendix A.4, pp.258–259, whose adjunction
topology is the coinduced quotient topology. -/
theorem CellularTelescopeAdjunction.quotient_isClosed_iff
    {X : Type*} [TopologicalSpace X] {r : X → X → Prop}
    (s : Set (Quot r)) :
    IsClosed s ↔ IsClosed ((Quot.mk r) ⁻¹' s) := by
  exact (Topology.isQuotientMap_iff_isClosed.mp isQuotientMap_quot_mk).2 s


/-- A map out of the ordinary adjunction quotient is continuous exactly when
its pullback to the raw coproduct is continuous. Source: Fritsch–Piccinini
Appendix A.4, pp.258–259, by the defining final topology. -/
theorem CellularTelescopeAdjunction.quotient_continuous_iff
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {r : X → X → Prop} (g : Quot r → Y) :
    Continuous g ↔ Continuous (g ∘ Quot.mk r) := by
  exact isQuotientMap_quot_mk.continuous_iff


/-- The explicit comparison map from the original telescope into the ordinary
adjunction quotient is continuous. Source: Fritsch–Piccinini Appendix A.4,
pp.258–259, by quotient descent from the cylinder summand. -/
theorem CellularTelescopeAdjunction.fromTelescope_continuous
    {X : ℕ → Type*} [∀ n, TopologicalSpace (X n)]
    (c : ∀ n, C(X n, X (n + 1))) :
    Continuous (CellularTelescopeAdjunction.fromTelescope c) := by
  exact (continuous_quot_mk.comp continuous_inr).quotient_lift
    (local_cylinder_respects c)


/-- The explicit comparison map from the ordinary adjunction quotient to the
original telescope is continuous. Source: Fritsch–Piccinini Appendix A.4,
pp.258–259, by quotient descent from the level and cylinder summands. -/
theorem CellularTelescopeAdjunction.toTelescope_continuous
    {X : ℕ → Type*} [∀ n, TopologicalSpace (X n)]
    (c : ∀ n, C(X n, X (n + 1))) :
    Continuous (CellularTelescopeAdjunction.toTelescope c) := by
  exact continuous_quot_lift _
    ((continuous_sigma fun n ↦ (level c n).continuous).sumElim (quotient c).continuous)


/-- On a cylinder representative, the adjunction-to-telescope comparison is
the original cylinder quotient map. Source: the explicit comparison step in
Fritsch–Piccinini Theorem 2.3.1, pp.62–63. -/
theorem CellularTelescopeAdjunction.toTelescope_cylinder
    {X : ℕ → Type*} [∀ n, TopologicalSpace (X n)]
    (c : ∀ n, C(X n, X (n + 1))) (n : ℕ) (z : X n × unitInterval) :
    CellularTelescopeAdjunction.toTelescope c
        (Quot.mk (CellularTelescopeAdjunction.relation c)
          (Sum.inr ⟨n, z⟩)) =
      MappingTelescope.Sequence.cylinder c n z := rfl


/-- On a level representative, the adjunction-to-telescope comparison is the
original bottom-level map. Source: the explicit comparison step in
Fritsch–Piccinini Theorem 2.3.1, pp.62–63. -/
theorem CellularTelescopeAdjunction.toTelescope_level
    {X : ℕ → Type*} [∀ n, TopologicalSpace (X n)]
    (c : ∀ n, C(X n, X (n + 1))) (n : ℕ) (x : X n) :
    CellularTelescopeAdjunction.toTelescope c
        (Quot.mk (CellularTelescopeAdjunction.relation c)
          (Sum.inl ⟨n, x⟩)) =
      MappingTelescope.Sequence.level c n x := rfl


/-- The telescope-to-adjunction comparison sends an original cylinder quotient
representative to the corresponding raw cylinder class. Source: the explicit
comparison step in Fritsch–Piccinini Theorem 2.3.1, pp.62–63. -/
theorem CellularTelescopeAdjunction.fromTelescope_cylinder
    {X : ℕ → Type*} [∀ n, TopologicalSpace (X n)]
    (c : ∀ n, C(X n, X (n + 1))) (z : MappingTelescope.Sequence.Cylinder X) :
    CellularTelescopeAdjunction.fromTelescope c
        (MappingTelescope.Sequence.quotient c z) =
      Quot.mk (CellularTelescopeAdjunction.relation c) (Sum.inr z) := rfl


/-- The telescope-to-adjunction comparison sends a canonical level point to
the bottom cylinder representative of that level. Source: the endpoint
comparison in Fritsch–Piccinini Theorem 2.3.1, pp.62–63. -/
theorem CellularTelescopeAdjunction.fromTelescope_level
    {X : ℕ → Type*} [∀ n, TopologicalSpace (X n)]
    (c : ∀ n, C(X n, X (n + 1))) (n : ℕ) (x : X n) :
    CellularTelescopeAdjunction.fromTelescope c
        (MappingTelescope.Sequence.level c n x) =
      Quot.mk (CellularTelescopeAdjunction.relation c)
        (Sum.inr ⟨n, (x, 0)⟩) := rfl



open Set in
private theorem telescope_transport_characteristic
    {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]
    {d : ℕ} (e : PartialEquiv (Fin d → ℝ) A)
    (hs : e.source = Metric.ball 0 1)
    (he : ContinuousOn e (Metric.closedBall 0 1))
    (hi : ContinuousOn e.symm e.target)
    (f : A → B) (hf : Continuous f)
    (hemb : Topology.IsEmbedding (fun y : e.target ↦ f y)) :
    ∃ p : PartialEquiv (Fin d → ℝ) B,
      p.source = Metric.ball 0 1 ∧
      (∀ z, p z = f (e z)) ∧
      ContinuousOn p (Metric.closedBall 0 1) ∧ ContinuousOn p.symm p.target := by
  classical
  let h : e.source ≃ₜ e.target := {
    toEquiv := e.toEquiv
    continuous_toFun := (continuousOn_iff_continuous_domRestrict.mp
      (he.mono (hs ▸ Metric.ball_subset_closedBall))).subtype_mk _
    continuous_invFun := (continuousOn_iff_continuous_domRestrict.mp hi).subtype_mk _ }
  have hg : Topology.IsEmbedding (fun z : e.source ↦ f (e z)) :=
    hemb.comp h.isEmbedding
  have hinj : InjOn (fun z ↦ f (e z)) e.source := by
    intro x hx y hy hxy
    exact congrArg Subtype.val (hg.injective (a₁ := ⟨x, hx⟩) (a₂ := ⟨y, hy⟩) hxy)
  let p := hinj.toPartialEquiv (fun z ↦ f (e z)) e.source
  refine ⟨p, hs, fun _ ↦ rfl, hf.continuousOn.comp he (fun _ _ ↦ mem_univ _), ?_⟩
  have hr : p.target = (fun z : e.source ↦ f (e z)) '' univ := by
    ext y
    simp [p, Set.InjOn.toPartialEquiv, Set.BijOn.toPartialEquiv]
  rw [hr, hg.isInducing.continuousOn_image_iff]
  have heq : (p.symm ∘ (fun z : e.source ↦ f (e z))) = Subtype.val := by
    funext z
    exact p.left_inv z.property
  rw [heq]
  exact continuous_subtype_val.continuousOn

open Set in
private theorem telescope_prism_characteristic
    {A : Type*} [TopologicalSpace A] [Topology.CWComplex (univ : Set A)]
    (d : ℕ) (i : Topology.CWComplex.cell (univ : Set A) d) :
    ∃ e : PartialEquiv (Fin (d + 1) → ℝ) (A × unitInterval),
      e.source = Metric.ball 0 1 ∧
      e.target = (Topology.CWComplex.openCell (C := univ) d i).prod
        {t : unitInterval | (0 : ℝ) < t ∧ (t : ℝ) < 1} ∧
      e '' Metric.closedBall 0 1 =
        (Topology.CWComplex.closedCell (C := univ) d i).prod univ ∧
      e '' Metric.sphere 0 1 ⊆
        ((Topology.CWComplex.closedCell (C := univ) d i).prod
          {t : unitInterval | t = 0 ∨ t = 1}) ∪
        ((Topology.CWComplex.cellFrontier (C := univ) d i).prod univ) ∧
      ContinuousOn e (Metric.closedBall 0 1) ∧ ContinuousOn e.symm e.target := by
  obtain ⟨e, hs, ht, hf, he, hi⟩ := Topology.prism_partial_equiv_data d i
  obtain ⟨f, _, hfr, hfh, hft⟩ := Topology.prism_closed_disk_characteristic d i
  have hef (w : ↥(Metric.closedBall (0 : Fin (d + 1) → ℝ) 1)) : e w = f w := by
    apply Prod.ext
    · exact (hf w w.property).1.trans (hfh w).symm
    · apply Subtype.ext
      exact (hf w w.property).2.trans (hft w).symm
  have hclosed : e '' Metric.closedBall 0 1 =
      (Topology.CWComplex.closedCell (C := univ) d i).prod univ := by
    rw [← hfr]
    ext y
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact ⟨⟨w, hw⟩, (hef ⟨w, hw⟩).symm⟩
    · rintro ⟨w, rfl⟩
      exact ⟨w, w.property, hef w⟩
  refine ⟨e, hs, ht, hclosed, ?_, he, hi⟩
  rintro y ⟨w, hw, rfl⟩
  have hwc := Metric.sphere_subset_closedBall hw
  have hcw : ‖w‖ = 1 := by simpa using hw
  have hh : (fun j : Fin d ↦ w j.castSucc) ∈ Metric.closedBall 0 1 := by
    rw [Metric.mem_closedBall, dist_zero_right]
    exact (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)).mpr
      (fun j ↦ (norm_le_pi_norm w _).trans hcw.le)
  have himg : (e w).1 ∈ Topology.CWComplex.closedCell (C := univ) d i :=
    ⟨_, hh, (hf w hwc).1.symm⟩
  by_cases hend : (e w).2 = 0 ∨ (e w).2 = 1
  · exact Or.inl ⟨himg, hend⟩
  right
  refine ⟨⟨(fun j : Fin d ↦ w j.castSucc), ?_, (hf w hwc).1.symm⟩, mem_univ _⟩
  have htime : 0 < ((e w).2 : ℝ) ∧ ((e w).2 : ℝ) < 1 := by
    constructor
    · exact lt_of_le_of_ne (e w).2.property.1
        (fun h ↦ hend (Or.inl (Subtype.ext h.symm)))
    · exact lt_of_le_of_ne (e w).2.property.2
        (fun h ↦ hend (Or.inr (Subtype.ext h)))
  by_contra hns
  have hhn : ‖(fun j : Fin d ↦ w j.castSucc)‖ < 1 := by
    have hle : ‖(fun j : Fin d ↦ w j.castSucc)‖ ≤ 1 := by simpa using hh
    have hne : ‖(fun j : Fin d ↦ w j.castSucc)‖ ≠ 1 := by simpa using hns
    exact lt_of_le_of_ne hle hne
  have hwn : ‖w‖ < 1 := by
    apply (pi_norm_lt_iff (by norm_num : (0 : ℝ) < 1)).mpr
    intro j
    refine Fin.lastCases ?_ (fun k ↦ ?_) j
    · rw [Real.norm_eq_abs, abs_lt]
      have ht' := (hf w hwc).2
      constructor <;> linarith [htime.1, htime.2]
    · exact (norm_le_pi_norm (fun k : Fin d ↦ w k.castSucc) k).trans_lt hhn
  exact (lt_irrefl (1 : ℝ)) (hcw ▸ hwn)

/-!
# CW assembly for the original cellular mapping telescope

The geometric lemmas above supply the level and open-cylinder embeddings,
cell partition, and finite attaching-image covers. The construction below
packages their original quotient images directly into Mathlib's CW structure.
-/

/-- A cellular mapping telescope has the CW structure with precisely its level
cells and open prism cells, on the original quotient topology.

Source: Fritsch–Piccinini, *Cellular Structures in Topology*, Theorem 2.3.1,
pp.62–63 (cellular adjunction); Hatcher, *Algebraic Topology*, Appendix A.1,
p.520 (compact sets meet finitely many cells), and A.6, p.524 (ordinary
interval-product topology). The native coordinate and quotient-field packaging
below is an explicit formalization of the cell construction.

Proof: The coproduct of level spaces embeds as a closed subspace of the
original telescope. The quotient restricts to an open embedding on the
coproduct of cylinder interiors. Compose the original characteristic maps
with the level embeddings, and the native prism characteristic maps with
the cylinder maps. On their open targets these maps are embeddings, so their
original continuous inverses give continuous inverses onto the image. On the
closed native disks the maps remain continuous, including noninjective
original cell boundaries and noninjective bonding maps.

The prism characteristic map has head equal to the original characteristic
map and time equal to (last+1)/2 on its closed disk. Its closed image is the
closed source cell times the entire interval. A boundary vector has head on
the original sphere or last coordinate equal to minus or plus one; otherwise
all coordinates would have absolute value strictly less than one. Thus its
boundary maps into the lateral face or an endpoint face, including the
zero-dimensional head case.

For a level cell, transport the original finite lower-dimensional frontier
cover. For a prism over a d-cell, its bottom is the one corresponding level
closed cell. Its top is the image of that closed cell under the bonding map.
This is compact and contained in the receiving d-skeleton by cellularity;
the finite set of original open cells meeting it, restricted to dimensions
at most d, covers it by their closed cells. Its lateral face is covered by
prisms over the finite original frontier family, of dimensions at most d.
The resulting finite family therefore has dimension strictly less than d+1.
Package this finite sigma family degreewise to obtain the native frontier
field. No entire level is assumed compact or finite dimensional.

Level cells are pairwise disjoint by the level embedding and original cell
disjointness. Open prisms are pairwise disjoint by the interior embedding;
they are disjoint from levels because they have nonendpoint time. To cover
any telescope point, choose a cylinder representative. At the bottom use
its source open cell, at the top use the receiving open cell after the seam
identification, and at interior time use its source open prism.

Finally suppose A intersects each proposed closed cell in a closed set.
For each cylinder, pull back the closed intersection with each closed prism,
and intersect with its original closed-cell product. This is exactly the
intersection of the cylinder preimage of A with that closed-cell product.
The ordinary interval-product closed-set criterion makes each cylinder
preimage closed. The coproduct criterion and the original quotient criterion
then make A closed in the original telescope. Hence the weak topology field
does not introduce any replacement topology. The preceding maps and witnesses
form an unrestricted CWComplex whose indices are literally the indicated
level/prism sum; the label equivalences are identities. Empty levels, arbitrary
cell cardinalities, and unbounded dimensions are all permitted.

DAG node: `topo.cellular_mapping_telescope_cw_core_g7`.
-/
theorem cellular_mapping_telescope_cw_core
    {X : ℕ → Type*} [∀ n, TopologicalSpace (X n)] [∀ n, T2Space (X n)]
    [∀ n, Topology.CWComplex (Set.univ : Set (X n))]
    (c : ∀ n, C(X n, X (n + 1)))
    (hc : ∀ n d : ℕ, Set.MapsTo (c n)
      (Topology.CWComplex.skeleton (Set.univ : Set (X n)) d : Set (X n))
      (Topology.CWComplex.skeleton (Set.univ : Set (X (n + 1))) d : Set (X (n + 1)))) :
    ∃ cw : Topology.CWComplex (Set.univ : Set (telescope c)),
      letI : Topology.CWComplex (Set.univ : Set (telescope c)) := cw
      ∃ labels : ∀ d : ℕ,
        Topology.CWComplex.cell (Set.univ : Set (telescope c)) d ≃
          ((Σ n, Topology.CWComplex.cell (Set.univ : Set (X n)) d) ⊕
            (Σ m : {m : ℕ // m + 1 = d},
              Σ n, Topology.CWComplex.cell (Set.univ : Set (X n)) m.val)),
        (∀ (d n : ℕ) (e : Topology.CWComplex.cell (Set.univ : Set (X n)) d),
          Topology.CWComplex.openCell (C := (Set.univ : Set (telescope c))) d ((labels d).symm (Sum.inl ⟨n, e⟩)) =
            level c n '' Topology.CWComplex.openCell (C := (Set.univ : Set (X n))) d e) ∧
        (∀ (m d : ℕ) (h : m + 1 = d) (n : ℕ)
            (e : Topology.CWComplex.cell (Set.univ : Set (X n)) m),
          Topology.CWComplex.openCell (C := (Set.univ : Set (telescope c))) d ((labels d).symm (Sum.inr ⟨⟨m, h⟩, n, e⟩)) =
            cylinder c n ''
              ((Topology.CWComplex.openCell (C := (Set.univ : Set (X n))) m e).prod
                {t : unitInterval | (0 : ℝ) < (t : ℝ) ∧ (t : ℝ) < 1})) := by
  classical
  have hlevel (n : ℕ) : Topology.IsEmbedding (level c n) :=
    ((CellularTelescopeAdjunction.levels_isClosedEmbedding c).comp
      (Topology.IsClosedEmbedding.sigmaMk (i := n))).isEmbedding
  have ld (n d : ℕ) (i : Topology.CWComplex.cell (Set.univ : Set (X n)) d) :=
    telescope_transport_characteristic (Topology.CWComplex.map d i)
      (Topology.CWComplex.source_eq d i) (Topology.CWComplex.continuousOn d i)
      (Topology.CWComplex.continuousOn_symm d i)
      (level c n) (level c n).continuous ((hlevel n).comp .subtypeVal)
  choose L Ls Lf Lcont Linv using ld
  have ed (n d : ℕ) (i : Topology.CWComplex.cell (Set.univ : Set (X n)) d) :=
    telescope_prism_characteristic d i
  choose E Es Et Ec Eb Econt Einv using ed
  have pd (n d : ℕ) (i : Topology.CWComplex.cell (Set.univ : Set (X n)) d) :
      ∃ p : PartialEquiv (Fin (d + 1) → ℝ) (telescope c),
        p.source = Metric.ball 0 1 ∧ (∀ z, p z = cylinder c n (E n d i z)) ∧
        ContinuousOn p (Metric.closedBall 0 1) ∧ ContinuousOn p.symm p.target := by
    apply telescope_transport_characteristic (E n d i) (Es n d i) (Econt n d i)
      (Einv n d i) (cylinder c n) (cylinder c n).continuous
    have hint (y : (E n d i).target) : y.val.2 ≠ 0 ∧ y.val.2 ≠ 1 := by
      have hy : y.val ∈ (Topology.CWComplex.openCell (C := Set.univ) d i).prod
          {t : unitInterval | (0 : ℝ) < t ∧ (t : ℝ) < 1} :=
        (Et n d i) ▸ y.property
      constructor <;> intro h
      · simpa [h] using hy.2.1
      · simpa [h] using hy.2.2
    let f : (E n d i).target →
        {z : Cylinder X | z.2.2 ≠ 0 ∧ z.2.2 ≠ 1} :=
      fun y ↦ ⟨⟨n, y.val⟩, hint y⟩
    have hemb : Topology.IsEmbedding f :=
      Topology.IsEmbedding.subtypeVal.of_comp_iff.mp
        (Topology.IsEmbedding.sigmaMk.comp Topology.IsEmbedding.subtypeVal)
    exact (CellularTelescopeAdjunction.cylinderInteriors_isOpenEmbedding c).isEmbedding.comp hemb
  choose P Ps Pf Pcont Pinv using pd
  have Lo (n d : ℕ) (i : Topology.CWComplex.cell (Set.univ : Set (X n)) d) :
      L n d i '' Metric.ball 0 1 =
        level c n '' Topology.CWComplex.openCell (C := Set.univ) d i := by
    change (fun z ↦ L n d i z) '' _ = _
    simp_rw [Lf]
    exact Set.image_comp _ _ _
  have Lc (n d : ℕ) (i : Topology.CWComplex.cell (Set.univ : Set (X n)) d) :
      L n d i '' Metric.closedBall 0 1 =
        level c n '' Topology.CWComplex.closedCell (C := Set.univ) d i := by
    change (fun z ↦ L n d i z) '' _ = _
    simp_rw [Lf]
    exact Set.image_comp _ _ _
  have Po (n d : ℕ) (i : Topology.CWComplex.cell (Set.univ : Set (X n)) d) :
      P n d i '' Metric.ball 0 1 =
        cylinder c n '' ((Topology.CWComplex.openCell (C := Set.univ) d i).prod
          {t : unitInterval | (0 : ℝ) < t ∧ (t : ℝ) < 1}) := by
    change (fun z ↦ P n d i z) '' _ = _
    simp_rw [Pf]
    rw [← Set.image_image, ← Es, (E n d i).image_source_eq_target, Et]
  have Pc (n d : ℕ) (i : Topology.CWComplex.cell (Set.univ : Set (X n)) d) :
      P n d i '' Metric.closedBall 0 1 =
        cylinder c n '' ((Topology.CWComplex.closedCell (C := Set.univ) d i).prod
          (Set.univ : Set unitInterval)) := by
    change (fun z ↦ P n d i z) '' _ = _
    simp_rw [Pf]
    rw [← Set.image_image, Ec]
  let I (d : ℕ) :=
    ((Σ n, Topology.CWComplex.cell (Set.univ : Set (X n)) d) ⊕
      (Σ m : {m : ℕ // m + 1 = d},
        Σ n, Topology.CWComplex.cell (Set.univ : Set (X n)) m.val))
  let M (d : ℕ) (i : I d) : PartialEquiv (Fin d → ℝ) (telescope c) := by
    rcases i with ⟨n, i⟩ | ⟨⟨m, hm⟩, n, i⟩
    · exact L n d i
    · subst d
      exact P n m i
  have Mlevel (d n : ℕ) (i : Topology.CWComplex.cell (Set.univ : Set (X n)) d) :
      M d (Sum.inl ⟨n, i⟩) = L n d i := rfl
  have Mprism (d n : ℕ) (i : Topology.CWComplex.cell (Set.univ : Set (X n)) d) :
      M (d + 1) (Sum.inr ⟨⟨d, rfl⟩, n, i⟩) = P n d i := rfl
  have Msource (d : ℕ) (i : I d) : (M d i).source = Metric.ball 0 1 := by
    rcases i with ⟨n, i⟩ | ⟨⟨m, hm⟩, n, i⟩
    · exact Ls n d i
    · subst d
      exact Ps n m i
  have Mcont (d : ℕ) (i : I d) : ContinuousOn (M d i) (Metric.closedBall 0 1) := by
    rcases i with ⟨n, i⟩ | ⟨⟨m, hm⟩, n, i⟩
    · exact Lcont n d i
    · subst d
      exact Pcont n m i
  have Minv (d : ℕ) (i : I d) : ContinuousOn (M d i).symm (M d i).target := by
    rcases i with ⟨n, i⟩ | ⟨⟨m, hm⟩, n, i⟩
    · exact Linv n d i
    · subst d
      exact Pinv n m i
  have Mdisj : (Set.univ : Set (Σ d, I d)).PairwiseDisjoint
      (fun a ↦ M a.1 a.2 '' Metric.ball 0 1) := by
    intro a _ b _ hne
    rcases a with ⟨d, ⟨n, i⟩ | ⟨⟨m, hm⟩, n, i⟩⟩ <;>
      rcases b with ⟨k, ⟨l, j⟩ | ⟨⟨r, hr⟩, l, j⟩⟩
    · change Disjoint (L n d i '' _) (L l k j '' _)
      rw [Lo, Lo]
      apply CellularTelescopeAdjunction.level_cells_disjoint c i j
      intro heq
      cases heq
      exact hne rfl
    · subst k
      change Disjoint (L n d i '' _) (P l r j '' _)
      rw [Lo, Po]
      exact CellularTelescopeAdjunction.level_prism_cells_disjoint c n l d r i j
    · subst d
      change Disjoint (P n m i '' _) (L l k j '' _)
      rw [Po, Lo]
      exact (CellularTelescopeAdjunction.level_prism_cells_disjoint c l n k m j i).symm
    · subst d
      subst k
      change Disjoint (P n m i '' _) (P l r j '' _)
      rw [Po, Po]
      apply CellularTelescopeAdjunction.prism_cells_disjoint c i j
      intro heq
      cases heq
      exact hne rfl
  have Mcover : ⋃ (d : ℕ) (i : I d), M d i '' Metric.closedBall 0 1 = Set.univ := by
    apply Set.eq_univ_of_forall
    intro y
    rcases CellularTelescopeAdjunction.level_and_prism_cells_cover c y with
      ⟨n, d, i, hy⟩ | ⟨n, d, i, hy⟩
    · refine Set.mem_iUnion.mpr ⟨d, Set.mem_iUnion.mpr ⟨Sum.inl ⟨n, i⟩, ?_⟩⟩
      rw [Mlevel]
      exact Set.image_mono Metric.ball_subset_closedBall ((Lo n d i).symm ▸ hy)
    · refine Set.mem_iUnion.mpr ⟨d + 1,
        Set.mem_iUnion.mpr ⟨Sum.inr ⟨⟨d, rfl⟩, n, i⟩, ?_⟩⟩
      change y ∈ P n d i '' Metric.closedBall 0 1
      exact Set.image_mono Metric.ball_subset_closedBall ((Po n d i).symm ▸ hy)
  have Mclosed (A : Set (telescope c))
      (hA : ∀ d i, IsClosed (A ∩ M d i '' Metric.closedBall 0 1)) : IsClosed A := by
    have hq : Topology.IsQuotientMap (quotient c) := isQuotientMap_quotient_mk'
    apply (Topology.isQuotientMap_iff_isClosed.mp hq).2 A |>.mpr
    apply isClosed_sigma_iff.mpr
    intro n
    apply Topology.cw_interval_product_closed_of_closed_cells
    intro d i
    have h := hA (d + 1) (Sum.inr ⟨⟨d, rfl⟩, n, i⟩)
    change IsClosed (A ∩ P n d i '' Metric.closedBall 0 1) at h
    rw [Pc] at h
    have hpre := (h.preimage (cylinder c n).continuous).inter
      ((Topology.CWComplex.isClosed_closedCell (C := (Set.univ : Set (X n)))
        (n := d) (i := i)).prod isClosed_univ)
    convert hpre using 1
    ext y
    constructor
    · intro hy
      exact ⟨⟨hy.1, ⟨y, hy.2, rfl⟩⟩, hy.2⟩
    · exact fun hy ↦ ⟨hy.1.1, hy.2⟩
  have finite_frontier (d : ℕ) (i : I d) :
      ∃ S : Finset (Σ k, I k), (∀ a ∈ S, a.1 < d) ∧
        M d i '' Metric.sphere 0 1 ⊆ ⋃ a ∈ S, M a.1 a.2 '' Metric.closedBall 0 1 := by
    rcases i with ⟨n, i⟩ | ⟨⟨m, hm⟩, n, i⟩
    · obtain ⟨F, hF⟩ := Topology.CWComplex.mapsTo (C := (Set.univ : Set (X n))) d i
      let f : (Σ k, Topology.CWComplex.cell (Set.univ : Set (X n)) k) → Σ k, I k :=
        fun a ↦ ⟨a.1, Sum.inl ⟨n, a.2⟩⟩
      let S := ((Finset.range d).sigma F).image f
      refine ⟨S, ?_, ?_⟩
      · intro a ha
        obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp ha
        exact Finset.mem_range.mp (Finset.mem_sigma.mp hb).1
      · rintro y ⟨z, hz, rfl⟩
        obtain ⟨k, hk, j, hj, w, hw, hwz⟩ := by
          simpa only [Set.mem_iUnion, exists_prop, Set.mem_image] using hF hz
        have hjS : f ⟨k, j⟩ ∈ S := Finset.mem_image.mpr
          ⟨⟨k, j⟩, Finset.mem_sigma.mpr ⟨Finset.mem_range.mpr hk, hj⟩, rfl⟩
        refine Set.mem_iUnion.mpr ⟨f ⟨k, j⟩, Set.mem_iUnion.mpr ⟨hjS, ?_⟩⟩
        change L n d i z ∈ L n k j '' Metric.closedBall 0 1
        exact ⟨w, hw, by rw [Lf, Lf]; exact congrArg (level c n) hwz⟩
    · subst d
      obtain ⟨F, G, hFdim, hGdim, hbound⟩ :=
        CellularTelescopeAdjunction.prism_boundary_subset_finite_cells c hc n m i
      let f : (Σ k, Topology.CWComplex.cell (Set.univ : Set (X (n + 1))) k) → Σ k, I k :=
        fun a ↦ ⟨a.1, Sum.inl ⟨n + 1, a.2⟩⟩
      let g : (Σ k, Topology.CWComplex.cell (Set.univ : Set (X n)) k) → Σ k, I k :=
        fun a ↦ ⟨a.1 + 1, Sum.inr ⟨⟨a.1, rfl⟩, n, a.2⟩⟩
      let bottom : Σ k, I k := ⟨m, Sum.inl ⟨n, i⟩⟩
      let S := insert bottom (F.image f ∪ G.image g)
      refine ⟨S, ?_, ?_⟩
      · intro a ha
        rcases Finset.mem_insert.mp ha with rfl | ha
        · exact Nat.lt_succ_self m
        rcases Finset.mem_union.mp ha with ha | ha
        · obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp ha
          exact hFdim b hb
        · obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp ha
          exact hGdim b hb
      · rintro y ⟨z, hz, rfl⟩
        have hzbound := hbound ⟨E n m i z, Eb n m i ⟨z, hz, rfl⟩, rfl⟩
        rcases hzbound with (hbottom | htop) | hside
        · refine Set.mem_iUnion.mpr ⟨bottom,
            Set.mem_iUnion.mpr ⟨Finset.mem_insert_self _ _, ?_⟩⟩
          change P n m i z ∈ L n m i '' Metric.closedBall 0 1
          rw [Pf, Lc]
          exact hbottom
        · obtain ⟨a, ha, hya⟩ := by
            simpa only [Set.mem_iUnion, exists_prop] using htop
          have has : f a ∈ S := Finset.mem_insert_of_mem
            (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨a, ha, rfl⟩))
          refine Set.mem_iUnion.mpr ⟨f a, Set.mem_iUnion.mpr ⟨has, ?_⟩⟩
          change P n m i z ∈ L (n + 1) a.1 a.2 '' Metric.closedBall 0 1
          rw [Pf, Lc]
          exact hya
        · obtain ⟨a, ha, hya⟩ := by
            simpa only [Set.mem_iUnion, exists_prop] using hside
          have has : g a ∈ S := Finset.mem_insert_of_mem
            (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨a, ha, rfl⟩))
          refine Set.mem_iUnion.mpr ⟨g a, Set.mem_iUnion.mpr ⟨has, ?_⟩⟩
          change P n m i z ∈ P n a.1 a.2 '' Metric.closedBall 0 1
          rw [Pf, Pc]
          exact hya
  have Mfront (d : ℕ) (i : I d) : ∃ J : ∀ k, Finset (I k),
      Set.MapsTo (M d i) (Metric.sphere 0 1)
        (⋃ (k < d) (j ∈ J k), M k j '' Metric.closedBall 0 1) := by
    obtain ⟨S, hdim, hS⟩ := finite_frontier d i
    let J (k : ℕ) : Finset (I k) := S.preimage (Sigma.mk k) sigma_mk_injective.injOn
    refine ⟨J, ?_⟩
    intro z hz
    obtain ⟨⟨k, j⟩, hj, hzj⟩ := by
      simpa only [Set.mem_iUnion, exists_prop] using hS ⟨z, hz, rfl⟩
    exact Set.mem_iUnion.mpr ⟨k, Set.mem_iUnion.mpr ⟨hdim ⟨k, j⟩ hj,
      Set.mem_iUnion.mpr ⟨j, Set.mem_iUnion.mpr ⟨Finset.mem_preimage.mpr hj, hzj⟩⟩⟩⟩
  let cw : Topology.CWComplex (Set.univ : Set (telescope c)) := {
    cell := I
    map := M
    source_eq := Msource
    continuousOn := Mcont
    continuousOn_symm := Minv
    pairwiseDisjoint' := Mdisj
    mapsTo' := Mfront
    closed' := fun A _ ↦ Mclosed A
    union' := Mcover }
  refine ⟨cw, fun d ↦ Equiv.refl (I d), ?_, ?_⟩
  · intro d n i
    exact Lo n d i
  · intro m d h n i
    subst d
    exact Po n m i

/-- The CW-structure component of the joint telescope construction. -/
theorem cellular_mapping_telescope_cw_structure_exists_g7
    {X : ℕ → Type*} [∀ n, TopologicalSpace (X n)] [∀ n, T2Space (X n)]
    [∀ n, Topology.CWComplex (Set.univ : Set (X n))]
    (c : ∀ n, C(X n, X (n + 1)))
    (hc : ∀ n d : ℕ, Set.MapsTo (c n)
      (Topology.CWComplex.skeleton (Set.univ : Set (X n)) d : Set (X n))
      (Topology.CWComplex.skeleton (Set.univ : Set (X (n + 1))) d : Set (X (n + 1)))) :
    Nonempty (Topology.CWComplex (Set.univ : Set (telescope c))) := by
  obtain ⟨cw, _⟩ := cellular_mapping_telescope_cw_core c hc
  exact ⟨cw⟩

end HolomorphicAnosov


