import HolomorphicAnosov.Topology.NormalSigma
import HolomorphicAnosov.Topology.CWComplex.HomotopyExtension
import HolomorphicAnosov.Topology.CWComplex.Normality
import HolomorphicAnosov.Topology.CWIntervalProduct
import HolomorphicAnosov.Topology.NormalClosedAdjunction
import HolomorphicAnosov.Topology.Homotopy.MappingTelescopeSequence
import Mathlib.Topology.Homeomorph.Lemmas

/-! # Hausdorffness of the original cellular mapping telescope

Fritsch–Piccinini Appendix A.4.8(iv), pp.260–261, applied to the endpoint
adjunction. The quotient topology and the existing telescope are unchanged.
-/

namespace HolomorphicAnosov

open MappingTelescope.Sequence

namespace CellularTelescopeAdjunction

noncomputable section
open Set
universe u

variable {X : ℕ → Type u} [∀ n, TopologicalSpace (X n)]

/-- The actual closed endpoint subspace of the coproduct of original cylinders.
Source: Fritsch–Piccinini Theorem 2.3.1 pp.62–63, specialized to the endpoint
adjunction in the proof below. No topology is assigned independently of the
coproduct subspace topology. -/
def endpoints (X : ℕ → Type u) : Set (Cylinder X) :=
  {z | z.2.2 = 0 ∨ z.2.2 = 1}

/-- The prescribed endpoint attachment into the original coproduct of levels.
Source: the endpoint specialization of Fritsch–Piccinini Theorem 2.3.1.
The bottom retains its layer and point; the top uses the supplied next bond. -/
def attach (c : ∀ n, C(X n, X (n + 1))) (z : endpoints X) : Σ n, X n :=
  if z.val.2.2 = 0 then ⟨z.val.1, z.val.2.1⟩
  else ⟨z.val.1 + 1, c z.val.1 z.val.2.1⟩

/-- The single cellular-adjunction generating relation, on the original raw sum.
Source: Fritsch–Piccinini Appendix A.4 pp.258–259. This is exactly the ordinary
adjunction relation accepted by `normal_closed_adjunction`. -/
def relation (c : ∀ n, C(X n, X (n + 1)))
    (p q : (Σ n, X n) ⊕ Cylinder X) : Prop :=
  ∃ z : endpoints X, p = Sum.inr z.val ∧ q = Sum.inl (attach c z)

/-- The ordinary final-topology adjunction, before any CW or separation assertion.
Source: Fritsch–Piccinini Appendix A.4 pp.258–259. Mathlib's `Quot` carries
precisely the coinduced topology of its projection from the raw sum. -/
abbrev Space (c : ∀ n, C(X n, X (n + 1))) := Quot (relation c)

/-- The endpoint union is closed in the actual coproduct topology.
Source: FP Theorem 2.3.1's endpoint-domain specialization. In every summand
it is the union of the two closed endpoint slices; the sigma closed-set
criterion gives the assertion for arbitrary, possibly empty, layers. -/
theorem endpoints_isClosed : IsClosed (endpoints X) := by
  apply isClosed_sigma_iff.mpr
  intro n
  exact (isClosed_eq continuous_snd continuous_const).union
    (isClosed_eq continuous_snd continuous_const)

/-- The endpoint map is continuous on its original subspace domain.
Source: the same endpoint specialization. The time-zero and time-one pieces
are clopen in the endpoint union. Each formula is a continuous coproduct map,
and the two disjoint pieces therefore paste continuously. -/
theorem attach_continuous (c : ∀ n, C(X n, X (n + 1))) : Continuous (attach c) := by
  classical
  have htimeRaw : Continuous (fun z : Cylinder X ↦ z.2.2) :=
    continuous_sigma fun _ ↦ continuous_snd
  have htime : Continuous (fun z : endpoints X ↦ z.val.2.2) :=
    htimeRaw.comp continuous_subtype_val
  have hclosed : IsClosed {z : endpoints X | z.val.2.2 = 0} :=
    isClosed_eq htime continuous_const
  have hcompl : {z : endpoints X | z.val.2.2 = 0}ᶜ =
      {z : endpoints X | z.val.2.2 = 1} := by
    ext z
    simp only [mem_compl_iff, mem_ofPred_eq]
    constructor
    · exact fun hz ↦ z.prop.resolve_left hz
    · intro hz hzero
      have : (0 : unitInterval) = 1 := hzero.symm.trans hz
      exact zero_ne_one (congrArg Subtype.val this)
  have hopen : IsOpen {z : endpoints X | z.val.2.2 = 0} := by
    apply isClosed_compl_iff.mp
    rw [hcompl]
    exact isClosed_eq htime continuous_const
  have hfront : frontier {z : endpoints X | z.val.2.2 = 0} = ∅ :=
    (show IsClopen _ from ⟨hclosed, hopen⟩).frontier_eq
  have hbottomRaw : Continuous (fun z : Cylinder X ↦ (⟨z.1, z.2.1⟩ : Σ n, X n)) := by
    apply continuous_sigma
    intro n
    exact (continuous_sigmaMk (σ := X) (i := n)).comp continuous_fst
  have htopRaw : Continuous
      (fun z : Cylinder X ↦ (⟨z.1 + 1, c z.1 z.2.1⟩ : Σ n, X n)) := by
    apply continuous_sigma
    intro n
    exact (continuous_sigmaMk (σ := X) (i := n + 1)).comp
      ((c n).continuous.comp continuous_fst)
  have hbottom : Continuous (fun z : endpoints X ↦ (⟨z.val.1, z.val.2.1⟩ : Σ n, X n)) :=
    hbottomRaw.comp continuous_subtype_val
  have htop : Continuous
      (fun z : endpoints X ↦ (⟨z.val.1 + 1, c z.val.1 z.val.2.1⟩ : Σ n, X n)) :=
    htopRaw.comp continuous_subtype_val
  exact hbottom.if (by
    intro z hz
    rw [hfront] at hz
    exact hz.elim) htop

private theorem bottom_identification (c : ∀ n, C(X n, X (n + 1)))
    (n : ℕ) (x : X n) :
    Quot.mk (relation c) (Sum.inr ⟨n, (x, 0)⟩) =
      Quot.mk (relation c) (Sum.inl ⟨n, x⟩) := by
  apply Quot.sound
  refine ⟨⟨⟨n, (x, 0)⟩, Or.inl rfl⟩, rfl, ?_⟩
  simp [attach]

private theorem top_identification (c : ∀ n, C(X n, X (n + 1)))
    (n : ℕ) (x : X n) :
    Quot.mk (relation c) (Sum.inr ⟨n, (x, 1)⟩) =
      Quot.mk (relation c) (Sum.inl ⟨n + 1, c n x⟩) := by
  apply Quot.sound
  refine ⟨⟨⟨n, (x, 1)⟩, Or.inr rfl⟩, rfl, ?_⟩
  have h : (1 : unitInterval) ≠ 0 := fun h ↦ one_ne_zero (congrArg Subtype.val h)
  simp [attach, h]

private theorem cylinder_respects (c : ∀ n, C(X n, X (n + 1)))
    (p q : Cylinder X) (hpq : setoid c p q) :
    Quot.mk (relation c) (Sum.inr p) = Quot.mk (relation c) (Sum.inr q) := by
  change Relation.EqvGen (edge c) p q at hpq
  induction hpq with
  | rel p q h =>
      obtain ⟨n, x, h | h⟩ := h
      · rcases h with ⟨rfl, rfl⟩
        exact (top_identification c n x).trans (bottom_identification c (n + 1) (c n x)).symm
      · rcases h with ⟨rfl, rfl⟩
        exact (bottom_identification c (n + 1) (c n x)).trans (top_identification c n x).symm
  | refl => rfl
  | symm _ _ _ h => exact h.symm
  | trans _ _ _ _ _ h h' => exact h.trans h'

/-- Send an original telescope representative to its original cylinder point in
the ordinary adjunction. Source: the explicit comparison step below. The two
adjunction endpoint equations respect every original generated seam. -/
def fromTelescope (c : ∀ n, C(X n, X (n + 1))) : telescope c → Space c :=
  Quotient.lift (fun z ↦ Quot.mk (relation c) (Sum.inr z)) (cylinder_respects c)

private def rawToTelescope (c : ∀ n, C(X n, X (n + 1))) :
    (Σ n, X n) ⊕ Cylinder X → telescope c :=
  Sum.elim (fun z ↦ level c z.1 z.2) (quotient c)

private theorem rawToTelescope_respects (c : ∀ n, C(X n, X (n + 1)))
    (p q : (Σ n, X n) ⊕ Cylinder X) (hpq : relation c p q) :
    rawToTelescope c p = rawToTelescope c q := by
  obtain ⟨⟨⟨n, x, t⟩, ht⟩, rfl, rfl⟩ := hpq
  change t = 0 ∨ t = 1 at ht
  rcases ht with rfl | rfl
  · simp [rawToTelescope, attach, level, cylinder, quotient]
  · have h : (1 : unitInterval) ≠ 0 := fun h ↦ one_ne_zero (congrArg Subtype.val h)
    simp only [rawToTelescope, Sum.elim_inr, Sum.elim_inl, attach, h, ↓reduceIte]
    exact Quotient.sound (Relation.EqvGen.rel _ _ ⟨n, x, Or.inl ⟨rfl, rfl⟩⟩)

/-- Send the level summand to its original bottom and the cylinder summand to
its original quotient representative. Source: the explicit comparison step below.
The prescribed bottom/top attachment equations are exactly the original seams. -/
def toTelescope (c : ∀ n, C(X n, X (n + 1))) : Space c → telescope c :=
  Quot.lift (rawToTelescope c) (rawToTelescope_respects c)

/-- The ordinary one-shot endpoint adjunction and the original quotient-cylinder
telescope have identical topology under their explicit point comparison.
Source: Fritsch–Piccinini Appendix A.4 pp.258–259 and the comparison step of the
FP Theorem 2.3.1 specialization below. Quotient descent supplies continuity in
both directions; induction on representatives proves the inverse equations.
No Hausdorffness, CW structure, nonempty layer, or injective bond is assumed. -/
def homeomorph (c : ∀ n, C(X n, X (n + 1))) : Space c ≃ₜ telescope c where
  toFun := toTelescope c
  invFun := fromTelescope c
  left_inv := by
    intro z
    refine Quot.inductionOn z ?_
    intro p
    cases p with
    | inl a => exact bottom_identification c a.1 a.2
    | inr y => rfl
  right_inv := by
    intro z
    exact Quotient.inductionOn z (fun _ ↦ rfl)
  continuous_toFun := continuous_quot_lift _
    ((continuous_sigma fun n ↦ (level c n).continuous).sumElim (quotient c).continuous)
  continuous_invFun :=
    (continuous_quot_mk.comp continuous_inr).quotient_lift (cylinder_respects c)

/-- The homeomorphism preserves each original level map literally. -/
theorem homeomorph_level (c : ∀ n, C(X n, X (n + 1))) (n : ℕ) (x : X n) :
    homeomorph c (Quot.mk (relation c) (Sum.inl ⟨n, x⟩)) = level c n x := rfl

/-- The homeomorphism preserves each original cylinder map literally. -/
theorem homeomorph_cylinder (c : ∀ n, C(X n, X (n + 1)))
    (n : ℕ) (z : X n × unitInterval) :
    homeomorph c (Quot.mk (relation c) (Sum.inr ⟨n, z⟩)) = cylinder c n z := rfl

/-- The ordinary adjunction has exactly the final topology of its original level
and cylinder maps. Source: FP Theorem 2.3.1, final-topology paragraph p.63.
Apply the quotient continuity criterion, then the sum and sigma criteria; no
compact generation or subsequent CW structure is used in this identity. -/
theorem continuous_iff {W : Type*} [TopologicalSpace W]
    (c : ∀ n, C(X n, X (n + 1))) (g : Space c → W) :
    Continuous g ↔
      (∀ n, Continuous (fun x : X n ↦ g (Quot.mk (relation c) (Sum.inl ⟨n, x⟩)))) ∧
      (∀ n, Continuous (fun z : X n × unitInterval ↦
        g (Quot.mk (relation c) (Sum.inr ⟨n, z⟩)))) := by
  rw [isQuotientMap_quot_mk.continuous_iff, continuous_sum_dom]
  exact and_congr continuous_sigma_iff continuous_sigma_iff

/-- A function on the original telescope is continuous exactly when every
original cylinder restriction is continuous. Source: Hatcher A.11 p.528 and
FP Theorem 2.3.1's original-final-topology comparison. The criterion uses the
existing quotient map and the actual topological coproduct of cylinders. -/
theorem telescope_continuous_iff {W : Type*} [TopologicalSpace W]
    (c : ∀ n, C(X n, X (n + 1))) (g : telescope c → W) :
    Continuous g ↔ ∀ n, Continuous (fun z : X n × unitInterval ↦ g (cylinder c n z)) := by
  have hq : Topology.IsQuotientMap (quotient c) := isQuotientMap_quotient_mk'
  exact hq.continuous_iff.trans continuous_sigma_iff


end
end CellularTelescopeAdjunction


open Set
universe u
/-- The union of all cylinder endpoints has the homotopy extension property.
Source: Fritsch–Piccinini Appendix A.4.2(ii), pp.251–252, and the endpoint
subcomplex in the ordinary interval-product construction, Proposition 2.2.2 p.58.
In each cylinder, apply the CW pair homotopy extension theorem to its endpoint
subcomplex. The prescribed homotopy pulls back along the continuous summand
inclusion. Choose these extensions for every layer and combine them; the
homeomorphism distributing the interval product over the topological coproduct
proves joint continuity. The bottom and endpoint equations hold summandwise. -/
theorem CellularTelescopeAdjunction.endpoint_cofibration
    {X : ℕ → Type u} [∀ n, TopologicalSpace (X n)] [∀ n, T2Space (X n)]
    [∀ n, _root_.Topology.CWComplex (Set.univ : Set (X n))]
    (T : Type u) [TopologicalSpace T]
    (g : Cylinder X → T) (h : unitInterval × CellularTelescopeAdjunction.endpoints X → T)
    (hg : Continuous g) (hh : Continuous h)
    (hzero : ∀ d : CellularTelescopeAdjunction.endpoints X, h (0, d) = g d) :
    ∃ H : unitInterval × Cylinder X → T,
      Continuous H ∧ (∀ y, H (0, y) = g y) ∧
      ∀ (t : unitInterval) (d : CellularTelescopeAdjunction.endpoints X),
        H (t, d) = h (t, d) := by
  classical
  have local_extension (n : ℕ) : ∃ H : C(unitInterval × (X n × unitInterval), T),
      (∀ y, H (0, y) = g ⟨n, y⟩) ∧
      ∀ (t : unitInterval) (y : X n × unitInterval) (hy : y.2 = 0 ∨ y.2 = 1),
        H (t, y) = h (t, ⟨⟨n, y⟩, hy⟩) := by
    obtain ⟨K, labels, hlabels⟩ := Topology.cw_interval_product (X := X n)
    let := K
    obtain ⟨B, hB, _⟩ := hlabels.2.2.2.1
    have hb (b : (B : Set (X n × unitInterval))) : b.val.2 = 0 ∨ b.val.2 = 1 := by
      have hb := b.property
      have hb' : b.val ∈ univ.prod {(0 : unitInterval), 1} := hB ▸ hb
      exact hb'.2
    let e : ↥(B : Set (X n × unitInterval)) → CellularTelescopeAdjunction.endpoints X :=
      fun b ↦ ⟨⟨n, b.val⟩, hb b⟩
    have he : Continuous e :=
      ((continuous_sigmaMk (σ := fun n ↦ X n × unitInterval) (i := n)).comp
        continuous_subtype_val).subtype_mk _
    let f : C(X n × unitInterval, T) := ⟨fun y ↦ g ⟨n, y⟩, hg.comp continuous_sigmaMk⟩
    let k : C(unitInterval × (B : Set (X n × unitInterval)), T) :=
      ⟨fun p ↦ h (p.1, e p.2), hh.comp (continuous_fst.prodMk (he.comp continuous_snd))⟩
    obtain ⟨H, Hzero, Hside, _⟩ := cw_pair_homotopy_extension B f k (fun b ↦ hzero (e b))
    refine ⟨H, Hzero, ?_⟩
    intro t y hy
    have hyB : y ∈ (B : Set (X n × unitInterval)) := by
      rw [hB]
      exact ⟨mem_univ _, by simpa using hy⟩
    exact Hside t ⟨y, hyB⟩
  choose H Hzero Hside using local_extension
  let F : unitInterval × Cylinder X → T := fun p ↦ H p.2.1 (p.1, p.2.2)
  refine ⟨F, ?_, ?_, ?_⟩
  · have hF : Continuous (fun p : (Σ n, (X n × unitInterval) × unitInterval) ↦
        H p.1 (p.2.2, p.2.1)) :=
      continuous_sigma fun n ↦ (H n).continuous.comp (continuous_snd.prodMk continuous_fst)
    exact hF.comp ((Homeomorph.sigmaProdDistrib (X := fun n ↦ X n × unitInterval)
      (Y := unitInterval)).continuous.comp continuous_swap)
  · rintro ⟨n, y⟩
    exact Hzero n y
  · rintro t ⟨⟨n, y⟩, hy⟩
    exact Hside n t y hy
/-- The mapping telescope of continuous maps between Hausdorff CW spaces is
Hausdorff in its original quotient topology; the maps need not be cellular.
Source: Fritsch–Piccinini Proposition 1.2.1 pp.22–23, Proposition 2.2.2 p.58,
and Appendix A.4.8(iv) pp.260–261, specialized to the endpoint adjunction.
Each level and its ordinary interval product are normal and compactly generated
by CW normality. Their topological coproducts inherit these two properties.
The endpoint union is closed and has the homotopy extension property, and the
endpoint attaching map is continuous. The closed-adjunction theorem therefore
makes its ordinary quotient Hausdorff. The explicit homeomorphism with the
original cylinder quotient transfers Hausdorffness to the telescope.
No nonemptiness, finite dimension, finite cell family, or injective bond is used.
DAG node: `topo.cellular_telescope_hausdorff_g5`. -/
theorem cellular_telescope_hausdorff
    {X : ℕ → Type u} [∀ n, TopologicalSpace (X n)] [∀ n, T2Space (X n)]
    [∀ n, _root_.Topology.CWComplex (Set.univ : Set (X n))]
    (c : ∀ n, C(X n, X (n + 1))) : T2Space (telescope c) := by
  classical
  have normal_layer (n : ℕ) :=
    (Topology.CWComplex.normality_and_compact_generation (X := X n)).1
  let (n : ℕ) : NormalSpace (X n) := (normal_layer n).1
  let (n : ℕ) : CompactlyGeneratedSpace (X n) := (normal_layer n).2
  have normal_cylinder (n : ℕ) :
      NormalSpace (X n × unitInterval) ∧ CompactlyGeneratedSpace (X n × unitInterval) := by
    obtain ⟨K, _⟩ := Topology.cw_interval_product (X := X n)
    let := K
    exact (Topology.CWComplex.normality_and_compact_generation (X := X n × unitInterval)).1
  let (n : ℕ) : NormalSpace (X n × unitInterval) := (normal_cylinder n).1
  let (n : ℕ) : CompactlyGeneratedSpace (X n × unitInterval) := (normal_cylinder n).2
  let : NormalSpace (Σ n, X n) := normalSpace_sigma
  let : NormalSpace (Cylinder X) := normalSpace_sigma
  have hadj := normal_closed_adjunction (CellularTelescopeAdjunction.endpoints X)
    CellularTelescopeAdjunction.endpoints_isClosed (CellularTelescopeAdjunction.endpoint_cofibration (X := X))
    (CellularTelescopeAdjunction.attach c) (CellularTelescopeAdjunction.attach_continuous c)
  let : T2Space (CellularTelescopeAdjunction.Space c) := hadj.2
  exact (CellularTelescopeAdjunction.homeomorph c).symm.isEmbedding.t2Space
end HolomorphicAnosov

