import HolomorphicAnosov.Topology.EuclideanFixedPointIndex
import HolomorphicAnosov.Topology.ENRRetractionRepresentation

/-!
# The actual local fixed-point index on an ENR

Source: Dold, *Fixed point index and fixed point theorem for Euclidean neighborhood
retracts*, Topology 4 (1965), (1.3)–(1.8), pp.1–3, and (2.1)–(2.4), pp.3–4;
Granas, *The Leray–Schauder index and the fixed point theory for arbitrary ANRs*,
Bull. Soc. Math. France 100 (1972), §8 pp.217–218, §10 pp.223–224, §12 p.226.
Current node: `topo.enr_local_fixed_point_index_conjugacy_g9`.

The index below evaluates the canonical standard-positive integral Euclidean index
on the literal retracted map. A named theorem certifies compact support of the specified retracted map.
Its compactness argument supplies only admissibility, not integer data. No caller supplies an index or index axioms.
The ENR data and the Euclidean index are reused from their own producer modules.
-/

noncomputable section

open TopologicalSpace
open scoped BigOperators

namespace HolomorphicAnosov.FixedPointIndexInterface

universe u v

/-- The original inverse-image open domain, Dold (2.3), p.3.
The openness proof uses the original open Euclidean domain and continuous retraction. -/
def enrRetractedOpenDomain {X : Type u} [TopologicalSpace X]
    (e : ENRRepresentation X) (U : Opens X) : Opens (Euclidean e.dimension) := by
  refine ⟨retractedDomain e U, ?_⟩
  have heq : retractedDomain e U =
      (Subtype.val : e.domain → Euclidean e.dimension) ''
        (e.retraction ⁻¹' (U : Set X)) := by
    ext z
    constructor
    · rintro ⟨hz, hr⟩
      exact ⟨⟨z, hz⟩, hr, rfl⟩
    · rintro ⟨z, hz, rfl⟩
      exact ⟨z.2, hz⟩
  rw [heq]
  exact e.domain_open.isOpenMap_subtype_val _ (U.isOpen.preimage e.retraction.continuous)

/-- The literal `s ∘ f ∘ r`, with its domain presented as an open Euclidean set.
Source: Dold (2.3), p.3. `W ≤ U` supplies domain membership, not invariance of W. -/
def enrEuclideanLocalMap {X : Type u} [TopologicalSpace X]
    (e : ENRRepresentation X) (U W : Opens X) (hWU : W ≤ U) (f : C(U, X)) :
    C(enrRetractedOpenDomain e W, Euclidean e.dimension) :=
  retractedLocalMap e U W hWU f

/-- The actual fixed locus, in the original local domain. Source: Dold (2.3), p.3. -/
def enrLocalFixedSet {X : Type u} [TopologicalSpace X] {U : Opens X}
    (f : C(U, X)) : Set U :=
  {x | f x = x.1}

/-- Compact support of the literal retracted map on every neighborhood of all fixed points.

Source: Dold (2.3), printed p.3, the admissibility assertion preceding the definition;
Granas (10.1.1), p.223. This is the first step of the current node's proof.

Complete natural-language proof: let K be the fixed set in U. If v is fixed by s f r,
apply r and use r s=id to get f(r(v))=r(v). Conversely, for x∈K the point s(x)
belongs to r⁻¹(W), by the covering hypothesis, and s f r(s(x))=s(x).
These operations are inverse. The map K→r⁻¹(W), x↦s(x), is continuous with the
subspace topologies: its ambient map is the continuous section and its membership
proof uses precisely K⊆W. Its image is exactly the displayed Euclidean fixed set.
That image is compact as a continuous image of K. No compactness of the whole map,
invariance of W, or compactness of its closure is required. Empty K and dimension
zero use the same image argument. -/
theorem enrRetractedLocalMap_compact_fixedSet
    {X : Type u} [TopologicalSpace X] (e : ENRRepresentation X)
    (U W : Opens X) (hWU : W ≤ U) (f : C(U, X))
    (hK : IsCompact (enrLocalFixedSet f))
    (hcover : ∀ x : U, f x = x.1 → x.1 ∈ W) :
    IsCompact (euclideanFixedSet (enrEuclideanLocalMap e U W hWU f)) := by
  let K : Set U := enrLocalFixedSet f
  let g := enrEuclideanLocalMap e U W hWU f
  let t : C(K, enrRetractedOpenDomain e W) :=
    { toFun := fun x ↦ ⟨(e.sectionMap x).val,
        ⟨(e.sectionMap x).property, by
          rw [e.retraction_section x]
          exact hcover x x.property⟩⟩
      continuous_toFun := by fun_prop }
  have hEq : euclideanFixedSet g = t '' (Set.univ : Set K) := by
    ext v
    constructor
    · intro hv
      change g v = v.val at hv
      let x : U := ⟨e.retraction (retractedDomainInclusion e W v),
        hWU v.property.choose_spec⟩
      have hv' : e.sectionMap (f x) = retractedDomainInclusion e W v := by
        apply Subtype.ext
        change (e.sectionMap (f (retractedDomainToLocalDomain e U W hWU v))).val = v.val
        exact hv
      have hxf : f x = x.1 := by
        have hr := congrArg e.retraction hv'
        rw [e.retraction_section] at hr
        simpa [x] using hr
      have hxK : x ∈ K := by
        change f x = x.1
        exact hxf
      have hsec : e.sectionMap x = retractedDomainInclusion e W v := by
        rw [← hxf]
        exact hv'
      have hxs : t ⟨x, hxK⟩ = v := by
        apply Subtype.ext
        change (e.sectionMap x).val = (retractedDomainInclusion e W v).val
        exact congrArg Subtype.val hsec
      exact ⟨⟨x, hxK⟩, Set.mem_univ _, hxs⟩
    · rintro ⟨x, -, rfl⟩
      change g (t x) = (t x).val
      have hret : e.retraction (retractedDomainInclusion e W (t x)) = (x : X) := by
        have heq : retractedDomainInclusion e W (t x) = e.sectionMap (x : X) := by
          apply Subtype.ext
          rfl
        rw [heq, e.retraction_section]
      let y : U := ⟨e.retraction (retractedDomainInclusion e W (t x)), hWU (t x).property.choose_spec⟩
      have hy : y = (x : U) := by
        apply Subtype.ext
        exact hret
      change (e.sectionMap (f y)).val = (t x).val
      rw [hy, x.property]
      rfl

  rw [hEq]
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hcomp : IsCompact (t '' (Set.univ : Set K)) := by
    exact IsCompact.image isCompact_univ t.continuous
  simpa [K] using hcomp

/-- The actual Euclidean homological index of the retracted local map.
Source: Dold (2.3), p.3; Granas (10.1.1), p.223. The named compact-support
certificate proves admissibility of this specified map; no index data are chosen. -/
def enrRetractionIndex {X : Type u} [TopologicalSpace X]
    (e : ENRRepresentation X) (U W : Opens X) (hWU : W ≤ U) (f : C(U, X))
    (hK : IsCompact (enrLocalFixedSet f))
    (hcover : ∀ x : U, f x = x.1 → x.1 ∈ W) : ℤ :=
  euclideanFixedPointIndex (enrEuclideanLocalMap e U W hWU f)
    (enrRetractedLocalMap_compact_fixedSet e U W hWU f hK hcover)

/-- Dold's index on the original open domain; the theorem proves independence of e.
Source: Dold (2.3), p.3. Compactness certifies admissibility, and the integer data
are the actual retracted homological index, with no value assigned off admissibility. -/
def enrLocalFixedPointIndex {X : Type u} [TopologicalSpace X]
    (e : ENRRepresentation X) (U : Opens X) (f : C(U, X))
    (hK : IsCompact (enrLocalFixedSet f)) : ℤ :=
  enrRetractionIndex e U U le_rfl f hK (fun x _ ↦ x.2)

/-- Actual restriction to a smaller open local domain. Source: Dold (1.3), p.1. -/
def enrRestrictLocalMap {X : Type u} [TopologicalSpace X] {U : Opens X}
    (f : C(U, X)) (W : Opens X) (hWU : W ≤ U) : C(W, X) :=
  f.comp ⟨fun x ↦ ⟨x.1, hWU x.2⟩, continuous_subtype_val.subtype_mk _⟩

/-- An actual time slice on the original domain. Source: Dold (1.7), p.2. -/
def enrHomotopySlice {X : Type u} [TopologicalSpace X] {U : Opens X}
    (H : C(U × unitInterval, X)) (t : unitInterval) : C(U, X) :=
  H.comp ⟨fun x ↦ (x, t), continuous_id.prodMk continuous_const⟩

/-- The open image of the original domain under a homeomorphism.
Source: Dold (1.8), (2.3), pp.2–3. -/
def enrConjugateDomain {X : Type u} {Y : Type v} [TopologicalSpace X]
    [TopologicalSpace Y] (h : X ≃ₜ Y) (U : Opens X) : Opens Y :=
  ⟨h '' (U : Set X), h.isOpenMap _ U.isOpen⟩

/-- The literal conjugate `h ∘ f ∘ h⁻¹`, with all local-domain guards.
Source: Dold (1.8), (2.3), pp.2–3; Granas Theorem10.1, p.224. -/
def enrConjugateLocalMap {X : Type u} {Y : Type v} [TopologicalSpace X]
    [TopologicalSpace Y] (h : X ≃ₜ Y) (U : Opens X) (f : C(U, X)) :
    C(enrConjugateDomain h U, Y) := by
  let a : C(enrConjugateDomain h U, U) :=
    ⟨fun y ↦ ⟨h.symm y.1, by
      rcases y.2 with ⟨x, hx, hxy⟩
      rw [← hxy, h.symm_apply_apply]
      exact hx⟩,
      (h.symm.continuous.comp continuous_subtype_val).subtype_mk _⟩
  exact (⟨h, h.continuous⟩ : C(X, Y)).comp (f.comp a)

/-- The Euclidean space's identity representation, including dimension zero.
Source: Dold (2.1), (2.3), p.3. All maps and the retraction identity are literal. -/
def euclideanENRRepresentation (n : ℕ) : ENRRepresentation (Euclidean n) where
  dimension := n
  domain := Set.univ
  domain_open := isOpen_univ
  sectionMap := ⟨fun x ↦ ⟨x, Set.mem_univ x⟩, continuous_id.subtype_mk _⟩
  retraction := ⟨Subtype.val, continuous_subtype_val⟩
  retraction_section := fun _ ↦ rfl

/-- The canonical ENR index: exact retraction formula, independence, local laws and conjugacy.

Source: Dold (1.3)–(1.8), pp.1–3, (2.3)–(2.4), pp.3–4; Granas §8
pp.217–218, formulas8.1.1–8.1.6, §10 pp.223–224 and §12 p.226.
Current node: `topo.enr_local_fixed_point_index_conjugacy_g9`.

Complete natural-language proof:

1. The preceding compact-support theorem identifies Fix(sfr) with s(K). Thus the
named theorem certifies the specified map's admissibility, and the defined integer
is exactly Dold's canonical Euclidean index. If W contains K, excision from r⁻¹(U)
to r⁻¹(W) proves the first formula. In the locally compact metrizable case one
can choose W with compact closure inside U by a finite union of relatively compact
neighborhoods of the compact K. This recovers the precise localized Granas formula;
the stronger excision formula here needs no closure or image compactness assumption.

2. For completeness, the source commutativity argument has the following actual
domains. Let a:A⊆ℝᵖ→ℝᑫ and b:B⊆ℝᑫ→ℝᵖ be continuous, and assume the composite
fixed loci are compact. On A×B put φ(x,y)=(b(y),a(x)). Its fixed set is the compact
graph of Fix(ba). On (A∩a⁻¹B)×B use
h_t=(t b(a(x))+(1-t)b(y),a(x)); on A×(B∩b⁻¹A) use
h'_t=(b(y),t a(b(y))+(1-t)a(x)). The fixed equations force y=a(x),x=b(y)
at every t, so both total fixed sets are this graph times [0,1], compact.
Excision and Euclidean admissible homotopy give I(φ)=I(h₁)=I(h'₁).
Extend h₁ to (A∩a⁻¹B)×ℝᑫ and deform it by
H_t=(ba(x),(1-t)a(x)). Its total fixed locus is the compact image of
Fix(ba)×[0,1] under (x,t)↦(x,(1-t)a(x),t). At t=0 its fixed set is in
the original domain, so excision applies. At t=1 use product multiplicativity
and the full-space constant-zero index 1 to get I(ba). The analogous deformation
((1-t)b(y),ab(y)) yields I(ab). This is Dold (1.8), pp.2–3, and the actual
Granas8.1.1–8.1.6 argument; the composite-domain and total-support checks above
spell out the source's omitted admissibility details. No invariant domain is assumed.

3. For representations (s,r),(s',r'), take a=s'fr on D=r⁻¹(U) and b=sr'
on the whole second Euclidean representation domain V'. Then a(D)⊆V',
b⁻¹(D)=r'⁻¹(U), ba=sfr and ab=s'fr'. Their fixed sets are s(K),s'(K),
compact by the first step. Apply commutativity to obtain representation independence.
This is precisely Dold2.3 and Granas10.1.1, including the whole-domain guard on b.

4. Restriction to any open neighborhood of K corresponds to Euclidean excision;
the restricted fixed set is compact by lifting K through the domain inclusion.
For a finite disjoint open cover Vᵢ of K, each fixed piece is closed in K,
since its complement is the union of the other pieces. Its lift into Vᵢ is compact.
Their inverse-image domains are disjoint, cover the retracted fixed support, and
Euclidean additivity gives the sum. The empty fixed set gives zero directly.

5. For H on U×[0,1], assume the TOTAL fixed locus is compact. Its projection
to U is compact, and each endpoint fixed set is compact by intersection with a
closed time slice and projection. The retracted homotopy's total fixed locus is
the continuous image (x,t)↦(s(x),t) of the original total fixed locus.
Euclidean admissible homotopy gives the equality. Slice compactness alone does
not suffice, because fixed points could escape through the boundary of U.

6. Given a homeomorphism h:X→Y, transport the representation by s_Y=s h⁻¹,
r_Y=h r. Its identity r_Y s_Y=id is immediate; its retracted conjugate and
domain are literally the original sfr and r⁻¹(U). Representation independence
therefore gives equality for any representation of Y. The conjugate fixed set
is the continuous image of K under the induced domain homeomorphism, hence compact.
Applying this to any isolating open neighborhood gives the isolated local-index
conclusion with no differentiability hypothesis on h. Dold2.4 also permits
codomain localization: shrink W about an isolated fixed point inside a chart O
so that W and f(W) lie in O; use the restricted representation on r⁻¹(O).
The retracted map on r⁻¹(W) is unchanged, so the chart computes that same local index.

7. For the Euclidean identity representation the retracted domain identifies
with U by the identity on coordinates and the retracted map is exactly f.
Thus the canonical supported orientation and displacement map are the original
ones, proving the last normalization. This also covers ℝ⁰: its ordinary finite
point class gives the point index1. Empty spaces have empty fixed support and
index0. Representation independence handles orientation-reversing choices;
it never asserts a false conjugacy formula for displacement maps.
-/
theorem enr_local_fixed_point_index_conjugacy
    (X : Type u) [TopologicalSpace X] [MetrizableSpace X] [LocallyCompactSpace X]
    (e : ENRRepresentation X) :
    (∀ (U : Opens X) (f : C(U, X)) (hK : IsCompact (enrLocalFixedSet f)),
      ∀ (W : Opens X) (hWU : W ≤ U),
        (∀ x : U, f x = x.1 → x.1 ∈ W) →
        ∃ hWK : IsCompact (euclideanFixedSet (enrEuclideanLocalMap e U W hWU f)),
          enrLocalFixedPointIndex e U f hK =
            euclideanFixedPointIndex (enrEuclideanLocalMap e U W hWU f) hWK) ∧
    (∀ (e' : ENRRepresentation X) (U : Opens X) (f : C(U, X))
        (hK : IsCompact (enrLocalFixedSet f)),
      enrLocalFixedPointIndex e U f hK = enrLocalFixedPointIndex e' U f hK) ∧
    (∀ (U V : Opens X) (hVU : V ≤ U) (f : C(U, X))
        (hK : IsCompact (enrLocalFixedSet f)),
      (∀ x : U, f x = x.1 → x.1 ∈ V) →
        ∃ hV : IsCompact (enrLocalFixedSet (enrRestrictLocalMap f V hVU)),
          enrLocalFixedPointIndex e U f hK =
            enrLocalFixedPointIndex e V (enrRestrictLocalMap f V hVU) hV) ∧
    (∀ (U : Opens X) (f : C(U, X)) (hK : IsCompact (enrLocalFixedSet f)),
      enrLocalFixedSet f = ∅ → enrLocalFixedPointIndex e U f hK = 0) ∧
    (∀ (U : Opens X) (f : C(U, X)) (hK : IsCompact (enrLocalFixedSet f))
        (k : ℕ) (V : Fin k → Opens X) (hVU : ∀ i, V i ≤ U),
      Pairwise (fun i j ↦ Disjoint (V i : Set X) (V j : Set X)) →
      (∀ x : U, f x = x.1 → ∃ i, x.1 ∈ V i) →
        ∃ hV : ∀ i, IsCompact (enrLocalFixedSet (enrRestrictLocalMap f (V i) (hVU i))),
          enrLocalFixedPointIndex e U f hK =
            ∑ i, enrLocalFixedPointIndex e (V i)
              (enrRestrictLocalMap f (V i) (hVU i)) (hV i)) ∧
    (∀ (U : Opens X) (H : C(U × unitInterval, X)),
      IsCompact {p : U × unitInterval | H p = p.1.1} →
        ∃ (h0 : IsCompact (enrLocalFixedSet (enrHomotopySlice H 0)))
          (h1 : IsCompact (enrLocalFixedSet (enrHomotopySlice H 1))),
          enrLocalFixedPointIndex e U (enrHomotopySlice H 0) h0 =
            enrLocalFixedPointIndex e U (enrHomotopySlice H 1) h1) ∧
    (∀ (Y : Type v) [TopologicalSpace Y] [MetrizableSpace Y] [LocallyCompactSpace Y]
        (eY : ENRRepresentation Y) (h : X ≃ₜ Y) (U : Opens X) (f : C(U, X))
        (hK : IsCompact (enrLocalFixedSet f)),
      ∃ hY : IsCompact (enrLocalFixedSet (enrConjugateLocalMap h U f)),
        enrLocalFixedPointIndex eY (enrConjugateDomain h U)
          (enrConjugateLocalMap h U f) hY = enrLocalFixedPointIndex e U f hK) ∧
    (∀ (n : ℕ) (U : Opens (Euclidean n)) (f : C(U, Euclidean n))
        (hK : IsCompact (euclideanFixedSet f)),
      enrLocalFixedPointIndex (euclideanENRRepresentation n) U f hK =
        euclideanFixedPointIndex f hK) := by
  have hb := HolomorphicAnosov.euclidean_fixed_point_index_basic_laws
  dsimp at hb
  have hrepr : ∀ (e' : ENRRepresentation X) (U : Opens X) (f : C(U, X))
      (hK : IsCompact (enrLocalFixedSet f)),
      enrLocalFixedPointIndex e U f hK = enrLocalFixedPointIndex e' U f hK := by
    intro e' U f hK
    let D := enrRetractedOpenDomain e U
    let D' := enrRetractedOpenDomain e' U
    let a : C(D, e'.domain) :=
      e'.sectionMap.comp (f.comp (retractedDomainToLocalDomain e U U le_rfl))
    let b : C(e'.domain, e.domain) := e.sectionMap.comp e'.retraction
    have hret (y : e'.domain) : e.retraction (b y) = e'.retraction y := by
      exact e.retraction_section (e'.retraction y)
    have hdomain (y : e'.domain) :
        (b y).1 ∈ D ↔ e'.retraction y ∈ (U : Set X) := by
      change (∃ hz : (b y).1 ∈ e.domain,
        e.retraction ⟨(b y).1, hz⟩ ∈ (U : Set X)) ↔ _
      constructor
      · rintro ⟨hz, hy⟩
        have heq : (⟨(b y).1, hz⟩ : e.domain) = b y := Subtype.ext rfl
        rw [heq, hret] at hy
        exact hy
      · intro hy
        exact ⟨(b y).2, by simpa only [hret] using hy⟩
    let V' : Opens (Euclidean e'.dimension) := ⟨e'.domain, e'.domain_open⟩
    let aAmbient : C(D, Euclidean e'.dimension) :=
      (⟨Subtype.val, continuous_subtype_val⟩ : C(e'.domain, Euclidean e'.dimension)).comp a
    let bAmbient : C(V', Euclidean e.dimension) :=
      (⟨Subtype.val, continuous_subtype_val⟩ : C(e.domain, Euclidean e.dimension)).comp b
    have hfirstDomain :
        Subtype.val '' (aAmbient ⁻¹' (V' : Set (Euclidean e'.dimension))) =
          (D : Set (Euclidean e.dimension)) := by
      ext x
      constructor
      · rintro ⟨z, hz, rfl⟩
        exact z.2
      · intro hx
        exact ⟨⟨x, hx⟩, (a ⟨x, hx⟩).2, rfl⟩
    have hsecondDomain :
        Subtype.val '' (bAmbient ⁻¹' (D : Set (Euclidean e.dimension))) =
          (D' : Set (Euclidean e'.dimension)) := by
      ext y
      constructor
      · rintro ⟨z, hz, rfl⟩
        exact ⟨z.2, (hdomain z).1 hz⟩
      · rintro ⟨hy, hret'⟩
        exact ⟨⟨y, hy⟩, (hdomain ⟨y, hy⟩).2 hret', rfl⟩
    let bD : C(D', D) :=
      ⟨fun y ↦ ⟨(b (retractedDomainInclusion e' U y)).1,
        (hdomain _).2 y.2.choose_spec⟩,
        (continuous_subtype_val.comp
          (b.continuous.comp (retractedDomainInclusion e' U).continuous)).subtype_mk _⟩
    let ba : C(D, Euclidean e.dimension) :=
      (⟨Subtype.val, continuous_subtype_val⟩ : C(e.domain, Euclidean e.dimension)).comp
        (b.comp a)
    let ab : C(D', Euclidean e'.dimension) :=
      (⟨Subtype.val, continuous_subtype_val⟩ : C(e'.domain, Euclidean e'.dimension)).comp
        (a.comp bD)
    have hba : ba = enrEuclideanLocalMap e U U le_rfl f := by
      apply ContinuousMap.ext
      intro x
      change (e.sectionMap (e'.retraction
        (e'.sectionMap (f (retractedDomainToLocalDomain e U U le_rfl x))))).1 = _
      rw [e'.retraction_section]
      rfl
    have hab : ab = enrEuclideanLocalMap e' U U le_rfl f := by
      apply ContinuousMap.ext
      intro y
      have hincl : retractedDomainInclusion e U (bD y) =
          b (retractedDomainInclusion e' U y) := Subtype.ext rfl
      have hlocal : retractedDomainToLocalDomain e U U le_rfl (bD y) =
          retractedDomainToLocalDomain e' U U le_rfl y := by
        apply Subtype.ext
        change e.retraction (retractedDomainInclusion e U (bD y)) = _
        rw [hincl, hret]
        rfl
      change (e'.sectionMap (f (retractedDomainToLocalDomain e U U le_rfl (bD y)))).1 = _
      rw [hlocal]
      rfl
    have hbaK : IsCompact (euclideanFixedSet ba) := by
      rw [hba]
      exact enrRetractedLocalMap_compact_fixedSet e U U le_rfl f hK (fun x _ ↦ x.2)
    have habK : IsCompact (euclideanFixedSet ab) := by
      rw [hab]
      exact enrRetractedLocalMap_compact_fixedSet e' U U le_rfl f hK (fun x _ ↦ x.2)
    let ep := EuclideanSpace.finAddEquivProd (𝕜 := ℝ)
      (n := e.dimension) (m := e'.dimension)
    let P : Opens (Euclidean (e.dimension + e'.dimension)) :=
      ⟨ep ⁻¹' ((D : Set _) ×ˢ (V' : Set _)),
        (D.isOpen.prod V'.isOpen).preimage ep.continuous⟩
    let iD : C(P, D) :=
      ⟨fun z ↦ ⟨(ep z.1).1, z.2.1⟩,
        (ep.continuous.comp continuous_subtype_val).fst.subtype_mk _⟩
    let iV : C(P, V') :=
      ⟨fun z ↦ ⟨(ep z.1).2, z.2.2⟩,
        (ep.continuous.comp continuous_subtype_val).snd.subtype_mk _⟩
    let phi : C(P, Euclidean (e.dimension + e'.dimension)) :=
      ⟨fun z ↦ ep.symm (bAmbient (iV z), aAmbient (iD z)),
        ep.symm.continuous.comp ((bAmbient.continuous.comp iV.continuous).prodMk
          (aAmbient.continuous.comp iD.continuous))⟩
    let Kba := euclideanFixedSet ba
    let kD : C(Kba, D) := ⟨Subtype.val, continuous_subtype_val⟩
    let graphAmbient : C(Kba, Euclidean (e.dimension + e'.dimension)) :=
      ⟨fun x ↦ ep.symm (x.1.1, aAmbient x.1),
        ep.symm.continuous.comp
          ((continuous_subtype_val.comp kD.continuous).prodMk
            (aAmbient.continuous.comp kD.continuous))⟩
    have hgraphMem (x : Kba) : graphAmbient x ∈ P := by
      change (ep (ep.symm (x.1.1, aAmbient x.1))).1 ∈ D ∧
        (ep (ep.symm (x.1.1, aAmbient x.1))).2 ∈ V'
      rw [ep.apply_symm_apply]
      exact ⟨x.1.2, (a x.1).2⟩
    let graph : C(Kba, P) :=
      ⟨fun x ↦ ⟨graphAmbient x, hgraphMem x⟩,
        graphAmbient.continuous.subtype_mk hgraphMem⟩
    have hgraph : euclideanFixedSet phi = graph '' (Set.univ : Set Kba) := by
      ext z
      constructor
      · intro hz
        have hcoord : (bAmbient (iV z), aAmbient (iD z)) = ep z.1 := by
          simpa only [phi, ContinuousMap.coe_mk, ep.apply_symm_apply] using congrArg ep hz
        have hbx : bAmbient (iV z) = (iD z).1 := congrArg Prod.fst hcoord
        have hay : a (iD z) = iV z := by
          apply Subtype.ext
          exact congrArg Prod.snd hcoord
        have hfix : ba (iD z) = (iD z).1 := by
          change bAmbient (a (iD z)) = (iD z).1
          rw [hay]
          exact hbx
        refine ⟨⟨iD z, hfix⟩, Set.mem_univ _, ?_⟩
        apply Subtype.ext
        apply ep.injective
        change ep (ep.symm ((iD z).1, aAmbient (iD z))) = ep z.1
        rw [ep.apply_symm_apply, ← hbx]
        exact hcoord
      · rintro ⟨x, -, rfl⟩
        have hiD : iD (graph x) = x.1 := by
          apply Subtype.ext
          exact congrArg Prod.fst (ep.apply_symm_apply (x.1.1, aAmbient x.1))
        have hiV : iV (graph x) = a x.1 := by
          apply Subtype.ext
          exact congrArg Prod.snd (ep.apply_symm_apply (x.1.1, aAmbient x.1))
        change ep.symm (bAmbient (iV (graph x)), aAmbient (iD (graph x))) =
          ep.symm (x.1.1, aAmbient x.1)
        rw [hiD, hiV]
        have hfix : bAmbient (a x.1) = x.1.1 := x.2
        rw [hfix]
    have hphiK : IsCompact (euclideanFixedSet phi) := by
      let : CompactSpace Kba := isCompact_iff_compactSpace.mp hbaK
      rw [hgraph]
      exact IsCompact.image isCompact_univ graph.continuous
    let triangular : C(P, Euclidean (e.dimension + e'.dimension)) :=
      ⟨fun z ↦ ep.symm (ba (iD z), aAmbient (iD z)),
        ep.symm.continuous.comp ((ba.continuous.comp iD.continuous).prodMk
          (aAmbient.continuous.comp iD.continuous))⟩
    let Hgraph : C(P × unitInterval, Euclidean (e.dimension + e'.dimension)) :=
      ⟨fun w ↦ ep.symm ((w.2 : ℝ) • ba (iD w.1) +
          (1 - (w.2 : ℝ)) • bAmbient (iV w.1), aAmbient (iD w.1)), by
        apply ep.symm.continuous.comp
        apply Continuous.prodMk
        · exact ((continuous_subtype_val.comp continuous_snd).smul
              (ba.continuous.comp (iD.continuous.comp continuous_fst))).add
            ((continuous_const.sub (continuous_subtype_val.comp continuous_snd)).smul
              (bAmbient.continuous.comp (iV.continuous.comp continuous_fst)))
        · exact aAmbient.continuous.comp (iD.continuous.comp continuous_fst)⟩
    have hHgraphSet : {w : P × unitInterval | Hgraph w = w.1.1} =
        euclideanFixedSet phi ×ˢ (Set.univ : Set unitInterval) := by
      ext w
      change (Hgraph w = w.1.1) ↔ (phi w.1 = w.1.1 ∧ True)
      rw [and_true]
      have hcancel (v : Euclidean e.dimension) :
          (w.2 : ℝ) • v + (1 - (w.2 : ℝ)) • v = v := by
        rw [← add_smul]
        have ht : (w.2 : ℝ) + (1 - (w.2 : ℝ)) = 1 := by ring
        rw [ht, one_smul]
      constructor
      · intro hw
        have hc : ((w.2 : ℝ) • ba (iD w.1) +
            (1 - (w.2 : ℝ)) • bAmbient (iV w.1), aAmbient (iD w.1)) = ep w.1.1 := by
          simpa only [Hgraph, ContinuousMap.coe_mk, ep.apply_symm_apply] using congrArg ep hw
        have hay : a (iD w.1) = iV w.1 := by
          apply Subtype.ext
          exact congrArg Prod.snd hc
        have hba' : ba (iD w.1) = bAmbient (iV w.1) := by
          change bAmbient (a (iD w.1)) = _
          rw [hay]
        rw [hba', hcancel] at hc
        apply ep.injective
        change ep (ep.symm (bAmbient (iV w.1), aAmbient (iD w.1))) = ep w.1.1
        rw [ep.apply_symm_apply]
        exact hc
      · intro hw
        have hc : (bAmbient (iV w.1), aAmbient (iD w.1)) = ep w.1.1 := by
          simpa only [phi, ContinuousMap.coe_mk, ep.apply_symm_apply] using congrArg ep hw
        have hay : a (iD w.1) = iV w.1 := by
          apply Subtype.ext
          exact congrArg Prod.snd hc
        have hba' : ba (iD w.1) = bAmbient (iV w.1) := by
          change bAmbient (a (iD w.1)) = _
          rw [hay]
        apply ep.injective
        change ep (ep.symm ((w.2 : ℝ) • ba (iD w.1) +
          (1 - (w.2 : ℝ)) • bAmbient (iV w.1), aAmbient (iD w.1))) = ep w.1.1
        rw [ep.apply_symm_apply, hba', hcancel]
        exact hc
    have hHgraphK : IsCompact {w : P × unitInterval | Hgraph w = w.1.1} := by
      rw [hHgraphSet]
      exact hphiK.prod isCompact_univ
    obtain ⟨hgraph0, hgraph1, hgraphIndex⟩ :=
      hb.2.1 (e.dimension + e'.dimension) P Hgraph hHgraphK
    have hgraph0Map :
        Hgraph.comp ⟨fun z ↦ (z, 0), continuous_id.prodMk continuous_const⟩ = phi := by
      apply ContinuousMap.ext
      intro z
      simp [Hgraph, phi]
    have hgraph1Map :
        Hgraph.comp ⟨fun z ↦ (z, 1), continuous_id.prodMk continuous_const⟩ = triangular := by
      apply ContinuousMap.ext
      intro z
      simp [Hgraph, triangular]
    have htriK : IsCompact (euclideanFixedSet triangular) := by
      rw [← hgraph1Map]
      exact hgraph1
    have hphiTri : euclideanFixedPointIndex phi hphiK =
        euclideanFixedPointIndex triangular htriK := by
      simpa only [hgraph0Map, hgraph1Map] using hgraphIndex
    let Q : Opens (Euclidean (e.dimension + e'.dimension)) :=
      ⟨ep ⁻¹' ((D : Set _) ×ˢ (Set.univ : Set (Euclidean e'.dimension))),
        (D.isOpen.prod isOpen_univ).preimage ep.continuous⟩
    let qD : C(Q, D) :=
      ⟨fun z ↦ ⟨(ep z.1).1, z.2.1⟩,
        (ep.continuous.comp continuous_subtype_val).fst.subtype_mk _⟩
    let extended : C(Q, Euclidean (e.dimension + e'.dimension)) :=
      ⟨fun z ↦ ep.symm (ba (qD z), aAmbient (qD z)),
        ep.symm.continuous.comp ((ba.continuous.comp qD.continuous).prodMk
          (aAmbient.continuous.comp qD.continuous))⟩
    have hPQ : P ≤ Q := fun _ hz ↦ ⟨hz.1, Set.mem_univ _⟩
    let jPQ : C(P, Q) :=
      ⟨fun z ↦ ⟨z.1, hPQ z.2⟩, continuous_subtype_val.subtype_mk _⟩
    have hextSet : euclideanFixedSet extended =
        jPQ '' euclideanFixedSet triangular := by
      ext z
      constructor
      · intro hz
        have hc : (ba (qD z), aAmbient (qD z)) = ep z.1 := by
          simpa only [extended, ContinuousMap.coe_mk, ep.apply_symm_apply] using congrArg ep hz
        have hy : (ep z.1).2 ∈ V' := by
          have hs := congrArg Prod.snd hc
          rw [← hs]
          exact (a (qD z)).2
        let zP : P := ⟨z.1, ⟨z.2.1, hy⟩⟩
        refine ⟨zP, ?_, ?_⟩
        · exact hz
        · exact Subtype.ext rfl
      · rintro ⟨z, hz, rfl⟩
        exact hz
    have hextK : IsCompact (euclideanFixedSet extended) := by
      rw [hextSet]
      exact htriK.image jPQ.continuous
    have hextCover : ∀ z ∈ euclideanFixedSet extended, z.1 ∈ P := by
      intro z hz
      rw [hextSet] at hz
      obtain ⟨w, hw, rfl⟩ := hz
      exact w.2
    obtain ⟨hresK, hresIndex⟩ :=
      (hb.1 (e.dimension + e'.dimension) Q extended hextK).1 P hPQ hextCover
    have htriExt : euclideanFixedPointIndex triangular htriK =
        euclideanFixedPointIndex extended hextK := by
      have hmap : (⟨fun z : P ↦ extended ⟨z.1, hPQ z.2⟩,
          extended.continuous.comp (continuous_subtype_val.subtype_mk _)⟩ :
          C(P, Euclidean (e.dimension + e'.dimension))) = triangular := by
        apply ContinuousMap.ext
        intro z
        rfl
      simpa only [hmap] using hresIndex
    let scaled : C(Q × unitInterval, Euclidean (e.dimension + e'.dimension)) :=
      ⟨fun w ↦ ep.symm (ba (qD w.1), (1 - (w.2 : ℝ)) • aAmbient (qD w.1)),
        ep.symm.continuous.comp
          ((ba.continuous.comp (qD.continuous.comp continuous_fst)).prodMk
            ((continuous_const.sub (continuous_subtype_val.comp continuous_snd)).smul
              (aAmbient.continuous.comp (qD.continuous.comp continuous_fst))))⟩
    let scaleAmbient : C(Kba × unitInterval, Euclidean (e.dimension + e'.dimension)) :=
      ⟨fun w ↦ ep.symm (w.1.1.1, (1 - (w.2 : ℝ)) • aAmbient w.1.1),
        ep.symm.continuous.comp
          ((continuous_subtype_val.comp (kD.continuous.comp continuous_fst)).prodMk
            ((continuous_const.sub (continuous_subtype_val.comp continuous_snd)).smul
              (aAmbient.continuous.comp (kD.continuous.comp continuous_fst))))⟩
    have hscaleMem (w : Kba × unitInterval) : scaleAmbient w ∈ Q := by
      change (ep (ep.symm (w.1.1.1, (1 - (w.2 : ℝ)) • aAmbient w.1.1))).1 ∈ D ∧ _
      rw [ep.apply_symm_apply]
      exact ⟨w.1.1.2, Set.mem_univ _⟩
    let scaleGraph : C(Kba × unitInterval, Q × unitInterval) :=
      ⟨fun w ↦ (⟨scaleAmbient w, hscaleMem w⟩, w.2),
        (scaleAmbient.continuous.subtype_mk hscaleMem).prodMk continuous_snd⟩
    have hscaledSet : {w : Q × unitInterval | scaled w = w.1.1} =
        scaleGraph '' (Set.univ : Set (Kba × unitInterval)) := by
      ext w
      constructor
      · intro hw
        have hc : (ba (qD w.1), (1 - (w.2 : ℝ)) • aAmbient (qD w.1)) = ep w.1.1 := by
          simpa only [scaled, ContinuousMap.coe_mk, ep.apply_symm_apply] using congrArg ep hw
        have hx : ba (qD w.1) = (qD w.1).1 := congrArg Prod.fst hc
        refine ⟨(⟨qD w.1, hx⟩, w.2), Set.mem_univ _, ?_⟩
        apply Prod.ext
        · apply Subtype.ext
          apply ep.injective
          change ep (ep.symm ((qD w.1).1,
            (1 - (w.2 : ℝ)) • aAmbient (qD w.1))) = ep w.1.1
          rw [ep.apply_symm_apply, ← hx]
          exact hc
        · rfl
      · rintro ⟨w, -, rfl⟩
        have hqD : qD (scaleGraph w).1 = w.1.1 := by
          apply Subtype.ext
          exact congrArg Prod.fst
            (ep.apply_symm_apply (w.1.1.1, (1 - (w.2 : ℝ)) • aAmbient w.1.1))
        change ep.symm (ba (qD (scaleGraph w).1),
          (1 - (w.2 : ℝ)) • aAmbient (qD (scaleGraph w).1)) =
          ep.symm (w.1.1.1, (1 - (w.2 : ℝ)) • aAmbient w.1.1)
        rw [hqD, w.1.2]
    have hscaledK : IsCompact {w : Q × unitInterval | scaled w = w.1.1} := by
      let : CompactSpace Kba := isCompact_iff_compactSpace.mp hbaK
      rw [hscaledSet]
      exact isCompact_univ.image scaleGraph.continuous
    obtain ⟨hs0, hs1, hsIndex⟩ :=
      hb.2.1 (e.dimension + e'.dimension) Q scaled hscaledK
    let baZero : C(Q, Euclidean (e.dimension + e'.dimension)) :=
      ⟨fun z ↦ ep.symm (ba (qD z), 0),
        ep.symm.continuous.comp ((ba.continuous.comp qD.continuous).prodMk continuous_const)⟩
    have hs0Map :
        scaled.comp ⟨fun z ↦ (z, 0), continuous_id.prodMk continuous_const⟩ = extended := by
      apply ContinuousMap.ext
      intro z
      simp [scaled, extended]
    have hs1Map :
        scaled.comp ⟨fun z ↦ (z, 1), continuous_id.prodMk continuous_const⟩ = baZero := by
      apply ContinuousMap.ext
      intro z
      simp [scaled, baZero]
    have hbaZeroK : IsCompact (euclideanFixedSet baZero) := by
      rw [← hs1Map]
      exact hs1
    have hextZero : euclideanFixedPointIndex extended hextK =
        euclideanFixedPointIndex baZero hbaZeroK := by
      simpa only [hs0Map, hs1Map] using hsIndex
    obtain ⟨hcZero, hiZero⟩ := hb.2.2.2.1 e'.dimension ⊤ 0 (Set.mem_univ _)
    obtain ⟨hprodK, hprodIndex⟩ := hb.2.2.1 e.dimension e'.dimension D ⊤ ba
      (ContinuousMap.const (⊤ : Opens (Euclidean e'.dimension)) 0) hbaK hcZero
    have hprodBa : euclideanFixedPointIndex baZero hbaZeroK =
        euclideanFixedPointIndex ba hbaK := by
      rw [hiZero, mul_one] at hprodIndex
      exact hprodIndex
    have hphiBa : euclideanFixedPointIndex phi hphiK =
        euclideanFixedPointIndex ba hbaK :=
      hphiTri.trans (htriExt.trans (hextZero.trans hprodBa))
    let R : Opens (Euclidean (e.dimension + e'.dimension)) :=
      ⟨ep ⁻¹' ((D : Set _) ×ˢ (D' : Set _)),
        (D.isOpen.prod D'.isOpen).preimage ep.continuous⟩
    have hRP : R ≤ P := fun _ hz ↦ ⟨hz.1, hz.2.choose⟩
    let jRP : C(R, P) :=
      ⟨fun z ↦ ⟨z.1, hRP z.2⟩, continuous_subtype_val.subtype_mk _⟩
    let rD : C(R, D) :=
      ⟨fun z ↦ ⟨(ep z.1).1, z.2.1⟩,
        (ep.continuous.comp continuous_subtype_val).fst.subtype_mk _⟩
    let rD' : C(R, D') :=
      ⟨fun z ↦ ⟨(ep z.1).2, z.2.2⟩,
        (ep.continuous.comp continuous_subtype_val).snd.subtype_mk _⟩
    let phiR := phi.comp jRP
    have hphiCover : ∀ z ∈ euclideanFixedSet phi, z.1 ∈ R := by
      intro z hz
      have hc : (bAmbient (iV z), aAmbient (iD z)) = ep z.1 := by
        simpa only [phi, ContinuousMap.coe_mk, ep.apply_symm_apply] using congrArg ep hz
      have hbx : bAmbient (iV z) = (iD z).1 := congrArg Prod.fst hc
      have hy : e'.retraction (iV z) ∈ U := by
        apply (hdomain (iV z)).1
        change bAmbient (iV z) ∈ D
        rw [hbx]
        exact (iD z).2
      exact ⟨z.2.1, (iV z).2, hy⟩
    obtain ⟨hphiRK, hphiRIndex⟩ :=
      (hb.1 (e.dimension + e'.dimension) P phi hphiK).1 R hRP hphiCover
    have hphiRK' : IsCompact (euclideanFixedSet phiR) := hphiRK
    have hphiR : euclideanFixedPointIndex phiR hphiRK' =
        euclideanFixedPointIndex phi hphiK := hphiRIndex
    let triangularR : C(R, Euclidean (e.dimension + e'.dimension)) :=
      ⟨fun z ↦ ep.symm ((bD (rD' z)).1, ab (rD' z)),
        ep.symm.continuous.comp
          ((continuous_subtype_val.comp (bD.continuous.comp rD'.continuous)).prodMk
            (ab.continuous.comp rD'.continuous))⟩
    let Hright : C(R × unitInterval, Euclidean (e.dimension + e'.dimension)) :=
      ⟨fun w ↦ ep.symm ((bD (rD' w.1)).1,
        (w.2 : ℝ) • ab (rD' w.1) + (1 - (w.2 : ℝ)) • aAmbient (rD w.1)),
        ep.symm.continuous.comp
          ((continuous_subtype_val.comp
            (bD.continuous.comp (rD'.continuous.comp continuous_fst))).prodMk
            (((continuous_subtype_val.comp continuous_snd).smul
              (ab.continuous.comp (rD'.continuous.comp continuous_fst))).add
              ((continuous_const.sub (continuous_subtype_val.comp continuous_snd)).smul
                (aAmbient.continuous.comp (rD.continuous.comp continuous_fst)))))⟩
    have hHrightSet : {w : R × unitInterval | Hright w = w.1.1} =
        euclideanFixedSet phiR ×ˢ (Set.univ : Set unitInterval) := by
      ext w
      change (Hright w = w.1.1) ↔ (phiR w.1 = w.1.1 ∧ True)
      rw [and_true]
      have hcancel (v : Euclidean e'.dimension) :
          (w.2 : ℝ) • v + (1 - (w.2 : ℝ)) • v = v := by
        rw [← add_smul]
        have ht : (w.2 : ℝ) + (1 - (w.2 : ℝ)) = 1 := by ring
        rw [ht, one_smul]
      constructor
      · intro hw
        have hc : ((bD (rD' w.1)).1,
            (w.2 : ℝ) • ab (rD' w.1) + (1 - (w.2 : ℝ)) • aAmbient (rD w.1)) = ep w.1.1 := by
          simpa only [Hright, ContinuousMap.coe_mk, ep.apply_symm_apply] using congrArg ep hw
        have hbx : bD (rD' w.1) = rD w.1 := by
          apply Subtype.ext
          exact congrArg Prod.fst hc
        have hab' : ab (rD' w.1) = aAmbient (rD w.1) := by
          change aAmbient (bD (rD' w.1)) = _
          rw [hbx]
        rw [hab', hcancel] at hc
        apply ep.injective
        change ep (ep.symm ((bD (rD' w.1)).1, aAmbient (rD w.1))) = ep w.1.1
        rw [ep.apply_symm_apply]
        exact hc
      · intro hw
        have hc : ((bD (rD' w.1)).1, aAmbient (rD w.1)) = ep w.1.1 := by
          change ep.symm ((bD (rD' w.1)).1, aAmbient (rD w.1)) = w.1.1 at hw
          simpa only [ep.apply_symm_apply] using congrArg ep hw
        have hbx : bD (rD' w.1) = rD w.1 := by
          apply Subtype.ext
          exact congrArg Prod.fst hc
        have hab' : ab (rD' w.1) = aAmbient (rD w.1) := by
          change aAmbient (bD (rD' w.1)) = _
          rw [hbx]
        apply ep.injective
        change ep (ep.symm ((bD (rD' w.1)).1,
          (w.2 : ℝ) • ab (rD' w.1) + (1 - (w.2 : ℝ)) • aAmbient (rD w.1))) = ep w.1.1
        rw [ep.apply_symm_apply, hab', hcancel]
        exact hc
    have hHrightK : IsCompact {w : R × unitInterval | Hright w = w.1.1} := by
      rw [hHrightSet]
      exact hphiRK'.prod isCompact_univ
    obtain ⟨hr0, hr1, hrIndex⟩ :=
      hb.2.1 (e.dimension + e'.dimension) R Hright hHrightK
    have hr0Map :
        Hright.comp ⟨fun z ↦ (z, 0), continuous_id.prodMk continuous_const⟩ = phiR := by
      apply ContinuousMap.ext
      intro z
      change ep.symm ((bD (rD' z)).1, (0 : ℝ) • ab (rD' z) +
        (1 - (0 : ℝ)) • aAmbient (rD z)) =
        ep.symm ((bD (rD' z)).1, aAmbient (rD z))
      simp
    have hr1Map :
        Hright.comp ⟨fun z ↦ (z, 1), continuous_id.prodMk continuous_const⟩ = triangularR := by
      apply ContinuousMap.ext
      intro z
      simp [Hright, triangularR]
    have htriRK : IsCompact (euclideanFixedSet triangularR) := by
      rw [← hr1Map]
      exact hr1
    have hphiRTri : euclideanFixedPointIndex phiR hphiRK' =
        euclideanFixedPointIndex triangularR htriRK := by
      simpa only [hr0Map, hr1Map] using hrIndex
    let S : Opens (Euclidean (e.dimension + e'.dimension)) :=
      ⟨ep ⁻¹' ((Set.univ : Set (Euclidean e.dimension)) ×ˢ (D' : Set _)),
        (isOpen_univ.prod D'.isOpen).preimage ep.continuous⟩
    let sD' : C(S, D') :=
      ⟨fun z ↦ ⟨(ep z.1).2, z.2.2⟩,
        (ep.continuous.comp continuous_subtype_val).snd.subtype_mk _⟩
    let extendedR : C(S, Euclidean (e.dimension + e'.dimension)) :=
      ⟨fun z ↦ ep.symm ((bD (sD' z)).1, ab (sD' z)),
        ep.symm.continuous.comp
          ((continuous_subtype_val.comp (bD.continuous.comp sD'.continuous)).prodMk
            (ab.continuous.comp sD'.continuous))⟩
    have hRS : R ≤ S := fun _ hz ↦ ⟨Set.mem_univ _, hz.2⟩
    let jRS : C(R, S) :=
      ⟨fun z ↦ ⟨z.1, hRS z.2⟩, continuous_subtype_val.subtype_mk _⟩
    have hextRSet : euclideanFixedSet extendedR =
        jRS '' euclideanFixedSet triangularR := by
      ext z
      constructor
      · intro hz
        have hc : ((bD (sD' z)).1, ab (sD' z)) = ep z.1 := by
          simpa only [extendedR, ContinuousMap.coe_mk, ep.apply_symm_apply] using congrArg ep hz
        have hx : (ep z.1).1 ∈ D := by
          have hs := congrArg Prod.fst hc
          rw [← hs]
          exact (bD (sD' z)).2
        let zR : R := ⟨z.1, ⟨hx, z.2.2⟩⟩
        exact ⟨zR, hz, Subtype.ext rfl⟩
      · rintro ⟨z, hz, rfl⟩
        exact hz
    have hextRK : IsCompact (euclideanFixedSet extendedR) := by
      rw [hextRSet]
      exact htriRK.image jRS.continuous
    have hextRCover : ∀ z ∈ euclideanFixedSet extendedR, z.1 ∈ R := by
      intro z hz
      rw [hextRSet] at hz
      obtain ⟨w, hw, rfl⟩ := hz
      exact w.2
    obtain ⟨hresRK, hresRIndex⟩ :=
      (hb.1 (e.dimension + e'.dimension) S extendedR hextRK).1 R hRS hextRCover
    have htriRExt : euclideanFixedPointIndex triangularR htriRK =
        euclideanFixedPointIndex extendedR hextRK := by
      have hmap : (⟨fun z : R ↦ extendedR ⟨z.1, hRS z.2⟩,
          extendedR.continuous.comp (continuous_subtype_val.subtype_mk _)⟩ :
          C(R, Euclidean (e.dimension + e'.dimension))) = triangularR := by
        apply ContinuousMap.ext
        intro z
        rfl
      simpa only [hmap] using hresRIndex
    let scaledR : C(S × unitInterval, Euclidean (e.dimension + e'.dimension)) :=
      ⟨fun w ↦ ep.symm ((1 - (w.2 : ℝ)) • (bD (sD' w.1)).1, ab (sD' w.1)),
        ep.symm.continuous.comp
          (((continuous_const.sub (continuous_subtype_val.comp continuous_snd)).smul
            (continuous_subtype_val.comp
              (bD.continuous.comp (sD'.continuous.comp continuous_fst)))).prodMk
            (ab.continuous.comp (sD'.continuous.comp continuous_fst)))⟩
    let Kab := euclideanFixedSet ab
    let kD' : C(Kab, D') := ⟨Subtype.val, continuous_subtype_val⟩
    let scaleRAmbient : C(Kab × unitInterval, Euclidean (e.dimension + e'.dimension)) :=
      ⟨fun w ↦ ep.symm ((1 - (w.2 : ℝ)) • (bD w.1.1).1, w.1.1.1),
        ep.symm.continuous.comp
          (((continuous_const.sub (continuous_subtype_val.comp continuous_snd)).smul
            (continuous_subtype_val.comp
              (bD.continuous.comp (kD'.continuous.comp continuous_fst)))).prodMk
            (continuous_subtype_val.comp (kD'.continuous.comp continuous_fst)))⟩
    have hscaleRMem (w : Kab × unitInterval) : scaleRAmbient w ∈ S := by
      change (ep (ep.symm ((1 - (w.2 : ℝ)) • (bD w.1.1).1, w.1.1.1))).1 ∈
        (Set.univ : Set (Euclidean e.dimension)) ∧
        (ep (ep.symm ((1 - (w.2 : ℝ)) • (bD w.1.1).1, w.1.1.1))).2 ∈ D'
      rw [ep.apply_symm_apply]
      exact ⟨Set.mem_univ _, w.1.1.2⟩
    let scaleRGraph : C(Kab × unitInterval, S × unitInterval) :=
      ⟨fun w ↦ (⟨scaleRAmbient w, hscaleRMem w⟩, w.2),
        (scaleRAmbient.continuous.subtype_mk hscaleRMem).prodMk continuous_snd⟩
    have hscaledRSet : {w : S × unitInterval | scaledR w = w.1.1} =
        scaleRGraph '' (Set.univ : Set (Kab × unitInterval)) := by
      ext w
      constructor
      · intro hw
        have hc : ((1 - (w.2 : ℝ)) • (bD (sD' w.1)).1, ab (sD' w.1)) = ep w.1.1 := by
          simpa only [scaledR, ContinuousMap.coe_mk, ep.apply_symm_apply] using congrArg ep hw
        have hy : ab (sD' w.1) = (sD' w.1).1 := congrArg Prod.snd hc
        refine ⟨(⟨sD' w.1, hy⟩, w.2), Set.mem_univ _, ?_⟩
        apply Prod.ext
        · apply Subtype.ext
          apply ep.injective
          change ep (ep.symm ((1 - (w.2 : ℝ)) • (bD (sD' w.1)).1,
            (sD' w.1).1)) = ep w.1.1
          rw [ep.apply_symm_apply, ← hy]
          exact hc
        · rfl
      · rintro ⟨w, -, rfl⟩
        have hsD : sD' (scaleRGraph w).1 = w.1.1 := by
          apply Subtype.ext
          exact congrArg Prod.snd
            (ep.apply_symm_apply ((1 - (w.2 : ℝ)) • (bD w.1.1).1, w.1.1.1))
        change ep.symm ((1 - (w.2 : ℝ)) • (bD (sD' (scaleRGraph w).1)).1,
          ab (sD' (scaleRGraph w).1)) =
          ep.symm ((1 - (w.2 : ℝ)) • (bD w.1.1).1, w.1.1.1)
        rw [hsD, w.1.2]
    have hscaledRK : IsCompact {w : S × unitInterval | scaledR w = w.1.1} := by
      let : CompactSpace Kab := isCompact_iff_compactSpace.mp habK
      rw [hscaledRSet]
      exact isCompact_univ.image scaleRGraph.continuous
    obtain ⟨hsr0, hsr1, hsrIndex⟩ :=
      hb.2.1 (e.dimension + e'.dimension) S scaledR hscaledRK
    let zeroAb : C(S, Euclidean (e.dimension + e'.dimension)) :=
      ⟨fun z ↦ ep.symm (0, ab (sD' z)),
        ep.symm.continuous.comp (continuous_const.prodMk (ab.continuous.comp sD'.continuous))⟩
    have hsr0Map :
        scaledR.comp ⟨fun z ↦ (z, 0), continuous_id.prodMk continuous_const⟩ = extendedR := by
      apply ContinuousMap.ext
      intro z
      simp [scaledR, extendedR]
    have hsr1Map :
        scaledR.comp ⟨fun z ↦ (z, 1), continuous_id.prodMk continuous_const⟩ = zeroAb := by
      apply ContinuousMap.ext
      intro z
      simp [scaledR, zeroAb]
    have hzeroAbK : IsCompact (euclideanFixedSet zeroAb) := by
      rw [← hsr1Map]
      exact hsr1
    have hextRZero : euclideanFixedPointIndex extendedR hextRK =
        euclideanFixedPointIndex zeroAb hzeroAbK := by
      simpa only [hsr0Map, hsr1Map] using hsrIndex
    obtain ⟨hcZeroR, hiZeroR⟩ := hb.2.2.2.1 e.dimension ⊤ 0 (Set.mem_univ _)
    obtain ⟨hprodRK, hprodRIndex⟩ := hb.2.2.1 e.dimension e'.dimension ⊤ D'
      (ContinuousMap.const (⊤ : Opens (Euclidean e.dimension)) 0) ab hcZeroR habK
    have hprodAb : euclideanFixedPointIndex zeroAb hzeroAbK =
        euclideanFixedPointIndex ab habK := by
      rw [hiZeroR, one_mul] at hprodRIndex
      exact hprodRIndex
    have hphiAb : euclideanFixedPointIndex phi hphiK =
        euclideanFixedPointIndex ab habK :=
      hphiR.symm.trans (hphiRTri.trans (htriRExt.trans (hextRZero.trans hprodAb)))
    suffices hcomm : euclideanFixedPointIndex ba hbaK = euclideanFixedPointIndex ab habK by
      unfold enrLocalFixedPointIndex enrRetractionIndex
      simpa only [hba, hab] using hcomm
    exact hphiBa.symm.trans hphiAb
  constructor
  · intro U f hK W hWU hcover
    have hcU := enrRetractedLocalMap_compact_fixedSet e U U le_rfl f hK (fun x _ ↦ x.2)
    have hWU' : enrRetractedOpenDomain e W ≤ enrRetractedOpenDomain e U := by
      intro v hv
      exact ⟨hv.choose, hWU hv.choose_spec⟩
    have hcover' : ∀ x : enrRetractedOpenDomain e U,
        enrEuclideanLocalMap e U U le_rfl f x = x.val →
          x.val ∈ enrRetractedOpenDomain e W := by
      intro v hv
      change enrEuclideanLocalMap e U U le_rfl f v = v.val at hv
      let x : U := ⟨e.retraction (retractedDomainInclusion e U v), v.property.choose_spec⟩
      have hv' : e.sectionMap (f x) = retractedDomainInclusion e U v := by
        apply Subtype.ext
        change (e.sectionMap (f (retractedDomainToLocalDomain e U U le_rfl v))).val = v.val
        exact hv
      have hxf : f x = x.1 := by
        have hr := congrArg e.retraction hv'
        rw [e.retraction_section] at hr
        simpa [x] using hr
      have hvdom : v.val ∈ e.domain := v.property.choose
      have hrv : e.retraction ⟨v.val, hvdom⟩ = x.1 := by
        have heq : (⟨v.val, hvdom⟩ : e.domain) = retractedDomainInclusion e U v := by
          apply Subtype.ext
          rfl
        rw [heq]
      exact ⟨hvdom, by
        rw [hrv]
        exact hcover x hxf⟩
    obtain ⟨hV, hidx⟩ := (hb.1 e.dimension (enrRetractedOpenDomain e U)
      (enrEuclideanLocalMap e U U le_rfl f) hcU).1
      (enrRetractedOpenDomain e W) hWU' hcover'
    refine ⟨?_, ?_⟩
    · have hV' : IsCompact (euclideanFixedSet (enrEuclideanLocalMap e U W hWU f)) := by
        convert hV using 1; try { ext z; rfl }
      exact hV'
    · unfold enrLocalFixedPointIndex enrRetractionIndex
      rw [← hidx]
      congr 1
  · constructor
    · exact hrepr
    · constructor
      · intro U V hVU f hK hcover
        let K : Set U := enrLocalFixedSet f
        let t : C(K, V) :=
          { toFun := fun x ↦ ⟨x.1, hcover x.1 x.2⟩
            continuous_toFun := by fun_prop }
        have hEq : enrLocalFixedSet (enrRestrictLocalMap f V hVU) =
            t '' (Set.univ : Set K) := by
          ext v
          constructor
          · intro hv
            let x : U := ⟨v.1, hVU v.2⟩
            have hxf : f x = x.1 := hv
            have hxK : x ∈ K := hxf
            have htx : t ⟨x, hxK⟩ = v := by
              apply Subtype.ext
              rfl
            exact ⟨⟨x, hxK⟩, Set.mem_univ _, htx⟩
          · rintro ⟨x, -, rfl⟩
            exact x.2
        let : CompactSpace K := isCompact_iff_compactSpace.mp hK
        have hKV : IsCompact (enrLocalFixedSet (enrRestrictLocalMap f V hVU)) := by
          rw [hEq]
          exact IsCompact.image isCompact_univ t.continuous
        have hU' := enrRetractedLocalMap_compact_fixedSet e U U le_rfl f hK
          (fun x _ ↦ x.2)
        have hV' := enrRetractedLocalMap_compact_fixedSet e V V le_rfl
          (enrRestrictLocalMap f V hVU) hKV (fun x _ ↦ x.2)
        have hWU : enrRetractedOpenDomain e V ≤ enrRetractedOpenDomain e U := by
          intro z hz
          exact ⟨hz.choose, hVU hz.choose_spec⟩
        have hcoverU : ∀ x : enrRetractedOpenDomain e U,
            enrEuclideanLocalMap e U U le_rfl f x = x.val →
              x.val ∈ enrRetractedOpenDomain e V := by
          intro z hz
          change enrEuclideanLocalMap e U U le_rfl f z = z.val at hz
          let x : U := ⟨e.retraction (retractedDomainInclusion e U z), z.property.choose_spec⟩
          have hz' : e.sectionMap (f x) = retractedDomainInclusion e U z := by
            apply Subtype.ext
            change (e.sectionMap (f (retractedDomainToLocalDomain e U U le_rfl z))).val = z.val
            exact hz
          have hxf : f x = x.1 := by
            have hr := congrArg e.retraction hz'
            rw [e.retraction_section] at hr
            simpa [x] using hr
          have hzdom : z.val ∈ e.domain := z.property.choose
          have hzr : e.retraction ⟨z.val, hzdom⟩ = x.1 := by
            have heq : (⟨z.val, hzdom⟩ : e.domain) = retractedDomainInclusion e U z := by
              apply Subtype.ext
              rfl
            rw [heq]
          exact ⟨hzdom, by rw [hzr]; exact hcover x hxf⟩
        obtain ⟨hriU, hiU⟩ := (hb.1 e.dimension (enrRetractedOpenDomain e U)
          (enrEuclideanLocalMap e U U le_rfl f) hU').1
          (enrRetractedOpenDomain e V) hWU hcoverU
        have hcoverV : ∀ x : enrRetractedOpenDomain e V,
            enrEuclideanLocalMap e V V le_rfl (enrRestrictLocalMap f V hVU) x = x.val →
              x.val ∈ enrRetractedOpenDomain e V := by
          intro z hz
          exact ⟨z.property.choose, z.property.choose_spec⟩
        obtain ⟨hriV, hiV⟩ := (hb.1 e.dimension (enrRetractedOpenDomain e V)
          (enrEuclideanLocalMap e V V le_rfl (enrRestrictLocalMap f V hVU)) hV').1
          (enrRetractedOpenDomain e V) le_rfl hcoverV
        refine ⟨hKV, ?_⟩
        unfold enrLocalFixedPointIndex enrRetractionIndex
        rw [← hiU, ← hiV]
        congr 1
      · constructor
        · intro U f hK hempty
          have hcover : ∀ x : U, f x = x.1 → x.1 ∈ U := fun x _ ↦ x.2
          have hc := enrRetractedLocalMap_compact_fixedSet e U U le_rfl f hK hcover
          unfold enrLocalFixedPointIndex enrRetractionIndex
          apply (hb.1 e.dimension _ _ hc).2.1
          ext v
          constructor
          · intro hv
            change enrEuclideanLocalMap e U U le_rfl f v = v.val at hv
            let x : U := ⟨e.retraction (retractedDomainInclusion e U v), v.property.choose_spec⟩
            have hv' : e.sectionMap (f x) = retractedDomainInclusion e U v := by
              apply Subtype.ext
              change (e.sectionMap (f (retractedDomainToLocalDomain e U U le_rfl v))).val = v.val
              exact hv
            have hxf : f x = x.1 := by
              have hr := congrArg e.retraction hv'
              rw [e.retraction_section] at hr
              simpa [x] using hr
            have hx : x ∈ enrLocalFixedSet f := hxf
            rw [hempty] at hx
            exact hx
          · intro hv
            simp at hv
        · constructor
          · intro U f hK k V hVU hdisj hcover
            have hU' := enrRetractedLocalMap_compact_fixedSet e U U le_rfl f hK (fun x _ ↦ x.2)
            have hVdom : ∀ i, enrRetractedOpenDomain e (V i) ≤ enrRetractedOpenDomain e U := by
              intro i z hz
              exact ⟨hz.choose, hVU i hz.choose_spec⟩
            have hdisj' : ∀ i j, i ≠ j →
                Disjoint (enrRetractedOpenDomain e (V i) : Set (Euclidean e.dimension))
                  (enrRetractedOpenDomain e (V j) : Set (Euclidean e.dimension)) := by
              intro i j hij
              apply Set.disjoint_left.2
              intro z hzi hzj
              let zi : enrRetractedOpenDomain e (V i) := ⟨z, hzi⟩
              let zj : enrRetractedOpenDomain e (V j) := ⟨z, hzj⟩
              have hi : e.retraction (retractedDomainInclusion e (V i) zi) ∈ (V i : Set X) :=
                zi.property.choose_spec
              have hj : e.retraction (retractedDomainInclusion e (V j) zj) ∈ (V j : Set X) :=
                zj.property.choose_spec
              have heq : retractedDomainInclusion e (V i) zi =
                  retractedDomainInclusion e (V j) zj := by
                apply Subtype.ext
                rfl
              apply Set.disjoint_left.1 (hdisj hij)
              · exact hi
              · simpa [heq] using hj
            have hcover' : ∀ z : enrRetractedOpenDomain e U,
                enrEuclideanLocalMap e U U le_rfl f z = z.val →
                  ∃ i, z.val ∈ enrRetractedOpenDomain e (V i) := by
              intro z hz
              change enrEuclideanLocalMap e U U le_rfl f z = z.val at hz
              let x : U := ⟨e.retraction (retractedDomainInclusion e U z), z.property.choose_spec⟩
              have hz' : e.sectionMap (f x) = retractedDomainInclusion e U z := by
                apply Subtype.ext
                change (e.sectionMap (f (retractedDomainToLocalDomain e U U le_rfl z))).val = z.val
                exact hz
              have hxf : f x = x.1 := by
                have hr := congrArg e.retraction hz'
                rw [e.retraction_section] at hr
                simpa [x] using hr
              obtain ⟨i, hxi⟩ := hcover x hxf
              refine ⟨i, ?_⟩
              exact ⟨z.property.choose, by
                change e.retraction (retractedDomainInclusion e U z) ∈ (V i : Set X)
                simpa [x] using hxi⟩
            obtain ⟨hVec, hsum⟩ := (hb.1 e.dimension (enrRetractedOpenDomain e U)
              (enrEuclideanLocalMap e U U le_rfl f) hU').2.2 k
              (fun i ↦ enrRetractedOpenDomain e (V i)) hVdom hdisj' hcover'
            have hV : ∀ i, IsCompact
                (enrLocalFixedSet (enrRestrictLocalMap f (V i) (hVU i))) := by
              intro i
              let A := euclideanFixedSet (enrEuclideanLocalMap e U (V i) (hVU i) f)
              have hA : IsCompact A := by
                convert hVec i using 1; try { ext z; rfl }
              let q : C(A, V i) :=
                { toFun := fun z ↦ ⟨e.retraction (retractedDomainInclusion e (V i) z.1),
                    z.1.property.choose_spec⟩
                  continuous_toFun := by
                    exact (e.retraction.continuous.comp
                      ((retractedDomainInclusion e (V i)).continuous.comp continuous_subtype_val)).subtype_mk _ }
              have hEq : q '' (Set.univ : Set A) =
                  enrLocalFixedSet (enrRestrictLocalMap f (V i) (hVU i)) := by
                ext x
                constructor
                · rintro ⟨z, -, rfl⟩
                  change enrRestrictLocalMap f (V i) (hVU i) (q z) = (q z).1
                  have hz : enrEuclideanLocalMap e U (V i) (hVU i) f z.1 = z.1.val := z.property
                  let y : U := ⟨e.retraction (retractedDomainInclusion e (V i) z.1),
                    hVU i z.1.property.choose_spec⟩
                  change (e.sectionMap (f y)).val = z.1.val at hz
                  have hz' : e.sectionMap (f y) = retractedDomainInclusion e (V i) z.1 := by
                    apply Subtype.ext
                    exact hz
                  have hr := congrArg e.retraction hz'
                  rw [e.retraction_section] at hr
                  change f y = e.retraction (retractedDomainInclusion e (V i) z.1)
                  exact hr
                · intro hx
                  let z : enrRetractedOpenDomain e (V i) :=
                    ⟨e.sectionMap (x : X), ⟨e.sectionMap (x : X) |>.property, by
                      rw [e.retraction_section]
                      exact x.2⟩⟩
                  have hz : z ∈ A := by
                    let y : U := ⟨e.retraction (retractedDomainInclusion e (V i) z),
                      hVU i z.property.choose_spec⟩
                    change (e.sectionMap (f y)).val = z.val
                    let xU : U := ⟨x.1, hVU i x.2⟩
                    have hx' : f xU = xU.1 := hx
                    have hxdom : y = xU := by
                      apply Subtype.ext
                      dsimp [y]
                      rw [show retractedDomainInclusion e (V i) z = e.sectionMap (x : X) by
                        apply Subtype.ext; rfl]
                      rw [e.retraction_section]
                    rw [hxdom, hx']
                  exact ⟨⟨z, hz⟩, Set.mem_univ _, by
                    apply Subtype.ext
                    change e.retraction (retractedDomainInclusion e (V i) z) = (x : X)
                    rw [show retractedDomainInclusion e (V i) z = e.sectionMap (x : X) by
                      apply Subtype.ext; rfl]
                    rw [e.retraction_section]⟩
              rw [← hEq]
              let : CompactSpace A := isCompact_iff_compactSpace.mp hA
              exact IsCompact.image isCompact_univ q.continuous
            refine ⟨hV, ?_⟩
            unfold enrLocalFixedPointIndex enrRetractionIndex
            rw [hsum]
            congr 1
    
          · constructor
            · intro U H hTot
              have hs : ∀ t : unitInterval, IsCompact (enrLocalFixedSet (enrHomotopySlice H t)) := by
                intro t
                let K : Set (U × unitInterval) := {p | H p = p.1.1}
                let S : Set (U × unitInterval) := (Set.univ : Set U) ×ˢ ({t} : Set unitInterval)
                have hSt : IsClosed S := isClosed_univ.prod isClosed_singleton
                have hKS : IsCompact (K ∩ S) := hTot.inter_right hSt
                have hEq : (fun p : U × unitInterval => p.1) '' (K ∩ S) =
                    enrLocalFixedSet (enrHomotopySlice H t) := by
                  ext x
                  constructor
                  · rintro ⟨p, ⟨hpK, hpS⟩, rfl⟩
                    change enrHomotopySlice H t p.1 = p.1.1
                    have hpt : p.2 = t := hpS.2
                    change H p = p.1.1 at hpK
                    have hpfix : H (p.1, t) = p.1.1 := by rw [← hpt]; exact hpK
                    exact hpfix
                  · intro hx
                    have hfx : H (x, t) = x.1 := hx
                    exact ⟨(x,t), ⟨hfx, ⟨Set.mem_univ _, rfl⟩⟩, rfl⟩
                rw [← hEq]
                exact hKS.image continuous_fst
            
              let rpair : C(enrRetractedOpenDomain e U × unitInterval, U × unitInterval) :=
                { toFun := fun q ↦
                    (⟨e.retraction (retractedDomainInclusion e U q.1), q.1.property.choose_spec⟩, q.2)
                  continuous_toFun := by
                    exact ((e.retraction.continuous.comp ((retractedDomainInclusion e U).continuous.comp continuous_fst)).subtype_mk _).prodMk continuous_snd }
              let Hr : C(enrRetractedOpenDomain e U × unitInterval, Euclidean e.dimension) :=
                { toFun := fun q ↦ (e.sectionMap (H (rpair q))).val
                  continuous_toFun := by
                    exact continuous_subtype_val.comp (e.sectionMap.continuous.comp
                      (H.continuous.comp rpair.continuous)) }
              let K : Set (U × unitInterval) := {p | H p = p.1.1}
              let t : C(K, enrRetractedOpenDomain e U × unitInterval) :=
                { toFun := fun p ↦
                    (⟨(e.sectionMap p.1.1).val, ⟨(e.sectionMap p.1.1).property, by
                      rw [e.retraction_section]
                      exact p.1.1.2⟩⟩, p.1.2)
                  continuous_toFun := by fun_prop }
              have hEq : {p : enrRetractedOpenDomain e U × unitInterval | Hr p = p.1.1} =
                  t '' (Set.univ : Set K) := by
                ext q
                constructor
                · intro hq
                  let x : U := (rpair q).1
                  have hz' : e.sectionMap (H (rpair q)) = retractedDomainInclusion e U q.1 := by
                    apply Subtype.ext
                    exact hq
                  have hfx : H (rpair q) = (rpair q).1.1 := by
                    have hr := congrArg e.retraction hz'
                    rw [e.retraction_section] at hr
                    exact hr
                  have hxK : (x, q.2) ∈ K := by
                    change H (rpair q) = (rpair q).1.1
                    exact hfx
                  have htx : t ⟨(x, q.2), hxK⟩ = q := by
                    apply Prod.ext
                    · apply Subtype.ext
                      change (e.sectionMap (x : X)).val = q.1.val
                      have hsec : e.sectionMap (x : X) = retractedDomainInclusion e U q.1 := by
                        rw [← hfx]
                        exact hz'
                      exact congrArg Subtype.val hsec
                    · rfl
                  exact ⟨⟨(x, q.2), hxK⟩, Set.mem_univ _, htx⟩
                · rintro ⟨p, -, rfl⟩
                  have hpK : H p.1 = p.1.1 := by exact p.property
                  have hdom : rpair (t p) = p.1 := by
                    apply Prod.ext
                    · apply Subtype.ext
                      change e.retraction (retractedDomainInclusion e U (t p).1) = p.1.1
                      rw [show retractedDomainInclusion e U (t p).1 = e.sectionMap (p.1.1 : X) by
                        apply Subtype.ext; rfl]
                      rw [e.retraction_section]
                    · rfl
                  change (e.sectionMap (H (rpair (t p)))).val = (t p).1.val
                  rw [hdom, hpK]
                  rfl
              have h0 := hs 0
              have h1 := hs 1
              have h0e := enrRetractedLocalMap_compact_fixedSet e U U le_rfl (enrHomotopySlice H 0) h0 (fun x _ ↦ x.2)
              have h1e := enrRetractedLocalMap_compact_fixedSet e U U le_rfl (enrHomotopySlice H 1) h1 (fun x _ ↦ x.2)
              have hcomp : IsCompact {p : enrRetractedOpenDomain e U × unitInterval | Hr p = p.1.1} := by
                rw [hEq]
                let : CompactSpace K := isCompact_iff_compactSpace.mp hTot
                exact IsCompact.image isCompact_univ t.continuous
              obtain ⟨ha, hb1, hi⟩ := hb.2.1 e.dimension (enrRetractedOpenDomain e U) Hr hcomp
              have hmap0 : Hr.comp ⟨fun x ↦ (x, 0), continuous_id.prodMk continuous_const⟩ =
                  enrEuclideanLocalMap e U U le_rfl (enrHomotopySlice H 0) := by
                ext z
                rfl
              have hmap1 : Hr.comp ⟨fun x ↦ (x, 1), continuous_id.prodMk continuous_const⟩ =
                  enrEuclideanLocalMap e U U le_rfl (enrHomotopySlice H 1) := by
                ext z
                rfl
              refine ⟨h0, h1, ?_⟩
              unfold enrLocalFixedPointIndex enrRetractionIndex
              simpa [hmap0, hmap1] using hi
            · constructor
              · intro Y _ _ _ eY h U f hK
                have hY : IsCompact (enrLocalFixedSet (enrConjugateLocalMap h U f)) := by
                  let t : C(U, enrConjugateDomain h U) :=
                    ⟨fun x ↦ ⟨h x.1, ⟨x.1, x.2, rfl⟩⟩,
                      (h.continuous.comp continuous_subtype_val).subtype_mk _⟩
                  have hEq : enrLocalFixedSet (enrConjugateLocalMap h U f) =
                      t '' enrLocalFixedSet f := by
                    ext y
                    constructor
                    · intro hy
                      obtain ⟨x, hx, hxy⟩ := y.property
                      let xU : U := ⟨x, hx⟩
                      have ht : t xU = y := Subtype.ext hxy
                      refine ⟨xU, ?_, ht⟩
                      change enrConjugateLocalMap h U f y = y.1 at hy
                      rw [← ht] at hy
                      have hmem : h.symm (h x) ∈ (U : Set X) := by simpa only [h.symm_apply_apply] using hx
                      change h (f ⟨h.symm (h x), hmem⟩) = h x at hy
                      have harg : (⟨h.symm (h x), hmem⟩ : U) = xU := by
                        apply Subtype.ext
                        exact h.symm_apply_apply x
                      rw [harg] at hy
                      exact h.injective hy
                    · rintro ⟨x, hx, rfl⟩
                      have hmem : h.symm (h x.1) ∈ (U : Set X) := by simp
                      change h (f ⟨h.symm (h x.1), hmem⟩) = h x.1
                      have harg : (⟨h.symm (h x.1), hmem⟩ : U) = x := by
                        apply Subtype.ext
                        exact h.symm_apply_apply x.1
                      rw [harg, hx]
                  rw [hEq]
                  exact hK.image t.continuous
                let eBack : ENRRepresentation X :=
                  { dimension := eY.dimension
                    domain := eY.domain
                    domain_open := eY.domain_open
                    sectionMap := eY.sectionMap.comp ⟨h, h.continuous⟩
                    retraction := (⟨h.symm, h.symm.continuous⟩ : C(Y, X)).comp eY.retraction
                    retraction_section := by
                      intro x
                      change h.symm (eY.retraction (eY.sectionMap (h x))) = x
                      rw [eY.retraction_section, h.symm_apply_apply] }
                have hd : enrRetractedOpenDomain eY (enrConjugateDomain h U) =
                    enrRetractedOpenDomain eBack U := by
                  ext z
                  change (∃ hz : z ∈ eY.domain, eY.retraction ⟨z, hz⟩ ∈ h '' (U : Set X)) ↔
                    (∃ hz : z ∈ eY.domain, h.symm (eY.retraction ⟨z, hz⟩) ∈ (U : Set X))
                  constructor
                  · rintro ⟨hz, x, hx, hxy⟩
                    refine ⟨hz, ?_⟩
                    rw [← hxy, h.symm_apply_apply]
                    exact hx
                  · rintro ⟨hz, hx⟩
                    exact ⟨hz, h.symm (eY.retraction ⟨z, hz⟩), hx, h.apply_symm_apply _⟩
                have htransport : enrLocalFixedPointIndex eY (enrConjugateDomain h U)
                    (enrConjugateLocalMap h U f) hY = enrLocalFixedPointIndex eBack U f hK := by
                  let g := enrEuclideanLocalMap eBack U U le_rfl f
                  have hg : ∀ z : enrRetractedOpenDomain eY (enrConjugateDomain h U),
                      enrEuclideanLocalMap eY (enrConjugateDomain h U) (enrConjugateDomain h U)
                        le_rfl (enrConjugateLocalMap h U f) z =
                      g ⟨z.1, by rw [← hd]; exact z.2⟩ := by
                    intro z
                    rfl
                  suffices hh : ∀ (V : Opens (Euclidean eY.dimension))
                      (heq : V = enrRetractedOpenDomain eBack U)
                      (q : C(V, Euclidean eY.dimension)) (hq : IsCompact (euclideanFixedSet q))
                      (hgK : IsCompact (euclideanFixedSet g)),
                      (∀ z : V, q z = g ⟨z.1, by rw [← heq]; exact z.2⟩) →
                        euclideanFixedPointIndex q hq = euclideanFixedPointIndex g hgK by
                    unfold enrLocalFixedPointIndex enrRetractionIndex
                    exact hh _ hd _ _ _ hg
                  intro V heq q hq hgK hqg
                  subst V
                  have he : q = g := by
                    apply ContinuousMap.ext
                    intro z
                    exact hqg z
                  subst q
                  rfl
                refine ⟨hY, htransport.trans ?_⟩
                exact (hrepr eBack U f hK).symm
              · intro n U f hK
                have hd : enrRetractedOpenDomain (euclideanENRRepresentation n) U = U := by
                  ext z
                  change (∃ _ : z ∈ (Set.univ : Set (Euclidean n)), z ∈ U) ↔ z ∈ U
                  constructor
                  · rintro ⟨_, hz⟩
                    exact hz
                  · intro hz
                    exact ⟨Set.mem_univ _, hz⟩
                suffices hh : ∀ (V : Opens (Euclidean n)) (hd : V = U)
                    (g : C(V, Euclidean n)) (hk : IsCompact (euclideanFixedSet g)),
                    (∀ z : V, g z = f ⟨z.1, by rw [← hd]; exact z.2⟩) →
                    euclideanFixedPointIndex g hk = euclideanFixedPointIndex f hK by
                  unfold enrLocalFixedPointIndex enrRetractionIndex
                  apply hh _ hd
                  intro z
                  rfl
                intro V hd g hk hg
                subst V
                have he : g = f := by
                  apply ContinuousMap.ext
                  intro z
                  exact hg z
                subst g
                rfl
end HolomorphicAnosov.FixedPointIndexInterface
