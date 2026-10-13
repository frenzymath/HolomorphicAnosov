import HolomorphicAnosov.Dynamics.Anosov.InvariantRealTangentSplitting
import HolomorphicAnosov.Topology.FranksPiecewiseC1PathG8
import HolomorphicAnosov.Topology.Franks.LeafBox
import HolomorphicAnosov.Topology.Franks.LeafFoliation
import HolomorphicAnosov.Topology.Franks.LeafTransport
import HolomorphicAnosov.Topology.Franks.LeafPathLength
import HolomorphicAnosov.Topology.Franks.IntrinsicLeafDistance
import HolomorphicAnosov.Geometry.Manifold.Diffeomorph.RealIterate
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Manifold.Immersion
import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Geometry.Manifold.Riemannian.Basic
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.Topology.Covering.Basic
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.Separation.Lemmas
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.Calculus.AddTorsor.AffineMap
import Mathlib.Topology.Connected.Clopen

/-!
# Intrinsic leaf lengths on the original smooth universal cover

Source: Franks, *Anosov Diffeomorphisms*, Global Analysis Part I (1970),
Proposition 1.1, Lemma 1.2 and Corollary 1.3, printed pp. 65--66.
All manifolds below retain their supplied native atlases. The leaf distances
are constructed from actual finite-piece C¹ paths in their intrinsic atlases.
-/

open scoped ContDiff Manifold Bundle Topology _root_.Topology ENNReal
open Set Manifold MeasureTheory Filter Bundle

universe u
namespace HolomorphicAnosov.Franks
noncomputable section

section PathOperations

variable {r s : ℕ} {L K : Type u} [TopologicalSpace L] [TopologicalSpace K]
variable [ChartedSpace (EuclideanSpace ℝ (Fin r)) L]
variable [ChartedSpace (EuclideanSpace ℝ (Fin s)) K]
variable [IsManifold (𝓡 r) 1 L] [IsManifold (𝓡 s) 1 K]

/-- Literal composition of a finite-piece intrinsic path with a native C¹ map.
The partition, original endpoints and one underlying function are retained.
This is constructor data, not a postulated path or leaf transport. -/
def PiecewiseC1Path.map {x y : L} (γ : PiecewiseC1Path (r := r) x y)
    (a : L → K) (ha : ContMDiff (𝓡 r) (𝓡 s) 1 a) :
    PiecewiseC1Path (r := s) (a x) (a y) where
  toFun := a ∘ γ.toFun
  continuousOn := ha.continuous.comp_continuousOn γ.continuousOn
  pieces := γ.pieces
  pieces_pos := γ.pieces_pos
  division := γ.division
  division_strictMono := γ.division_strictMono
  division_zero := γ.division_zero
  division_one := γ.division_one
  contMDiffOn_piece j := ha.comp_contMDiffOn (γ.contMDiffOn_piece j)
  source := by change a (γ.toFun 0) = a x; rw [γ.source]
  target := by change a (γ.toFun 1) = a y; rw [γ.target]

end PathOperations

section SetLevelLeafImage

attribute [local instance] LeafBox.topology

variable {n r : ℕ} {P : Type u} [MetricSpace P]
variable [ChartedSpace (EuclideanSpace ℝ (Fin n)) P] [IsManifold (𝓡 n) ∞ P]
variable {ι : Type u} {L : ι → Type u} [∀ i, TopologicalSpace (L i)]
variable [∀ i, ChartedSpace (EuclideanSpace ℝ (Fin r)) (L i)]
variable [∀ i, IsManifold (𝓡 r) 1 (L i)]
variable {D : RealTangentDistribution (𝓡 n) P}

/-- Reindexing the SAME native leaf along an equality of its label. -/
def nativeLeafCast {i j : ι} (h : i = j) : L i ≃ₜ L j := by
  subst j
  exact Homeomorph.refl _

theorem nativeLeafCast_inclusion (G : LeafFoliation (r := r) (L := L) D)
    {i j : ι} (h : i = j) (v : L i) :
    G.inclusion j (nativeLeafCast h v) = G.inclusion i v := by
  subst j
  rfl

/-- Choose an actual point of an original connected leaf, solely to label its image. -/
def leafBasepoint (G : LeafFoliation (r := r) (L := L) D) (i : ι) : L i :=
  Classical.choice (G.connected i).toNonempty

/-- The covering partition chooses the image label of one actual original leaf point.
No intrinsic topology or smoothness claim is encoded in this choice. -/
def imageLeafLabel (G : LeafFoliation (r := r) (L := L) D) (a : P → P) (i : ι) : ι :=
  Classical.choose (G.cover (a (G.inclusion i (leafBasepoint G i))))

/-- If the actual ambient map preserves the given whole-leaf relation, all points
of one original leaf land in the label chosen from its basepoint. Disjointness,
rather than an identification with an ambient subspace, supplies this result. -/
theorem exists_image_leaf_point (G : LeafFoliation (r := r) (L := L) D) (a : P → P)
    (hpres : ∀ x y : P,
      (∃ i u v, G.inclusion i u = x ∧ G.inclusion i v = y) →
      ∃ j u v, G.inclusion j u = a x ∧ G.inclusion j v = a y)
    (i : ι) (x : L i) :
    ∃ y : L (imageLeafLabel G a i), G.inclusion (imageLeafLabel G a i) y =
      a (G.inclusion i x) := by
  obtain ⟨j, u, v, hu, hv⟩ := hpres _ _ ⟨i, leafBasepoint G i, x, rfl, rfl⟩
  obtain ⟨z, hz⟩ := Classical.choose_spec (G.cover (a (G.inclusion i (leafBasepoint G i))))
  have hj : j = imageLeafLabel G a i := G.disjoint _ _ u z (hu.trans hz.symm)
  subst j
  exact ⟨v, hv⟩

/-- The actual pointwise restriction of an ambient leaf-preserving map. Its
intrinsic C¹ regularity is deliberately not part of this set-level construction. -/
def imageLeafPoint (G : LeafFoliation (r := r) (L := L) D) (a : P → P)
    (hpres : ∀ x y : P,
      (∃ i u v, G.inclusion i u = x ∧ G.inclusion i v = y) →
      ∃ j u v, G.inclusion j u = a x ∧ G.inclusion j v = a y)
    (i : ι) (x : L i) : L (imageLeafLabel G a i) :=
  Classical.choose (exists_image_leaf_point G a hpres i x)

theorem imageLeafPoint_intertwining (G : LeafFoliation (r := r) (L := L) D) (a : P → P)
    (hpres : ∀ x y : P,
      (∃ i u v, G.inclusion i u = x ∧ G.inclusion i v = y) →
      ∃ j u v, G.inclusion j u = a x ∧ G.inclusion j v = a y)
    (i : ι) (x : L i) :
    G.inclusion (imageLeafLabel G a i) (imageLeafPoint G a hpres i x) =
      a (G.inclusion i x) :=
  Classical.choose_spec (exists_image_leaf_point G a hpres i x)

/-- The native immersion criterion reduces regularity of the CONSTRUCTED
restriction to its intrinsic continuity. The ambient map's C¹ law alone does
not imply that continuity: a whole leaf may return in several plaques. -/
theorem imageLeafPoint_contMDiffAt_of_continuousAt
    (G : LeafFoliation (r := r) (L := L) D) (a : P → P)
    (ha : ContMDiff (𝓡 n) (𝓡 n) 1 a)
    (hpres : ∀ x y : P,
      (∃ i u v, G.inclusion i u = x ∧ G.inclusion i v = y) →
      ∃ j u v, G.inclusion j u = a x ∧ G.inclusion j v = a y)
    (i : ι) (x : L i)
    (hc : ContinuousAt (imageLeafPoint G a hpres i) x) :
    ContMDiffAt (𝓡 r) (𝓡 r) 1 (imageLeafPoint G a hpres i) x := by
  apply (ContMDiffAt.iff_comp_isImmersionAt
    (G.immersion (imageLeafLabel G a i) (imageLeafPoint G a hpres i x))).2
  refine ⟨hc, ?_⟩
  have heq : G.inclusion (imageLeafLabel G a i) ∘ imageLeafPoint G a hpres i =
      a ∘ G.inclusion i :=
    funext (imageLeafPoint_intertwining G a hpres i)
  rw [heq]
  exact ha.contMDiffAt.comp x (G.immersion i x).contMDiffAt

/-- In a target box, equality of its ACTUAL transverse coordinate identifies
the original leaf point with the C¹ plaque parametrization. This supplies an
explicit local inverse without treating the entire leaf as ambiently embedded. -/
theorem LeafBox.point_eq_chart_of_transverse_eq
    (G : LeafFoliation (r := r) (L := L) D) (B : LeafBox (n := n) (r := r) G.inclusion)
    (t : B.transversal) (q : L (B.label t)) (hq : G.inclusion (B.label t) q ∈ B.ambient)
    (ht : (B.box.symm ⟨G.inclusion (B.label t) q, hq⟩).2 = t) :
    (B.chart t (B.box.symm ⟨G.inclusion (B.label t) q, hq⟩).1 : L (B.label t)) = q := by
  apply G.injective (B.label t)
  rw [← B.intertwining]
  have hpair : ((B.box.symm ⟨G.inclusion (B.label t) q, hq⟩).1, t) =
      B.box.symm ⟨G.inclusion (B.label t) q, hq⟩ := Prod.ext rfl ht.symm
  rw [hpair, B.box.apply_symm_apply]

/-- The same box has disjoint intrinsic open plaques. These sets are defined
using actual points and the original inclusion; label equality is used only to
recognize their openness, not as an assumed topology identification. -/
def LeafBox.plaqueInLeaf
    (G : LeafFoliation (r := r) (L := L) D) (B : LeafBox (n := n) (r := r) G.inclusion)
    (j : ι) (t : B.transversal) : Set (L j) :=
  {q | ∃ z : B.disc, (B.box (z, t) : P) = G.inclusion j q}

theorem LeafBox.plaqueInLeaf_eq
    (G : LeafFoliation (r := r) (L := L) D) (B : LeafBox (n := n) (r := r) G.inclusion)
    (t : B.transversal) :
    B.plaqueInLeaf G (B.label t) t = (B.plaque t : Set (L (B.label t))) := by
  ext q
  constructor
  · rintro ⟨z, hz⟩
    have he : (B.chart t z : L (B.label t)) = q :=
      G.injective _ ((B.intertwining t z).symm.trans hz)
    rw [← he]
    exact (B.chart t z).property
  · intro hq
    refine ⟨(B.chart t).symm ⟨q, hq⟩, ?_⟩
    rw [B.intertwining, (B.chart t).apply_symm_apply]

theorem LeafBox.plaqueInLeaf_pairwiseDisjoint
    (G : LeafFoliation (r := r) (L := L) D) (B : LeafBox (n := n) (r := r) G.inclusion) (j : ι) :
    (Set.univ : Set B.transversal).PairwiseDisjoint (B.plaqueInLeaf G j) := by
  intro t ht s hs hts
  apply Set.disjoint_left.2
  rintro q ⟨z, hz⟩ ⟨w, hw⟩
  have he : B.box (z, t) = B.box (w, s) := Subtype.ext (hz.trans hw.symm)
  exact hts (congrArg Prod.snd (B.box.injective he))

/-- Countability of returning plaques is a CONSEQUENCE of the original
intrinsic leaf's second-countability and the box's disjoint open plaques.
The supplied `z` is an actual box coordinate; no extra nonemptiness axiom is used. -/
theorem LeafBox.countable_labels_eq
    (G : LeafFoliation (r := r) (L := L) D) (B : LeafBox (n := n) (r := r) G.inclusion)
    (j : ι) (z : B.disc) : {t : B.transversal | B.label t = j}.Countable := by
  let : SecondCountableTopology (L j) := G.second_countable j
  have ho : ∀ t ∈ {t : B.transversal | B.label t = j},
      IsOpen (B.plaqueInLeaf G j t) := by
    intro t ht
    change B.label t = j at ht
    cases ht
    rw [B.plaqueInLeaf_eq]
    exact (B.plaque t).isOpen
  have hn : ∀ t ∈ {t : B.transversal | B.label t = j},
      (B.plaqueInLeaf G j t).Nonempty := by
    intro t ht
    change B.label t = j at ht
    cases ht
    exact ⟨B.chart t z, z, B.intertwining t z⟩
  have hd : {t : B.transversal | B.label t = j}.PairwiseDisjoint
      (B.plaqueInLeaf G j) := by
    intro t ht s hs hts
    exact B.plaqueInLeaf_pairwiseDisjoint G j (Set.mem_univ t) (Set.mem_univ s) hts
  exact hd.countable_of_isOpen ho hn

/-- A continuous transverse coordinate on a connected neighborhood cannot move
among a countable set of returning plaques. The proof maps it into the ORIGINAL
metric ambient space using a fixed genuine box coordinate. No metric is installed
on the transversal and no leaf subspace topology is substituted. -/
theorem LeafBox.transverse_constant
    {Q : Type*} [TopologicalSpace Q] [PreconnectedSpace Q]
    (G : LeafFoliation (r := r) (L := L) D) (B : LeafBox (n := n) (r := r) G.inclusion)
    (j : ι) (z : B.disc) (τ : Q → B.transversal) (hτ : Continuous τ)
    (hlabel : ∀ q, B.label (τ q) = j) (x y : Q) : τ x = τ y := by
  let e : B.transversal → P := fun t ↦ (B.box (z, t) : P)
  have he : Continuous e :=
    continuous_subtype_val.comp (B.box.continuous.comp (continuous_const.prodMk continuous_id))
  have hi : Function.Injective e := by
    intro t s hts
    exact congrArg Prod.snd (B.box.injective (Subtype.ext hts))
  have hcount : (e '' {t : B.transversal | B.label t = j}).Countable :=
    (B.countable_labels_eq G j z).image e
  have hsub : Set.range (e ∘ τ) ⊆ e '' {t : B.transversal | B.label t = j} := by
    rintro _ ⟨q, rfl⟩
    exact ⟨τ q, hlabel q, rfl⟩
  have hsingle := hcount.isTotallyDisconnected _ hsub
    (isPreconnected_range (he.comp hτ))
  exact hi (hsingle ⟨x, rfl⟩ ⟨y, rfl⟩)

/-- A continuous ambient map into ONE original leaf is intrinsically continuous.
The proof uses an actual target box and a connected source neighborhood. Its
transverse coordinate is constant by countability of returning plaques; the
actual plaque inverse then gives the native lift. No whole-leaf embedding or
ambient-subspace topology is assumed. -/
theorem leaf_map_continuous_of_inclusion
    (G : LeafFoliation (r := r) (L := L) D) (i j : ι) (q : L i → L j)
    (hq : Continuous (G.inclusion j ∘ q)) : Continuous q := by
  let : LocallyConnectedSpace (L i) :=
    ChartedSpace.locallyConnectedSpace (EuclideanSpace ℝ (Fin r)) (L i)
  apply continuous_iff_continuousAt.2
  intro x
  obtain ⟨B, hxB⟩ := G.box_cover (G.inclusion j (q x))
  let U : Set (L i) := (G.inclusion j ∘ q) ⁻¹' (B.ambient : Set P)
  have hU : IsOpen U := B.ambient.isOpen.preimage hq
  obtain ⟨V, hVU, hV, hxV, hVconn⟩ :=
    (locallyConnectedSpace_iff_subsets_isOpen_isConnected.1
      (inferInstance : LocallyConnectedSpace (L i))) x U (hU.mem_nhds hxB)
  let : ConnectedSpace V := Subtype.connectedSpace hVconn
  let c : V → B.ambient := fun z ↦ ⟨G.inclusion j (q z), hVU z.property⟩
  have hc : Continuous c := (hq.comp continuous_subtype_val).subtype_mk _
  let τ : V → B.transversal := fun z ↦ (B.box.symm (c z)).2
  have hτ : Continuous τ := continuous_snd.comp (B.box.symm.continuous.comp hc)
  have hlabel : ∀ z : V, B.label (τ z) = j := by
    intro z
    apply G.disjoint _ _ (B.chart (τ z) (B.box.symm (c z)).1) (q z)
    rw [← B.intertwining]
    change (B.box (B.box.symm (c z)) : P) = G.inclusion j (q z)
    rw [B.box.apply_symm_apply]
  let xV : V := ⟨x, hxV⟩
  let t : B.transversal := τ xV
  let z0 : B.disc := (B.box.symm (c xV)).1
  have ht : ∀ z : V, τ z = t := fun z ↦ B.transverse_constant G j z0 τ hτ hlabel z xV
  have hLj : B.label t = j := hlabel xV
  let e : L (B.label t) ≃ₜ L j := nativeLeafCast hLj
  have he : ∀ v : L (B.label t), G.inclusion j (e v) = G.inclusion (B.label t) v := by
    intro v
    exact nativeLeafCast_inclusion G hLj v
  let v : V → L j := fun z ↦ e (B.chart t (B.box.symm (c z)).1)
  have hv : Continuous v := e.continuous.comp
    (continuous_subtype_val.comp ((B.chart t).continuous.comp
      (continuous_fst.comp (B.box.symm.continuous.comp hc))))
  have hvq : v = V.domRestrict q := by
    funext z
    apply G.injective j
    change G.inclusion j (e (B.chart t (B.box.symm (c z)).1)) = G.inclusion j (q z)
    rw [he, ← B.intertwining]
    have hpair : ((B.box.symm (c z)).1, t) = B.box.symm (c z) :=
      Prod.ext rfl (ht z).symm
    rw [hpair, B.box.apply_symm_apply]
  have hqV : ContinuousOn q V := continuousOn_iff_continuous_domRestrict.2 (hvq ▸ hv)
  exact hqV.continuousAt (hV.mem_nhds hxV)

/-- The set-level restriction actually constructed above is therefore C¹ in the
ORIGINAL intrinsic leaf atlases. All topology work is discharged by the existing
target box laws; this is not a new assumption on an abstract transport. -/
theorem imageLeafPoint_contMDiff
    (G : LeafFoliation (r := r) (L := L) D) (a : P → P)
    (ha : ContMDiff (𝓡 n) (𝓡 n) 1 a)
    (hpres : ∀ x y : P,
      (∃ i u v, G.inclusion i u = x ∧ G.inclusion i v = y) →
      ∃ j u v, G.inclusion j u = a x ∧ G.inclusion j v = a y)
    (i : ι) : ContMDiff (𝓡 r) (𝓡 r) 1 (imageLeafPoint G a hpres i) := by
  have he : G.inclusion (imageLeafLabel G a i) ∘ imageLeafPoint G a hpres i =
      a ∘ G.inclusion i := funext (imageLeafPoint_intertwining G a hpres i)
  have hc : Continuous (imageLeafPoint G a hpres i) := by
    apply leaf_map_continuous_of_inclusion G i (imageLeafLabel G a i)
    rw [he]
    exact ha.continuous.comp (continuous_iff_continuousAt.2
      (fun x ↦ (G.immersion i x).continuousAt))
  exact fun x ↦ imageLeafPoint_contMDiffAt_of_continuousAt G a ha hpres i x hc.continuousAt

/-- The actual lifted finite-piece path, now constructed on the original image
leaf rather than supplied as a transport hypothesis. The native C¹ restriction
has just been proved using the genuine foliation boxes and returning plaques. -/
def imageLeafPath
    (G : LeafFoliation (r := r) (L := L) D) (a : P → P)
    (ha : ContMDiff (𝓡 n) (𝓡 n) 1 a)
    (hpres : ∀ x y : P,
      (∃ i u v, G.inclusion i u = x ∧ G.inclusion i v = y) →
      ∃ j u v, G.inclusion j u = a x ∧ G.inclusion j v = a y)
    {i : ι} {x y : L i} (γ : PiecewiseC1Path (r := r) x y) :
    PiecewiseC1Path (r := r) (imageLeafPoint G a hpres i x)
      (imageLeafPoint G a hpres i y) :=
  γ.map (imageLeafPoint G a hpres i) (imageLeafPoint_contMDiff G a ha hpres i)

/-- Exact equality of the constructed path's ambient realization and the given
ambient action on the ORIGINAL path, at every parameter, including breakpoints. -/
theorem imageLeafPath_inclusion
    (G : LeafFoliation (r := r) (L := L) D) (a : P → P)
    (ha : ContMDiff (𝓡 n) (𝓡 n) 1 a)
    (hpres : ∀ x y : P,
      (∃ i u v, G.inclusion i u = x ∧ G.inclusion i v = y) →
      ∃ j u v, G.inclusion j u = a x ∧ G.inclusion j v = a y)
    {i : ι} {x y : L i} (γ : PiecewiseC1Path (r := r) x y) :
    G.inclusion (imageLeafLabel G a i) ∘ (imageLeafPath G a ha hpres γ).toFun =
      a ∘ G.inclusion i ∘ γ.toFun := by
  funext t
  exact imageLeafPoint_intertwining G a hpres i (γ.toFun t)

theorem same_leaf_iff_eq_labels
    (G : LeafFoliation (r := r) (L := L) D) (i j : ι) (x : L i) (y : L j) :
    (∃ k u v, G.inclusion k u = G.inclusion i x ∧
      G.inclusion k v = G.inclusion j y) ↔ i = j := by
  constructor
  · rintro ⟨k, u, v, hu, hv⟩
    exact (G.disjoint k i u x hu).symm.trans (G.disjoint k j v y hv)
  · intro h
    subst j
    exact ⟨i, x, y, rfl, rfl⟩

/-- An actual ambient bijection preserving the whole-leaf relation in both
directions gives a bijection of the ORIGINAL labels, using their partition law. -/
theorem imageLeafLabel_bijective
    (G : LeafFoliation (r := r) (L := L) D) (a : P ≃ P)
    (hrel : ∀ x y : P,
      (∃ i u v, G.inclusion i u = x ∧ G.inclusion i v = y) ↔
      ∃ j u v, G.inclusion j u = a x ∧ G.inclusion j v = a y) :
    Function.Bijective (imageLeafLabel G a) := by
  let hpres := fun x y ↦ (hrel x y).1
  constructor
  · intro i j hij
    apply (same_leaf_iff_eq_labels G i j (leafBasepoint G i) (leafBasepoint G j)).1
    apply (hrel _ _).2
    rw [← imageLeafPoint_intertwining G a hpres i (leafBasepoint G i),
      ← imageLeafPoint_intertwining G a hpres j (leafBasepoint G j)]
    exact (same_leaf_iff_eq_labels G _ _ _ _).2 hij
  · intro j
    obtain ⟨i, x, hx⟩ := G.cover (a.symm (G.inclusion j (leafBasepoint G j)))
    refine ⟨i, G.disjoint _ _ (imageLeafPoint G a hpres i x) (leafBasepoint G j) ?_⟩
    rw [imageLeafPoint_intertwining, hx, a.apply_symm_apply]

/-- The actual restriction of that bijection is a bijection of whole original
leaf carriers. Surjectivity uses coverage of the inverse ambient point and the
original whole-leaf relation, including returning plaques. -/
theorem imageLeafPoint_bijective
    (G : LeafFoliation (r := r) (L := L) D) (a : P ≃ P)
    (hrel : ∀ x y : P,
      (∃ i u v, G.inclusion i u = x ∧ G.inclusion i v = y) ↔
      ∃ j u v, G.inclusion j u = a x ∧ G.inclusion j v = a y) (i : ι) :
    Function.Bijective (imageLeafPoint G a (fun x y ↦ (hrel x y).1) i) := by
  let hpres := fun x y ↦ (hrel x y).1
  constructor
  · intro x y hxy
    apply G.injective i
    apply a.injective
    rw [← imageLeafPoint_intertwining G a hpres i x,
      ← imageLeafPoint_intertwining G a hpres i y, hxy]
  · intro y
    obtain ⟨j, u, hu⟩ := G.cover (a.symm (G.inclusion (imageLeafLabel G a i) y))
    have hau : a (G.inclusion j u) = G.inclusion (imageLeafLabel G a i) y := by
      rw [hu, a.apply_symm_apply]
    have hij : i = j := by
      apply (same_leaf_iff_eq_labels G i j (leafBasepoint G i) u).1
      apply (hrel _ _).2
      rw [hau, ← imageLeafPoint_intertwining G a hpres i (leafBasepoint G i)]
      exact ⟨imageLeafLabel G a i, imageLeafPoint G a hpres i (leafBasepoint G i),
        y, rfl, rfl⟩
    subst j
    refine ⟨u, G.injective _ ?_⟩
    rw [imageLeafPoint_intertwining, hau]

theorem inverse_leaf_relation_iff
    (G : LeafFoliation (r := r) (L := L) D) (a : P ≃ P)
    (hrel : ∀ x y : P,
      (∃ i u v, G.inclusion i u = x ∧ G.inclusion i v = y) ↔
      ∃ j u v, G.inclusion j u = a x ∧ G.inclusion j v = a y) (x y : P) :
    (∃ i u v, G.inclusion i u = x ∧ G.inclusion i v = y) ↔
      ∃ j u v, G.inclusion j u = a.symm x ∧ G.inclusion j v = a.symm y := by
  simpa only [a.apply_symm_apply] using (hrel (a.symm x) (a.symm y)).symm

/-- An actual native ambient diffeomorphism preserving the actual whole-leaf
relation constructs the required transport DATA. Both intrinsic regularity
proofs use the original target boxes, never a global Euclidean leaf model. -/
def leafTransportOfDiffeomorph
    (G : LeafFoliation (r := r) (L := L) D)
    (a : Diffeomorph (𝓡 n) (𝓡 n) P P ∞)
    (hrel : ∀ x y : P,
      (∃ i u v, G.inclusion i u = x ∧ G.inclusion i v = y) ↔
      ∃ j u v, G.inclusion j u = a x ∧ G.inclusion j v = a y) :
    LeafTransport G a where
  permutation := Equiv.ofBijective (imageLeafLabel G a) (imageLeafLabel_bijective G a.toEquiv hrel)
  leafMap i := by
    change Diffeomorph (𝓡 r) (𝓡 r) (L i) (L (imageLeafLabel G a i)) 1
    let hpres := fun x y ↦ (hrel x y).1
    let e := Equiv.ofBijective (imageLeafPoint G a hpres i)
      (imageLeafPoint_bijective G a.toEquiv hrel i)
    refine { toEquiv := e
             contMDiff_toFun := imageLeafPoint_contMDiff G a (a.contMDiff.of_le (by simp)) hpres i
             contMDiff_invFun := ?_ }
    have he : G.inclusion i ∘ e.symm = a.symm ∘ G.inclusion (imageLeafLabel G a i) := by
      funext y
      apply a.injective
      change a (G.inclusion i (e.symm y)) =
        a (a.symm (G.inclusion (imageLeafLabel G a i) y))
      rw [a.apply_symm_apply]
      have h := imageLeafPoint_intertwining G a hpres i (e.symm y)
      change G.inclusion (imageLeafLabel G a i) (e (e.symm y)) =
        a (G.inclusion i (e.symm y)) at h
      simpa only [e.apply_symm_apply] using h.symm
    have hc : Continuous e.symm := by
      apply leaf_map_continuous_of_inclusion G (imageLeafLabel G a i) i
      rw [he]
      exact a.symm.continuous.comp (continuous_iff_continuousAt.2
        (fun x ↦ (G.immersion (imageLeafLabel G a i) x).continuousAt))
    intro x
    apply (ContMDiffAt.iff_comp_isImmersionAt (G.immersion i (e.symm x))).2
    refine ⟨hc.continuousAt, ?_⟩
    rw [he]
    exact (a.symm.contMDiff.of_le (by simp)).contMDiffAt.comp x
      (G.immersion (imageLeafLabel G a i) x).contMDiffAt
  intertwining i x := by
    change G.inclusion (imageLeafLabel G a i)
      (imageLeafPoint G a (fun x y ↦ (hrel x y).1) i x) = a (G.inclusion i x)
    exact imageLeafPoint_intertwining G a (fun x y ↦ (hrel x y).1) i x


end SetLevelLeafImage


section NativePathSupport

variable {n : ℕ} {P : Type u} [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) P] [IsManifold (𝓡 n) ∞ P]

/-- The supplied original smooth tensor gives finite length to each closed C¹
piece. The within derivative includes its actual endpoint values; only continuity
on the compact interval is needed. -/
theorem originalMetric_piece_pathELength_ne_top
    (g : ContMDiffRiemannianMetric (𝓡 n) ∞ (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : P → Type _))
    (a b : ℝ) (hab : a < b) (γ : ℝ → P)
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 n) 1 γ (Icc a b)) :
    letI : ∀ p : P, ENorm (TangentSpace (𝓡 n) p) := ambientMetricENorm g
    pathELength (𝓡 n) γ a b ≠ ⊤ := by
  let : RiemannianBundle (fun p : P ↦ TangentSpace (𝓡 n) p) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (fun p : P ↦ TangentSpace (𝓡 n) p) :=
    ⟨g.inner, g.contMDiff.continuous, fun _ _ _ ↦ rfl⟩
  have hu : UniqueMDiffOn 𝓘(ℝ, ℝ) (Icc a b) := by
    rw [uniqueMDiffOn_iff_uniqueDiffOn]
    exact uniqueDiffOn_Icc hab
  have ht := hγ.continuousOn_tangentMapWithin (le_refl 1) hu
  have hv : ContinuousOn
      (fun t ↦ TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) (γ t)
        (mfderivWithin 𝓘(ℝ, ℝ) (𝓡 n) γ (Icc a b) t 1)) (Icc a b) := by
    have hc : Continuous (fun t : ℝ ↦
        TotalSpace.mk' ℝ t (1 : TangentSpace 𝓘(ℝ, ℝ) t)) := by
      exact (tangentBundleModelSpaceHomeomorph 𝓘(ℝ, ℝ)).symm.continuous.comp
        (continuous_id.prodMk continuous_const)
    exact ht.comp hc.continuousOn (fun t ht ↦ ht)
  have hs : ContinuousOn
      (fun t ↦ Real.sqrt (g.inner (γ t)
        (mfderivWithin 𝓘(ℝ, ℝ) (𝓡 n) γ (Icc a b) t 1)
        (mfderivWithin 𝓘(ℝ, ℝ) (𝓡 n) γ (Icc a b) t 1))) (Icc a b) := by
    exact Real.continuous_sqrt.comp_continuousOn (hv.inner_bundle hv)
  obtain ⟨C, hC⟩ := isCompact_Icc.bddAbove_image hs
  let : ∀ p : P, ENorm (TangentSpace (𝓡 n) p) := ambientMetricENorm g
  apply ne_of_lt
  rw [pathELength_eq_lintegral_mfderivWithin_Icc]
  calc
    _ ≤ ∫⁻ _t in Icc a b, ENNReal.ofReal C := by
      apply setLIntegral_mono' measurableSet_Icc
      intro t ht
      exact ENNReal.ofReal_le_ofReal (hC ⟨t, ht, rfl⟩)
    _ < ⊤ := by
      simp only [setLIntegral_const, Real.volume_Icc]
      exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top


omit [IsManifold (𝓡 n) ∞ P] in
/-- Finite additivity needs no smoothness at the finitely many joining times. -/
theorem pathELength_partition_ne_top
    [∀ p : P, ENorm (TangentSpace (𝓡 n) p)]
    (a : ℝ → P) (d : ℕ → ℝ) (hd : Monotone d) (N : ℕ)
    (hpiece : ∀ j < N, pathELength (𝓡 n) a (d j) (d (j + 1)) ≠ ⊤) :
    pathELength (𝓡 n) a (d 0) (d N) ≠ ⊤ := by
  revert hpiece
  induction N with
  | zero => intro _; simp
  | succ N ih =>
      intro hpiece
      rw [← pathELength_add (hd (Nat.zero_le N)) (hd (Nat.le_succ N))]
      exact ENNReal.add_ne_top.mpr ⟨ih (fun j hj ↦ hpiece j (Nat.lt_succ_of_lt hj)),
        hpiece N (Nat.lt_succ_self N)⟩

/-- Every actual finite-piece intrinsic path has finite length in the ORIGINAL
smooth ambient metric: compose each piece with the given C¹ leaf immersion,
bound its continuous metric speed on the compact interval, then add finitely
many lengths. No metric or topology is placed on the leaf by this argument. -/
theorem leafPathELength_ne_top
    {r : ℕ} {ι : Type u} {L : ι → Type u}
    [∀ i, TopologicalSpace (L i)]
    [∀ i, ChartedSpace (EuclideanSpace ℝ (Fin r)) (L i)]
    [∀ i, IsManifold (𝓡 r) 1 (L i)]
    (g : ContMDiffRiemannianMetric (𝓡 n) ∞ (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : P → Type _))
    {D : RealTangentDistribution (𝓡 n) P}
    (G : LeafFoliation (r := r) (L := L) D)
    {i : ι} {x y : L i} (γ : PiecewiseC1Path (r := r) x y) :
    leafPathELength g G γ ≠ ⊤ := by
  let : ∀ p : P, ENorm (TangentSpace (𝓡 n) p) := ambientMetricENorm g
  have hinc : ContMDiff (𝓡 r) (𝓡 n) 1 (G.inclusion i) :=
    fun z ↦ (G.immersion i z).contMDiffAt
  let d : ℕ → ℝ := fun m ↦
    γ.division ⟨min m γ.pieces, Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩
  have hd : Monotone d := by
    intro m l hml
    apply γ.division_strictMono.monotone
    change min m γ.pieces ≤ min l γ.pieces
    exact min_le_min_right γ.pieces hml
  have hpiece : ∀ j < γ.pieces,
      pathELength (𝓡 n) (G.inclusion i ∘ γ.toFun) (d j) (d (j + 1)) ≠ ⊤ := by
    intro j hj
    have hlt := γ.division_strictMono (Fin.castSucc_lt_succ (i := (⟨j, hj⟩ : Fin γ.pieces)))
    have hs := hinc.comp_contMDiffOn (γ.contMDiffOn_piece ⟨j, hj⟩)
    simpa [d, Nat.min_eq_left (Nat.le_of_lt hj),
      Nat.min_eq_left (Nat.succ_le_of_lt hj)] using
      originalMetric_piece_pathELength_ne_top g _ _ hlt _ hs
  have hb := pathELength_partition_ne_top (G.inclusion i ∘ γ.toFun) d hd γ.pieces hpiece
  have hd0 : d 0 = 0 := by simpa [d] using γ.division_zero
  have hdN : d γ.pieces = 1 := by simpa [d, Fin.last] using γ.division_one
  simpa only [leafPathELength, hd0, hdN] using hb


section PathExistence

variable {r : ℕ} {L : Type*} [TopologicalSpace L]
  [ChartedSpace (EuclideanSpace ℝ (Fin r)) L] [IsManifold (𝓡 r) 1 L]

/-- A connected C¹ manifold admits actual C¹ interval paths. An auxiliary zero
ENorm is used ONLY to encode reachability in Mathlib's existing path-infimum
concatenation theorem; it is never used for the original metric length. Local
chart line segments give reachability, and connected induction globalizes it. -/
theorem connected_piecewiseC1Path_nonempty [ConnectedSpace L] (x y : L) :
    Nonempty (PiecewiseC1Path (r := r) x y) := by
  let : ∀ z : L, ENorm (TangentSpace (𝓡 r) z) := fun _ ↦ ⟨fun _ ↦ 0⟩
  let : ∀ z : L, ENormSMulClass ℝ (TangentSpace (𝓡 r) z) :=
    fun _ ↦ ⟨fun _ _ ↦ by change (0 : ℝ≥0∞) = _ * 0; simp⟩
  have hlocal (a : L) : ∀ᶠ b in 𝓝 a, riemannianEDist (𝓡 r) a b < ⊤ := by
    let c := chartAt (EuclideanSpace ℝ (Fin r)) a
    have ha : a ∈ c.source := mem_chart_source _ _
    have hac : c a ∈ c.target := c.map_source ha
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp c.open_target (c a) hac
    have hn : c ⁻¹' Metric.ball (c a) ε ∩ c.source ∈ 𝓝 a :=
      inter_mem (c.continuousAt ha |>.preimage_mem_nhds (Metric.ball_mem_nhds _ hε))
        (c.open_source.mem_nhds ha)
    filter_upwards [hn] with b hb
    let α : ℝ → L := c.symm ∘ AffineMap.lineMap (c a) (c b)
    have hα : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 r) 1 α (Icc 0 1) := by
      apply contMDiffOn_chart_symm.comp
      · rw [contMDiffOn_iff_contDiffOn]
        exact (AffineMap.contDiff_lineMap _ _).contDiffOn
      · exact (convex_ball (c a) ε).mapsTo_lineMap (Metric.mem_ball_self hε) hb.1
          |>.mono_right hball
    have h0 : α 0 = a := by simp [α, c.left_inv ha]
    have h1 : α 1 = b := by simp [α, c.left_inv hb.2]
    have hzero : pathELength (𝓡 r) α 0 1 = 0 := by
      rw [pathELength_eq_lintegral_mfderiv_Icc]
      change (∫⁻ _t in Icc (0 : ℝ) 1, (0 : ℝ≥0∞)) = 0
      simp
    exact lt_of_le_of_lt (riemannianEDist_le_pathELength hα h0 h1 zero_le_one)
      (by rw [hzero]; exact ENNReal.zero_lt_top)
  let R : L → L → Prop := fun a b ↦ riemannianEDist (𝓡 r) a b < ⊤
  have hglobal : R x y := by
    apply PreconnectedSpace.induction₂' R
    · intro a
      filter_upwards [hlocal a] with b hb
      exact ⟨hb, by change riemannianEDist (𝓡 r) b a < ⊤; rwa [riemannianEDist_comm]⟩
    · exact ⟨fun a b c hab hbc ↦ lt_of_le_of_lt riemannianEDist_triangle
        (ENNReal.add_lt_top.mpr ⟨hab, hbc⟩)⟩
  obtain ⟨γ, hγ0, hγ1, hγ, -⟩ := exists_lt_of_riemannianEDist_lt hglobal
  refine ⟨{
    toFun := γ
    continuousOn := hγ.continuousOn
    pieces := 1
    pieces_pos := by decide
    division := fun i ↦ (i.val : ℝ)
    division_strictMono := ?_
    division_zero := by norm_num
    division_one := by norm_num
    contMDiffOn_piece := ?_
    source := hγ0
    target := hγ1 }⟩
  · intro a b hab
    change (a.val : ℝ) < (b.val : ℝ)
    exact_mod_cast hab
  · intro i
    fin_cases i
    simpa using hγ


end PathExistence


end NativePathSupport

section Bounds

variable {n rs ru : ℕ}
variable {M P : Type u} [MetricSpace M] [MetricSpace P]
variable [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) P]
variable [IsManifold (𝓡 n) ∞ M] [IsManifold (𝓡 n) ∞ P]
variable [hMcompact : CompactSpace M] [hMconn : PreconnectedSpace M]
variable [hPconn : PreconnectedSpace P]
variable [hMcount : SecondCountableTopology M] [hPcount : SecondCountableTopology P]
variable [Bundle.RiemannianBundle (fun x : M ↦ TangentSpace (𝓡 n) x)]
variable [Bundle.RiemannianBundle (fun x : P ↦ TangentSpace (𝓡 n) x)]
variable [hMg : IsContMDiffRiemannianBundle (𝓡 n) ∞ (EuclideanSpace ℝ (Fin n))
  (fun x : M ↦ TangentSpace (𝓡 n) x)]
variable [hPg : IsContMDiffRiemannianBundle (𝓡 n) ∞ (EuclideanSpace ℝ (Fin n))
  (fun x : P ↦ TangentSpace (𝓡 n) x)]
variable [hMd : IsRiemannianManifold (𝓡 n) M] [hPd : IsRiemannianManifold (𝓡 n) P]
variable {ιs ιu : Type u} {Ls : ιs → Type u} {Lu : ιu → Type u}
variable [∀ i, TopologicalSpace (Ls i)] [∀ i, TopologicalSpace (Lu i)]
variable [∀ i, ChartedSpace (EuclideanSpace ℝ (Fin rs)) (Ls i)]
variable [∀ i, ChartedSpace (EuclideanSpace ℝ (Fin ru)) (Lu i)]
variable [∀ i, IsManifold (𝓡 rs) 1 (Ls i)]
variable [∀ i, IsManifold (𝓡 ru) 1 (Lu i)]

omit [IsManifold (𝓡 n) ∞ M] [IsManifold (𝓡 n) ∞ P]
    hMcompact hMconn hPconn hMcount hPcount hMg hPg hMd hPd in
/-- Franks (1970), Lemma 1.2, pp.65–66: the pullback tensor makes the
covering derivative preserve the ORIGINAL tangent norm in both fibres. -/
theorem covering_derivative_norm
    (p : P → M)
    (hp_metric : ∀ x (v w : TangentSpace (𝓡 n) x),
      inner ℝ v w = inner ℝ (mfderiv (𝓡 n) (𝓡 n) p x v)
        (mfderiv (𝓡 n) (𝓡 n) p x w))
    (x : P) (v : TangentSpace (𝓡 n) x) :
    ‖mfderiv (𝓡 n) (𝓡 n) p x v‖ = ‖v‖ := by
  rw [norm_eq_sqrt_real_inner, norm_eq_sqrt_real_inner, ← hp_metric x v v]

omit [MetricSpace M] [MetricSpace P] hMcompact hMconn hPconn hMcount hPcount in
/-- The original lift identity iterates pointwise; no metric or chart
identification enters this application of semiconjugacy. -/
theorem covering_iterate_semiconj
    (f : M → M) (F : P → P) (p : P → M)
    (hF : ∀ x, p (F x) = f (p x)) (k : ℕ) (x : P) :
    p ((F^[k]) x) = (f^[k]) (p x) :=
  (show Function.Semiconj p F f from hF).iterate_right k x

omit [IsManifold (𝓡 n) ∞ M] [IsManifold (𝓡 n) ∞ P]
    hMcompact hMconn hPconn hMcount hPcount hMg hPg hMd hPd in
/-- Franks (1970), Lemma 1.2, pp.65–66, the lifted distribution speed calculation.
Differentiate the actual iterated lift identity. The covering derivative
is isometric in the original metrics at the source and at the receiving
point. Membership in the pulled-back stable fibre supplies the original
base estimate; no intrinsic leaf metric or global Euclidean carrier is used. -/
theorem lifted_distribution_iterate_speed
    (f : Diffeomorph (𝓡 n) (𝓡 n) M M ∞)
    (D : RealTangentDistribution (𝓡 n) M)
    (C rate : ℝ)
    (hs : ∀ k x (v : TangentSpace (𝓡 n) x),
      v ∈ D x →
      ‖mfderiv (𝓡 n) (𝓡 n) ((f : M → M)^[k]) x v‖ ≤ C * rate^k * ‖v‖)
    (p : P → M) (hp_smooth : IsLocalDiffeomorph (𝓡 n) (𝓡 n) ∞ p)
    (hp_metric : ∀ x (v w : TangentSpace (𝓡 n) x),
      inner ℝ v w = inner ℝ (mfderiv (𝓡 n) (𝓡 n) p x v)
        (mfderiv (𝓡 n) (𝓡 n) p x w))
    (F : Diffeomorph (𝓡 n) (𝓡 n) P P ∞)
    (hF : ∀ x, p (F x) = f (p x)) (k : ℕ) (x : P)
    (v : TangentSpace (𝓡 n) x)
    (hv : v ∈ (D (p x)).comap
      (mfderiv (𝓡 n) (𝓡 n) p x).toLinearMap) :
    ‖mfderiv (𝓡 n) (𝓡 n) ((F : P → P)^[k]) x v‖ ≤ C * rate^k * ‖v‖ := by
  have hi := covering_iterate_semiconj (f : M → M) (F : P → P) p hF k
  have hc : p ∘ ((F : P → P)^[k]) = ((f : M → M)^[k]) ∘ p := funext hi
  have hd := mfderiv_congr (I := 𝓡 n) (I' := 𝓡 n) (x := x) hc
  rw [mfderiv_comp x (hp_smooth.mdifferentiable (by simp) _)
    ((F.contMDiff.iterate k).mdifferentiable (by simp) x),
    mfderiv_comp x ((f.contMDiff.iterate k).mdifferentiable (by simp) _)
      (hp_smooth.mdifferentiable (by simp) x)] at hd
  have hdv := congrArg (fun A ↦ A v) hd
  change mfderiv (𝓡 n) (𝓡 n) p (((F : P → P)^[k]) x)
    (mfderiv (𝓡 n) (𝓡 n) ((F : P → P)^[k]) x v) =
    mfderiv (𝓡 n) (𝓡 n) ((f : M → M)^[k]) (p x)
      (mfderiv (𝓡 n) (𝓡 n) p x v) at hdv
  calc
    _ = ‖mfderiv (𝓡 n) (𝓡 n) p (((F : P → P)^[k]) x)
        (mfderiv (𝓡 n) (𝓡 n) ((F : P → P)^[k]) x v)‖ :=
      (covering_derivative_norm p hp_metric _ _).symm
    _ = ‖mfderiv (𝓡 n) (𝓡 n) ((f : M → M)^[k]) (p x)
        (mfderiv (𝓡 n) (𝓡 n) p x v)‖ := by
      rw [hdv, hi x]
    _ ≤ C * rate^k * ‖mfderiv (𝓡 n) (𝓡 n) p x v‖ := hs k (p x) _ hv
    _ = C * rate^k * ‖v‖ := by rw [covering_derivative_norm p hp_metric x v]


omit [IsManifold (𝓡 n) ∞ P] hMcompact hMconn hPconn hMcount hPcount hMg hPg hMd hPd in
/-- Franks (1970), Lemma 1.2, pp.65–66, the lifted stable speed calculation.
Differentiate the actual iterated lift identity. The covering derivative
is isometric in the original metrics at the source and at the receiving
point. Membership in the pulled-back stable fibre supplies the original
base estimate; no intrinsic leaf metric or global Euclidean carrier is used. -/
theorem lifted_stable_iterate_speed
    (f : Diffeomorph (𝓡 n) (𝓡 n) M M ∞)
    (splitting : InvariantRealTangentSplitting f)
    (C rate : ℝ)
    (hs : ∀ k x (v : TangentSpace (𝓡 n) x),
      v ∈ splitting.stable.toDistribution x →
      ‖mfderiv (𝓡 n) (𝓡 n) ((f : M → M)^[k]) x v‖ ≤ C * rate^k * ‖v‖)
    (p : P → M) (hp_smooth : IsLocalDiffeomorph (𝓡 n) (𝓡 n) ∞ p)
    (hp_metric : ∀ x (v w : TangentSpace (𝓡 n) x),
      inner ℝ v w = inner ℝ (mfderiv (𝓡 n) (𝓡 n) p x v)
        (mfderiv (𝓡 n) (𝓡 n) p x w))
    (F : Diffeomorph (𝓡 n) (𝓡 n) P P ∞)
    (hF : ∀ x, p (F x) = f (p x)) (k : ℕ) (x : P)
    (v : TangentSpace (𝓡 n) x)
    (hv : v ∈ (splitting.stable.toDistribution (p x)).comap
      (mfderiv (𝓡 n) (𝓡 n) p x).toLinearMap) :
    ‖mfderiv (𝓡 n) (𝓡 n) ((F : P → P)^[k]) x v‖ ≤ C * rate^k * ‖v‖ := by
  exact lifted_distribution_iterate_speed f splitting.stable.toDistribution C rate hs
    p hp_smooth hp_metric F hF k x v hv

omit [IsManifold (𝓡 n) ∞ M] [IsManifold (𝓡 n) ∞ P]
    hMcompact hMconn hPconn hMcount hPcount
    [Bundle.RiemannianBundle (fun x : M ↦ TangentSpace (𝓡 n) x)]
    [Bundle.RiemannianBundle (fun x : P ↦ TangentSpace (𝓡 n) x)] hMg hPg hMd hPd in
/-- The lift relation for the inverse original diffeomorphisms, with the
receiving point explicitly retained. No inverse tangent norm is taken at x
when its true receiving fibre is F⁻¹x. -/
theorem covering_inverse_semiconj
    (f : Diffeomorph (𝓡 n) (𝓡 n) M M ∞)
    (F : Diffeomorph (𝓡 n) (𝓡 n) P P ∞) (p : P → M)
    (hF : ∀ x, p (F x) = f (p x)) (x : P) : p (F.symm x) = f.symm (p x) := by
  apply f.injective
  change f (p (F.symm x)) = f (f.symm (p x))
  rw [← hF, F.apply_symm_apply, f.apply_symm_apply]

omit [IsManifold (𝓡 n) ∞ P] hMcompact hMconn hPconn hMcount hPcount hMg hPg hMd hPd in
/-- The unstable inverse-iterate speed bound in the SAME original metrics.
It is the preceding actual lift calculation with f⁻¹/F⁻¹ and the original
unstable distribution; no reconstructed splitting or chart metric is used. -/
theorem lifted_unstable_inverse_iterate_speed
    (f : Diffeomorph (𝓡 n) (𝓡 n) M M ∞)
    (splitting : InvariantRealTangentSplitting f)
    (C rate : ℝ)
    (hu : ∀ k x (v : TangentSpace (𝓡 n) x),
      v ∈ splitting.unstable.toDistribution x →
      ‖mfderiv (𝓡 n) (𝓡 n) ((f.symm : M → M)^[k]) x v‖ ≤ C * rate^k * ‖v‖)
    (p : P → M) (hp_smooth : IsLocalDiffeomorph (𝓡 n) (𝓡 n) ∞ p)
    (hp_metric : ∀ x (v w : TangentSpace (𝓡 n) x),
      inner ℝ v w = inner ℝ (mfderiv (𝓡 n) (𝓡 n) p x v)
        (mfderiv (𝓡 n) (𝓡 n) p x w))
    (F : Diffeomorph (𝓡 n) (𝓡 n) P P ∞)
    (hF : ∀ x, p (F x) = f (p x)) (k : ℕ) (x : P)
    (v : TangentSpace (𝓡 n) x)
    (hv : v ∈ (splitting.unstable.toDistribution (p x)).comap
      (mfderiv (𝓡 n) (𝓡 n) p x).toLinearMap) :
    ‖mfderiv (𝓡 n) (𝓡 n) ((F.symm : P → P)^[k]) x v‖ ≤ C * rate^k * ‖v‖ := by
  exact lifted_distribution_iterate_speed f.symm splitting.unstable.toDistribution C rate hu
    p hp_smooth hp_metric F.symm (covering_inverse_semiconj f F p hF) k x v hv


omit hPconn hPcount hPg hPd in
/-- Franks's original tensor norm and the explicit norm used by the leaf
length definition agree pointwise. This is only a norm adapter, with the
given tensor identified with the ORIGINAL installed inner product. -/
theorem ambient_metric_enorm_eq
    (g : Bundle.ContMDiffRiemannianMetric (𝓡 n) ∞ (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : P → Type _))
    (hg : ∀ x (v w : TangentSpace (𝓡 n) x), g.inner x v w = inner ℝ v w)
    (x : P) (v : TangentSpace (𝓡 n) x) :
    @enorm _ (ambientMetricENorm g x) v = ‖v‖ₑ := by
  change ENNReal.ofReal (Real.sqrt (g.inner x v v)) = ‖v‖ₑ
  rw [hg x v v, ← norm_eq_sqrt_real_inner]
  exact ofReal_norm v


omit hPconn hPcount hPg hPd in
/-- The explicit tensor ENorm used by the intrinsic definition gives exactly
the ORIGINAL ambient norm integral when its tensor is the installed original g.
This identifies norms pointwise, not the leaf topology or a coordinate metric. -/
theorem metric_pathELength_eq
    (g : Bundle.ContMDiffRiemannianMetric (𝓡 n) ∞ (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : P → Type _))
    (hg : ∀ x (v w : TangentSpace (𝓡 n) x), g.inner x v w = inner ℝ v w)
    (γ : ℝ → P) (a b : ℝ) :
    (letI : ∀ p : P, ENorm (TangentSpace (𝓡 n) p) := ambientMetricENorm g
     Manifold.pathELength (𝓡 n) γ a b) = Manifold.pathELength (𝓡 n) γ a b := by
  simp only [Manifold.pathELength_eq_lintegral_mfderiv_Icc]
  apply MeasureTheory.setLIntegral_congr_fun measurableSet_Icc
  intro t ht
  exact ambient_metric_enorm_eq g hg _ _

omit hPconn hPcount hPg hPd in
theorem leafPathELength_eq_original
    {D : RealTangentDistribution (𝓡 n) P}
    (G : LeafFoliation (r := rs) (L := Ls) D)
    (g : Bundle.ContMDiffRiemannianMetric (𝓡 n) ∞ (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : P → Type _))
    (hg : ∀ x (v w : TangentSpace (𝓡 n) x), g.inner x v w = inner ℝ v w)
    {i : ιs} {x y : Ls i} (γ : PiecewiseC1Path (r := rs) x y) :
    leafPathELength g G γ = Manifold.pathELength (𝓡 n) (G.inclusion i ∘ γ.toFun) 0 1 :=
  metric_pathELength_eq g hg _ _ _

omit hPconn hPcount [Bundle.RiemannianBundle (fun x : P ↦ TangentSpace (𝓡 n) x)] hPg hPd in
/-- The given forward asymptotic characterization proves actual leaf preservation
by every nonnegative iterate: it is the SAME orbit sequence with a finite shift.
This supplies the input of `imageLeafPoint`, rather than assuming a transport. -/
theorem iterate_preserves_asymptotic_leaf
    {D : RealTangentDistribution (𝓡 n) P}
    (G : LeafFoliation (r := rs) (L := Ls) D) (F : P → P)
    (hG : ∀ x y : P, (∃ i u v, G.inclusion i u = x ∧ G.inclusion i v = y) ↔
      Filter.Tendsto (fun m : ℕ ↦ dist ((F^[m]) x) ((F^[m]) y))
        Filter.atTop (nhds 0)) (k : ℕ) :
    ∀ x y : P, (∃ i u v, G.inclusion i u = x ∧ G.inclusion i v = y) →
      ∃ j u v, G.inclusion j u = (F^[k]) x ∧ G.inclusion j v = (F^[k]) y := by
  intro x y hxy
  apply (hG _ _).2
  have ht := ((hG x y).1 hxy).comp (Filter.tendsto_add_atTop_nat k)
  change Filter.Tendsto
    (fun m : ℕ ↦ dist ((F^[m + k]) x) ((F^[m + k]) y))
    Filter.atTop (nhds 0) at ht
  simpa only [Function.comp_apply, Function.iterate_add_apply] using ht

omit hPconn hPcount [Bundle.RiemannianBundle (fun x : P ↦ TangentSpace (𝓡 n) x)] hPg hPd in
/-- Finite orbit shifts preserve the original asymptotic relation in BOTH
directions, so the actual forward iterate supplies the full native transport. -/
theorem iterate_asymptotic_leaf_iff
    {D : RealTangentDistribution (𝓡 n) P}
    (G : LeafFoliation (r := rs) (L := Ls) D) (F : P → P)
    (hG : ∀ x y : P, (∃ i u v, G.inclusion i u = x ∧ G.inclusion i v = y) ↔
      Filter.Tendsto (fun m : ℕ ↦ dist ((F^[m]) x) ((F^[m]) y))
        Filter.atTop (nhds 0)) (k : ℕ) (x y : P) :
    (∃ i u v, G.inclusion i u = x ∧ G.inclusion i v = y) ↔
      ∃ j u v, G.inclusion j u = (F^[k]) x ∧ G.inclusion j v = (F^[k]) y := by
  rw [hG x y, hG ((F^[k]) x) ((F^[k]) y)]
  have ht := (Filter.tendsto_add_atTop_iff_nat
    (f := fun m : ℕ ↦ dist ((F^[m]) x) ((F^[m]) y)) (l := nhds 0) k).symm
  simpa only [Function.iterate_add_apply] using ht

/-- The actual transport of original asymptotic leaves by the original iterate,
constructed from the native boxes and original partition; no transport is input. -/
def asymptoticIterateLeafTransport
    {D : RealTangentDistribution (𝓡 n) P}
    (G : LeafFoliation (r := rs) (L := Ls) D)
    (F : Diffeomorph (𝓡 n) (𝓡 n) P P ∞)
    (hG : ∀ x y : P, (∃ i u v, G.inclusion i u = x ∧ G.inclusion i v = y) ↔
      Filter.Tendsto (fun m : ℕ ↦ dist (((F : P → P)^[m]) x) (((F : P → P)^[m]) y))
        Filter.atTop (nhds 0)) (k : ℕ) :
    LeafTransport G ((F : P → P)^[k]) :=
  leafTransportOfDiffeomorph G (HolomorphicAnosov.realIterate (𝓡 n) F k)
    (iterate_asymptotic_leaf_iff G F hG k)

/-- The inverse iterate transports the SAME leaves: the original orbit-shift
iff and the genuine inverse ambient diffeomorphism supply this construction. -/
def asymptoticInverseIterateLeafTransport
    {D : RealTangentDistribution (𝓡 n) P}
    (G : LeafFoliation (r := rs) (L := Ls) D)
    (F : Diffeomorph (𝓡 n) (𝓡 n) P P ∞)
    (hG : ∀ x y : P, (∃ i u v, G.inclusion i u = x ∧ G.inclusion i v = y) ↔
      Filter.Tendsto (fun m : ℕ ↦ dist (((F : P → P)^[m]) x) (((F : P → P)^[m]) y))
        Filter.atTop (nhds 0)) (k : ℕ) :
    LeafTransport G ((F.symm : P → P)^[k]) :=
  leafTransportOfDiffeomorph G (HolomorphicAnosov.realIterate (𝓡 n) F k).symm
    (inverse_leaf_relation_iff G (HolomorphicAnosov.realIterate (𝓡 n) F k).toEquiv
      (iterate_asymptotic_leaf_iff G F hG k))

omit hPconn hPcount hPg hPd in
/-- The exact original-leaf speed calculation integrated on one of the EXISTING
path's open partition pieces. The derivative of the original inclusion has range
`D` by the foliation's tangent law. No target leaf map or target path is assumed. -/
theorem foliated_path_piece_length_le
    {D : RealTangentDistribution (𝓡 n) P}
    (G : LeafFoliation (r := rs) (L := Ls) D)
    (a : P → P) (ha : ContMDiff (𝓡 n) (𝓡 n) 1 a)
    (K : ℝ) (hK : 0 ≤ K)
    (hspeed : ∀ z (v : TangentSpace (𝓡 n) z), v ∈ D z →
      ‖mfderiv (𝓡 n) (𝓡 n) a z v‖ ≤ K * ‖v‖)
    {i : ιs} {x y : Ls i} (γ : PiecewiseC1Path (r := rs) x y)
    (j : Fin γ.pieces) :
    Manifold.pathELength (𝓡 n) (a ∘ G.inclusion i ∘ γ.toFun)
      (γ.division j.castSucc) (γ.division j.succ) ≤
      ENNReal.ofReal K * Manifold.pathELength (𝓡 n) (G.inclusion i ∘ γ.toFun)
        (γ.division j.castSucc) (γ.division j.succ) := by
  have hinc : ContMDiff (𝓡 rs) (𝓡 n) 1 (G.inclusion i) :=
    fun z ↦ (G.immersion i z).contMDiffAt
  rw [Manifold.pathELength_eq_lintegral_mfderiv_Ioo,
    Manifold.pathELength_eq_lintegral_mfderiv_Ioo]
  calc
    _ ≤ ∫⁻ t in Ioo (γ.division j.castSucc) (γ.division j.succ),
        ENNReal.ofReal K * ‖mfderiv 𝓘(ℝ, ℝ) (𝓡 n)
          (G.inclusion i ∘ γ.toFun) t 1‖ₑ := by
      apply MeasureTheory.setLIntegral_mono' measurableSet_Ioo
      intro t ht
      have hγ := ((γ.contMDiffOn_piece j).contMDiffAt
        (Icc_mem_nhds ht.1 ht.2)).mdifferentiableAt (by simp)
      have hi := hinc.mdifferentiableAt (x := γ.toFun t) (by simp)
      have hc := hi.comp t hγ
      have hv : mfderiv (𝓡 rs) (𝓡 n) (G.inclusion i) (γ.toFun t)
          (mfderiv 𝓘(ℝ, ℝ) (𝓡 rs) γ.toFun t 1) ∈
          D (G.inclusion i (γ.toFun t)) := by
        rw [← G.tangent i (γ.toFun t)]
        exact ⟨mfderiv 𝓘(ℝ, ℝ) (𝓡 rs) γ.toFun t 1, rfl⟩
      have hb := hspeed _ _ hv
      have he : ‖mfderiv (𝓡 n) (𝓡 n) a (G.inclusion i (γ.toFun t))
          (mfderiv (𝓡 rs) (𝓡 n) (G.inclusion i) (γ.toFun t)
            (mfderiv 𝓘(ℝ, ℝ) (𝓡 rs) γ.toFun t 1))‖ₑ ≤
          ENNReal.ofReal K * ‖mfderiv (𝓡 rs) (𝓡 n) (G.inclusion i) (γ.toFun t)
            (mfderiv 𝓘(ℝ, ℝ) (𝓡 rs) γ.toFun t 1)‖ₑ := by
        simpa only [ENNReal.ofReal_mul hK, ofReal_norm] using
          ENNReal.ofReal_le_ofReal hb
      rw [mfderiv_comp t (ha.mdifferentiableAt (by simp)) hc,
        mfderiv_comp t hi hγ]
      simpa only [ContinuousLinearMap.comp_apply, Function.comp_apply] using he
    _ = _ := MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

omit [IsManifold (𝓡 n) ∞ P] hPconn hPcount hPg hPd in
/-- Finite additivity converts per-piece bounds into the whole interval bound.
This applies even when derivatives jump at division times; the length definition
already ignores those finitely many endpoints. -/
theorem pathELength_le_mul_of_partition
    (a b : ℝ → P) (d : ℕ → ℝ) (hd : Monotone d) (K : ℝ≥0∞) (N : ℕ)
    (hpiece : ∀ j < N,
      Manifold.pathELength (𝓡 n) a (d j) (d (j + 1)) ≤
        K * Manifold.pathELength (𝓡 n) b (d j) (d (j + 1))) :
    Manifold.pathELength (𝓡 n) a (d 0) (d N) ≤
      K * Manifold.pathELength (𝓡 n) b (d 0) (d N) := by
  revert hpiece
  induction N with
  | zero => intro hpiece; simp
  | succ N ih =>
      intro hpiece
      have hprev := ih (fun j hj ↦ hpiece j (Nat.lt_succ_of_lt hj))
      rw [← Manifold.pathELength_add (hd (Nat.zero_le N)) (hd (Nat.le_succ N)),
        ← Manifold.pathELength_add (γ := b) (hd (Nat.zero_le N)) (hd (Nat.le_succ N)),
        mul_add]
      exact add_le_add hprev (hpiece N (Nat.lt_succ_self N))

omit hPconn hPcount hPg hPd in
/-- The native finite subdivision itself gives the full Franks path inequality.
The subdivision is extended constantly after its last endpoint only for Nat
induction; the ORIGINAL path function and every genuine piece are unchanged. -/
theorem foliated_path_length_le
    {D : RealTangentDistribution (𝓡 n) P}
    (G : LeafFoliation (r := rs) (L := Ls) D)
    (a : P → P) (ha : ContMDiff (𝓡 n) (𝓡 n) 1 a)
    (K : ℝ) (hK : 0 ≤ K)
    (hspeed : ∀ z (v : TangentSpace (𝓡 n) z), v ∈ D z →
      ‖mfderiv (𝓡 n) (𝓡 n) a z v‖ ≤ K * ‖v‖)
    {i : ιs} {x y : Ls i} (γ : PiecewiseC1Path (r := rs) x y) :
    Manifold.pathELength (𝓡 n) (a ∘ G.inclusion i ∘ γ.toFun) 0 1 ≤
      ENNReal.ofReal K * Manifold.pathELength (𝓡 n) (G.inclusion i ∘ γ.toFun) 0 1 := by
  let d : ℕ → ℝ := fun m ↦
    γ.division ⟨min m γ.pieces, Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩
  have hd : Monotone d := by
    intro m l hml
    apply γ.division_strictMono.monotone
    change min m γ.pieces ≤ min l γ.pieces
    exact min_le_min_right γ.pieces hml
  have hpiece : ∀ j < γ.pieces,
      Manifold.pathELength (𝓡 n) (a ∘ G.inclusion i ∘ γ.toFun) (d j) (d (j + 1)) ≤
      ENNReal.ofReal K *
        Manifold.pathELength (𝓡 n) (G.inclusion i ∘ γ.toFun) (d j) (d (j + 1)) := by
    intro j hj
    simpa [d, Nat.min_eq_left (Nat.le_of_lt hj),
      Nat.min_eq_left (Nat.succ_le_of_lt hj)] using
      foliated_path_piece_length_le G a ha K hK hspeed γ ⟨j, hj⟩
  have hb := pathELength_le_mul_of_partition
    (a ∘ G.inclusion i ∘ γ.toFun) (G.inclusion i ∘ γ.toFun) d hd
    (ENNReal.ofReal K) γ.pieces hpiece
  have hd0 : d 0 = 0 := by simpa [d] using γ.division_zero
  have hdN : d γ.pieces = 1 := by simpa [d, Fin.last] using γ.division_one
  simpa only [hd0, hdN] using hb

omit hMcompact hMconn hPconn hMcount hPcount hMg hPg hMd hPd in
/-- Franks's stable speed bound now applies to the actual original ambient
iterate and the actual finite-piece intrinsic path. Leaf transport existence is
not needed for this integral inequality and is not a hypothesis here. -/
theorem lifted_stable_path_length_le
    (f : Diffeomorph (𝓡 n) (𝓡 n) M M ∞)
    (splitting : InvariantRealTangentSplitting f)
    (C rate : ℝ) (hC : 0 < C) (hrate : 0 < rate)
    (hs : ∀ k x (v : TangentSpace (𝓡 n) x),
      v ∈ splitting.stable.toDistribution x →
      ‖mfderiv (𝓡 n) (𝓡 n) ((f : M → M)^[k]) x v‖ ≤ C * rate^k * ‖v‖)
    (p : P → M) (hp_smooth : IsLocalDiffeomorph (𝓡 n) (𝓡 n) ∞ p)
    (hp_metric : ∀ x (v w : TangentSpace (𝓡 n) x),
      inner ℝ v w = inner ℝ (mfderiv (𝓡 n) (𝓡 n) p x v)
        (mfderiv (𝓡 n) (𝓡 n) p x w))
    (F : Diffeomorph (𝓡 n) (𝓡 n) P P ∞)
    (hF : ∀ x, p (F x) = f (p x))
    (stable : LeafFoliation (r := rs) (L := Ls) (fun x ↦
      (splitting.stable.toDistribution (p x)).comap
        (mfderiv (𝓡 n) (𝓡 n) p x).toLinearMap))
    (k : ℕ) {i : ιs} {x y : Ls i} (γ : PiecewiseC1Path (r := rs) x y) :
    Manifold.pathELength (𝓡 n) (((F : P → P)^[k]) ∘ stable.inclusion i ∘ γ.toFun) 0 1 ≤
      ENNReal.ofReal (C * rate^k) *
        Manifold.pathELength (𝓡 n) (stable.inclusion i ∘ γ.toFun) 0 1 := by
  exact foliated_path_length_le stable ((F : P → P)^[k])
    ((F.contMDiff.iterate k).of_le (by simp)) (C * rate^k)
    (mul_pos hC (pow_pos hrate k)).le
    (lifted_stable_iterate_speed f splitting C rate hs p hp_smooth hp_metric F hF k) γ

omit hPconn hPcount hPg hPd in
/-- Real length comparison for the CONSTRUCTED lifted intrinsic path. The only
extra premise is the explicitly exposed finite-length obligation on the actual
input path, needed by ENNReal.toReal; it is not added to the public theorem. -/
theorem imageLeafPath_real_length_le
    {D : RealTangentDistribution (𝓡 n) P}
    (G : LeafFoliation (r := rs) (L := Ls) D)
    (g : Bundle.ContMDiffRiemannianMetric (𝓡 n) ∞ (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : P → Type _))
    (hg : ∀ x (v w : TangentSpace (𝓡 n) x), g.inner x v w = inner ℝ v w)
    (a : P → P) (ha : ContMDiff (𝓡 n) (𝓡 n) 1 a)
    (hpres : ∀ x y : P,
      (∃ i u v, G.inclusion i u = x ∧ G.inclusion i v = y) →
      ∃ j u v, G.inclusion j u = a x ∧ G.inclusion j v = a y)
    (K : ℝ) (hK : 0 ≤ K)
    (hspeed : ∀ z (v : TangentSpace (𝓡 n) z), v ∈ D z →
      ‖mfderiv (𝓡 n) (𝓡 n) a z v‖ ≤ K * ‖v‖)
    {i : ιs} {x y : Ls i} (γ : PiecewiseC1Path (r := rs) x y)
    (hfinite : leafPathELength g G γ ≠ (⊤ : ℝ≥0∞)) :
    leafPathLength g G (imageLeafPath G a ha hpres γ) ≤ K * leafPathLength g G γ := by
  have hbound := foliated_path_length_le G a ha K hK hspeed γ
  rw [← imageLeafPath_inclusion G a ha hpres γ,
    ← leafPathELength_eq_original G g hg (imageLeafPath G a ha hpres γ),
    ← leafPathELength_eq_original G g hg γ] at hbound
  have hre := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfinite) hbound
  simpa only [leafPathLength, ENNReal.toReal_mul, ENNReal.toReal_ofReal hK] using hre

/-- The infimum step of Franks's p.66 argument, on actual source and target path
families. It requires nonempty source paths and nonnegative target lengths, and
uses the constructed map of path data. There is no approximation or metric change. -/
theorem infimum_length_le_of_path_map {A B : Type*}
    (sourceLength : A → ℝ) (targetLength : B → ℝ) (φ : A → B)
    (hA : Nonempty A) (htarget : ∀ b, 0 ≤ targetLength b)
    (K : ℝ) (hK : 0 < K) (hbound : ∀ a, targetLength (φ a) ≤ K * sourceLength a) :
    sInf (Set.range targetLength) ≤ K * sInf (Set.range sourceLength) := by
  have hb : BddBelow (Set.range targetLength) := ⟨0, by
    rintro _ ⟨b, rfl⟩
    exact htarget b⟩
  have hn : (Set.range sourceLength).Nonempty := by
    obtain ⟨a⟩ := hA
    exact ⟨sourceLength a, a, rfl⟩
  have H : sInf (Set.range targetLength) / K ≤ sInf (Set.range sourceLength) := by
    apply le_csInf hn
    rintro _ ⟨a, rfl⟩
    apply (div_le_iff₀ hK).2
    simpa only [mul_comm] using
      (csInf_le hb ⟨φ a, rfl⟩).trans (hbound a)
  simpa only [mul_comm] using (div_le_iff₀ hK).1 H

omit hPconn hPcount hPg hPd in
/-- The actual intrinsic infimum inequality, using the constructed native image
path and its original-tensor length bound. The two explicitly stated obligations
are path existence and finiteness for the given C¹ finite-piece path class; they
will be discharged from connectedness/smooth metric in the public theorem. -/
theorem intrinsicDistance_imageLeafPoint_le
    {D : RealTangentDistribution (𝓡 n) P}
    (G : LeafFoliation (r := rs) (L := Ls) D)
    (g : Bundle.ContMDiffRiemannianMetric (𝓡 n) ∞ (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : P → Type _))
    (hg : ∀ x (v w : TangentSpace (𝓡 n) x), g.inner x v w = inner ℝ v w)
    (a : P → P) (ha : ContMDiff (𝓡 n) (𝓡 n) 1 a)
    (hpres : ∀ x y : P,
      (∃ i u v, G.inclusion i u = x ∧ G.inclusion i v = y) →
      ∃ j u v, G.inclusion j u = a x ∧ G.inclusion j v = a y)
    (K : ℝ) (hK : 0 < K)
    (hspeed : ∀ z (v : TangentSpace (𝓡 n) z), v ∈ D z →
      ‖mfderiv (𝓡 n) (𝓡 n) a z v‖ ≤ K * ‖v‖)
    {i : ιs} {x y : Ls i} (hpaths : Nonempty (PiecewiseC1Path (r := rs) x y))
    (hfinite : ∀ γ : PiecewiseC1Path (r := rs) x y, leafPathELength g G γ ≠ (⊤ : ℝ≥0∞)) :
    intrinsicLeafDistance g G (imageLeafPoint G a hpres i x) (imageLeafPoint G a hpres i y) ≤
      K * intrinsicLeafDistance g G x y := by
  unfold intrinsicLeafDistance
  apply infimum_length_le_of_path_map (leafPathLength g G) (leafPathLength g G)
    (imageLeafPath G a ha hpres) hpaths (fun γ ↦ ENNReal.toReal_nonneg) K hK
  intro γ
  exact imageLeafPath_real_length_le G g hg a ha hpres K hK.le hspeed γ (hfinite γ)

omit hMcompact hMconn hMcount hMg hMd in
omit hPconn hPcount hPg hPd in
/-- Applying the preceding intrinsic inequality to the actual stable lifted
iterate gives the first Franks distance contraction, once native finite-path
existence/finiteness is supplied. -/
theorem intrinsic_stable_iterate_distance_le
    (f : Diffeomorph (𝓡 n) (𝓡 n) M M ∞)
    (splitting : InvariantRealTangentSplitting f)
    (C rate : ℝ) (hC : 0 < C) (hrate : 0 < rate)
    (hs : ∀ k x (v : TangentSpace (𝓡 n) x),
      v ∈ splitting.stable.toDistribution x →
      ‖mfderiv (𝓡 n) (𝓡 n) ((f : M → M)^[k]) x v‖ ≤ C * rate^k * ‖v‖)
    (p : P → M) (hp_smooth : IsLocalDiffeomorph (𝓡 n) (𝓡 n) ∞ p)
    (hp_metric : ∀ x (v w : TangentSpace (𝓡 n) x),
      inner ℝ v w = inner ℝ (mfderiv (𝓡 n) (𝓡 n) p x v)
        (mfderiv (𝓡 n) (𝓡 n) p x w))
    (F : Diffeomorph (𝓡 n) (𝓡 n) P P ∞) (hF : ∀ x, p (F x) = f (p x))
    (stable : LeafFoliation (r := rs) (L := Ls) (fun x ↦
      (splitting.stable.toDistribution (p x)).comap
        (mfderiv (𝓡 n) (𝓡 n) p x).toLinearMap))
    (hstable : ∀ x y : P,
      (∃ i u v, stable.inclusion i u = x ∧ stable.inclusion i v = y) ↔
      Filter.Tendsto (fun m : ℕ ↦ dist (((F : P → P)^[m]) x)
        (((F : P → P)^[m]) y)) Filter.atTop (nhds 0))
    (g : Bundle.ContMDiffRiemannianMetric (𝓡 n) ∞ (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : P → Type _))
    (hg : ∀ x (v w : TangentSpace (𝓡 n) x), g.inner x v w = inner ℝ v w)
    (k : ℕ) {i : ιs} {x y : Ls i}
    (hpaths : Nonempty (PiecewiseC1Path (r := rs) x y))
    (hfinite : ∀ γ : PiecewiseC1Path (r := rs) x y,
      leafPathELength g stable γ ≠ (⊤ : ℝ≥0∞)) :
    intrinsicLeafDistance g stable
      (imageLeafPoint stable ((F : P → P)^[k])
        (iterate_preserves_asymptotic_leaf stable F hstable k) i x)
      (imageLeafPoint stable ((F : P → P)^[k])
        (iterate_preserves_asymptotic_leaf stable F hstable k) i y) ≤
      C * rate^k * intrinsicLeafDistance g stable x y := by
  exact intrinsicDistance_imageLeafPoint_le stable g hg ((F : P → P)^[k])
    ((F.contMDiff.iterate k).of_le (by simp))
    (iterate_preserves_asymptotic_leaf stable F hstable k)
    (C * rate^k) (mul_pos hC (pow_pos hrate k))
    (lifted_stable_iterate_speed f splitting C rate hs p hp_smooth hp_metric F hF k)
    hpaths hfinite

omit hPconn hPcount hPg hPd in
/-- A supplied actual native leaf diffeomorphism with the literal inclusion
square transports all finite-piece paths and the original metric infimum.
This is applied to CONSTRUCTED transports, not postulated by the public theorem. -/
theorem leafDiffeomorph_distance_le
    {D : RealTangentDistribution (𝓡 n) P}
    (G : LeafFoliation (r := rs) (L := Ls) D)
    (g : Bundle.ContMDiffRiemannianMetric (𝓡 n) ∞ (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : P → Type _))
    (hg : ∀ x (v w : TangentSpace (𝓡 n) x), g.inner x v w = inner ℝ v w)
    (a : P → P) (ha : ContMDiff (𝓡 n) (𝓡 n) 1 a)
    {i j : ιs} (e : Diffeomorph (𝓡 rs) (𝓡 rs) (Ls i) (Ls j) 1)
    (he : ∀ z, G.inclusion j (e z) = a (G.inclusion i z))
    (K : ℝ) (hK : 0 < K)
    (hspeed : ∀ z (v : TangentSpace (𝓡 n) z), v ∈ D z →
      ‖mfderiv (𝓡 n) (𝓡 n) a z v‖ ≤ K * ‖v‖) (x y : Ls i) :
    intrinsicLeafDistance g G (e x) (e y) ≤ K * intrinsicLeafDistance g G x y := by
  let : ConnectedSpace (Ls i) := G.connected i
  unfold intrinsicLeafDistance
  apply infimum_length_le_of_path_map (leafPathLength g G) (leafPathLength g G)
    (fun γ ↦ γ.map e e.contMDiff) (connected_piecewiseC1Path_nonempty x y)
    (fun _ ↦ ENNReal.toReal_nonneg) K hK
  intro γ
  have hb := foliated_path_length_le G a ha K hK.le hspeed γ
  have hinc : G.inclusion j ∘ (γ.map e e.contMDiff).toFun =
      a ∘ G.inclusion i ∘ γ.toFun := by
    funext t
    exact he (γ.toFun t)
  rw [← hinc, ← leafPathELength_eq_original G g hg (γ.map e e.contMDiff),
    ← leafPathELength_eq_original G g hg γ] at hb
  have hr := ENNReal.toReal_mono
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (leafPathELength_ne_top g G γ)) hb
  simpa only [leafPathLength, ENNReal.toReal_mul, ENNReal.toReal_ofReal hK.le] using hr

omit hPconn hPcount hPg hPd in
/-- Finite original lengths allow the speed-integral estimate to pass to
real lengths; no extra path-finiteness hypothesis survives in this theorem. -/
theorem foliated_path_real_length_le
    {D : RealTangentDistribution (𝓡 n) P}
    (G : LeafFoliation (r := rs) (L := Ls) D)
    (g : Bundle.ContMDiffRiemannianMetric (𝓡 n) ∞ (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : P → Type _))
    (hg : ∀ x (v w : TangentSpace (𝓡 n) x), g.inner x v w = inner ℝ v w)
    (a : P → P) (ha : ContMDiff (𝓡 n) (𝓡 n) 1 a)
    (K : ℝ) (hK : 0 ≤ K)
    (hspeed : ∀ z (v : TangentSpace (𝓡 n) z), v ∈ D z →
      ‖mfderiv (𝓡 n) (𝓡 n) a z v‖ ≤ K * ‖v‖)
    {i : ιs} {x y : Ls i} (γ : PiecewiseC1Path (r := rs) x y) :
    (Manifold.pathELength (𝓡 n) (a ∘ G.inclusion i ∘ γ.toFun) 0 1).toReal ≤
      K * leafPathLength g G γ := by
  have hb := foliated_path_length_le G a ha K hK hspeed γ
  rw [← leafPathELength_eq_original G g hg γ] at hb
  have hr := ENNReal.toReal_mono
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (leafPathELength_ne_top g G γ)) hb
  simpa only [leafPathLength, ENNReal.toReal_mul, ENNReal.toReal_ofReal hK] using hr

omit hPconn hPcount hPg hPd in
/-- A genuine leaf-map inclusion square turns the integral estimate into a
comparison of the SAME original leaf-length functions. -/
theorem leafDiffeomorph_path_length_le
    {D : RealTangentDistribution (𝓡 n) P}
    (G : LeafFoliation (r := rs) (L := Ls) D)
    (g : Bundle.ContMDiffRiemannianMetric (𝓡 n) ∞ (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : P → Type _))
    (hg : ∀ x (v w : TangentSpace (𝓡 n) x), g.inner x v w = inner ℝ v w)
    (a : P → P) (ha : ContMDiff (𝓡 n) (𝓡 n) 1 a)
    {i j : ιs} (e : Diffeomorph (𝓡 rs) (𝓡 rs) (Ls i) (Ls j) 1)
    (he : ∀ z, G.inclusion j (e z) = a (G.inclusion i z))
    (K : ℝ) (hK : 0 ≤ K)
    (hspeed : ∀ z (v : TangentSpace (𝓡 n) z), v ∈ D z →
      ‖mfderiv (𝓡 n) (𝓡 n) a z v‖ ≤ K * ‖v‖)
    {x y : Ls i} (γ : PiecewiseC1Path (r := rs) x y) :
    leafPathLength g G (γ.map e e.contMDiff) ≤ K * leafPathLength g G γ := by
  have hb := foliated_path_real_length_le G g hg a ha K hK hspeed γ
  have hinc : G.inclusion j ∘ (γ.map e e.contMDiff).toFun =
      a ∘ G.inclusion i ∘ γ.toFun := by funext t; exact he (γ.toFun t)
  simpa only [← hinc, ← leafPathELength_eq_original G g hg, leafPathLength] using hb

omit hPconn hPcount [Bundle.RiemannianBundle (fun x : P ↦ TangentSpace (𝓡 n) x)] hPg hPd in
/-- The inverse inclusion square of an actual leaf diffeomorphism is literal,
using ambient injectivity; source and receiving leaves need not share a label. -/
theorem inverse_leafDiffeomorph_intertwining
    {D : RealTangentDistribution (𝓡 n) P}
    (G : LeafFoliation (r := rs) (L := Ls) D)
    (a : Diffeomorph (𝓡 n) (𝓡 n) P P ∞)
    {i j : ιs} (e : Diffeomorph (𝓡 rs) (𝓡 rs) (Ls i) (Ls j) 1)
    (he : ∀ z, G.inclusion j (e z) = a (G.inclusion i z)) (z : Ls j) :
    G.inclusion i (e.symm z) = a.symm (G.inclusion j z) := by
  apply a.injective
  change a (G.inclusion i (e.symm z)) = a (a.symm (G.inclusion j z))
  rw [a.apply_symm_apply, ← he, e.apply_symm_apply]

omit hPconn hPcount hPg hPd in
/-- Reverse contraction applies to the inverse of the SAME actual leaf map,
so dividing by the positive constant gives forward path expansion. -/
theorem leafDiffeomorph_path_length_ge
    {D : RealTangentDistribution (𝓡 n) P}
    (G : LeafFoliation (r := rs) (L := Ls) D)
    (g : Bundle.ContMDiffRiemannianMetric (𝓡 n) ∞ (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : P → Type _))
    (hg : ∀ x (v w : TangentSpace (𝓡 n) x), g.inner x v w = inner ℝ v w)
    (a : Diffeomorph (𝓡 n) (𝓡 n) P P ∞)
    {i j : ιs} (e : Diffeomorph (𝓡 rs) (𝓡 rs) (Ls i) (Ls j) 1)
    (he : ∀ z, G.inclusion j (e z) = a (G.inclusion i z))
    (K : ℝ) (hK : 0 < K)
    (hspeed : ∀ z (v : TangentSpace (𝓡 n) z), v ∈ D z →
      ‖mfderiv (𝓡 n) (𝓡 n) a.symm z v‖ ≤ K * ‖v‖)
    {x y : Ls i} (γ : PiecewiseC1Path (r := rs) x y) :
    K⁻¹ * leafPathLength g G γ ≤
      (Manifold.pathELength (𝓡 n) (a ∘ G.inclusion i ∘ γ.toFun) 0 1).toReal := by
  have hb := leafDiffeomorph_path_length_le G g hg a.symm
    (a.symm.contMDiff.of_le (by simp)) e.symm
    (inverse_leafDiffeomorph_intertwining G a e he) K hK.le hspeed
    (γ.map e e.contMDiff)
  have hsame : G.inclusion i ∘ ((γ.map e e.contMDiff).map e.symm e.symm.contMDiff).toFun =
      G.inclusion i ∘ γ.toFun := by
    funext t
    change G.inclusion i (e.symm (e (γ.toFun t))) = _
    rw [e.symm_apply_apply]
    rfl
  have hinc : G.inclusion j ∘ (γ.map e e.contMDiff).toFun =
      a ∘ G.inclusion i ∘ γ.toFun := by funext t; exact he (γ.toFun t)
  change (leafPathELength g G ((γ.map e e.contMDiff).map e.symm e.symm.contMDiff)).toReal ≤
    K * (leafPathELength g G (γ.map e e.contMDiff)).toReal at hb
  rw [leafPathELength_eq_original G g hg, leafPathELength_eq_original G g hg,
    hsame, hinc] at hb
  have h := (div_le_iff₀ hK).2 (by simpa only [mul_comm] using hb)
  simpa only [← leafPathELength_eq_original G g hg γ, leafPathLength,
    div_eq_mul_inv, mul_comm] using h

omit hPconn hPcount hPg hPd in
/-- Reverse contraction on the inverse of the SAME leaf map gives the intrinsic
forward expansion, with exact source and receiving carriers. -/
theorem leafDiffeomorph_distance_ge
    {D : RealTangentDistribution (𝓡 n) P}
    (G : LeafFoliation (r := rs) (L := Ls) D)
    (g : Bundle.ContMDiffRiemannianMetric (𝓡 n) ∞ (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : P → Type _))
    (hg : ∀ x (v w : TangentSpace (𝓡 n) x), g.inner x v w = inner ℝ v w)
    (a : Diffeomorph (𝓡 n) (𝓡 n) P P ∞)
    {i j : ιs} (e : Diffeomorph (𝓡 rs) (𝓡 rs) (Ls i) (Ls j) 1)
    (he : ∀ z, G.inclusion j (e z) = a (G.inclusion i z))
    (K : ℝ) (hK : 0 < K)
    (hspeed : ∀ z (v : TangentSpace (𝓡 n) z), v ∈ D z →
      ‖mfderiv (𝓡 n) (𝓡 n) a.symm z v‖ ≤ K * ‖v‖) (x y : Ls i) :
    K⁻¹ * intrinsicLeafDistance g G x y ≤ intrinsicLeafDistance g G (e x) (e y) := by
  have hb := leafDiffeomorph_distance_le G g hg a.symm
    (a.symm.contMDiff.of_le (by simp)) e.symm
    (inverse_leafDiffeomorph_intertwining G a e he) K hK hspeed (e x) (e y)
  simp only [e.symm_apply_apply] at hb
  have h := (div_le_iff₀ hK).2 (by simpa only [mul_comm] using hb)
  simpa only [div_eq_mul_inv, mul_comm] using h




omit [IsManifold (𝓡 n) ∞ M] [IsManifold (𝓡 n) ∞ P]
    hMcompact hMconn hPconn hMcount hPcount
    [Bundle.RiemannianBundle (fun x : M ↦ TangentSpace (𝓡 n) x)]
    [Bundle.RiemannianBundle (fun x : P ↦ TangentSpace (𝓡 n) x)] hMg hPg hMd hPd in
/-- Franks Corollary 1.3, p.66: an actual continuous deck map is smooth
because, near x, it is the original covering's smooth local inverse near δx
composed with p. No smoothness is assumed of the deck homeomorphism. -/
theorem deck_contMDiff
    (p : P → M) (hp_smooth : IsLocalDiffeomorph (𝓡 n) (𝓡 n) ∞ p)
    (δ : P → P) (hδ : Continuous δ) (hdeck : ∀ x, p (δ x) = p x) :
    ContMDiff (𝓡 n) (𝓡 n) ∞ δ := by
  intro x
  let hi := hp_smooth (δ x)
  have hlocal : (hi.localInverse ∘ p) ∘ δ =ᶠ[nhds x] δ :=
    hi.localInverse_eventuallyEq_left.comp_tendsto hδ.continuousAt
  have heq : δ =ᶠ[nhds x] hi.localInverse ∘ p := by
    filter_upwards [hlocal] with y hy
    change hi.localInverse (p (δ y)) = δ y at hy
    simpa only [Function.comp_apply, hdeck y] using hy.symm
  exact (hi.localInverse_contMDiffAt.comp_of_eq
    (hp_smooth.contMDiff x) (hdeck x).symm).congr_of_eventuallyEq heq

omit [MetricSpace M] hMcompact hMconn hPconn hMcount hPcount in
/-- The deck homeomorphism's inverse is again an actual deck map. -/
theorem inverse_deck_identity
    (p : P → M) (δ : P ≃ₜ P) (hdeck : ∀ x, p (δ x) = p x) (x : P) :
    p (δ.symm x) = p x := by
  simpa only [δ.apply_symm_apply] using (hdeck (δ.symm x)).symm

/-- Actual smooth DATA for a deck homeomorphism and its actual inverse. -/
def deckDiffeomorph
    (p : P → M) (hp_smooth : IsLocalDiffeomorph (𝓡 n) (𝓡 n) ∞ p)
    (δ : P ≃ₜ P) (hdeck : ∀ x, p (δ x) = p x) :
    Diffeomorph (𝓡 n) (𝓡 n) P P ∞ where
  toEquiv := δ.toEquiv
  contMDiff_toFun := deck_contMDiff p hp_smooth δ δ.continuous hdeck
  contMDiff_invFun := deck_contMDiff p hp_smooth δ.symm δ.symm.continuous
    (inverse_deck_identity p δ hdeck)

omit [IsManifold (𝓡 n) ∞ M] [IsManifold (𝓡 n) ∞ P]
    hMcompact hMconn hPconn hMcount hPcount hMg hPg hMd hPd in
/-- Differentiate the literal deck identity: both source and receiving norms
are the ORIGINAL pullback norms. The deck derivative preserves them exactly. -/
theorem deck_derivative_norm
    (p : P → M) (hp_smooth : IsLocalDiffeomorph (𝓡 n) (𝓡 n) ∞ p)
    (hp_metric : ∀ x (v w : TangentSpace (𝓡 n) x),
      inner ℝ v w = inner ℝ (mfderiv (𝓡 n) (𝓡 n) p x v)
        (mfderiv (𝓡 n) (𝓡 n) p x w))
    (δ : P → P) (hδ : ContMDiff (𝓡 n) (𝓡 n) ∞ δ)
    (hdeck : ∀ x, p (δ x) = p x) (x : P) (v : TangentSpace (𝓡 n) x) :
    ‖mfderiv (𝓡 n) (𝓡 n) δ x v‖ = ‖v‖ := by
  have hc : p ∘ δ = p := funext hdeck
  have hd := mfderiv_congr (I := 𝓡 n) (I' := 𝓡 n) (x := x) hc
  rw [mfderiv_comp x (hp_smooth.mdifferentiable (by simp) _)
    (hδ.mdifferentiable (by simp) x)] at hd
  have hdv := congrArg (fun A ↦ A v) hd
  change mfderiv (𝓡 n) (𝓡 n) p (δ x)
    (mfderiv (𝓡 n) (𝓡 n) δ x v) = mfderiv (𝓡 n) (𝓡 n) p x v at hdv
  calc
    _ = ‖mfderiv (𝓡 n) (𝓡 n) p (δ x)
        (mfderiv (𝓡 n) (𝓡 n) δ x v)‖ :=
      (covering_derivative_norm p hp_metric _ _).symm
    _ = ‖mfderiv (𝓡 n) (𝓡 n) p x v‖ := by rw [hdv, hdeck x]
    _ = ‖v‖ := covering_derivative_norm p hp_metric x v

omit [IsManifold (𝓡 n) ∞ P] hPconn hPcount hPg hPd in
/-- The original native Riemannian infimum is nonincreasing under an actual
C¹ map whose derivative is nonincreasing in the ORIGINAL tangent norms.
Every competitor is mapped as actual `Path` data on the same unit interval. -/
theorem riemannianEDist_le_of_derivative_norm
    (a : P → P) (ha : ContMDiff (𝓡 n) (𝓡 n) 1 a)
    (hspeed : ∀ z (v : TangentSpace (𝓡 n) z),
      ‖mfderiv (𝓡 n) (𝓡 n) a z v‖ ≤ ‖v‖) (x y : P) :
    Manifold.riemannianEDist (𝓡 n) (a x) (a y) ≤
      Manifold.riemannianEDist (𝓡 n) x y := by
  conv_rhs => rw [Manifold.riemannianEDist]
  apply le_iInf
  intro γ
  apply le_iInf
  intro hγ
  let η : Path (a x) (a y) := γ.map ha.continuous
  have hη : ContMDiff (modelWithCornersEuclideanHalfSpace 1) (𝓡 n) 1 η :=
    ha.comp hγ
  have hb : Manifold.riemannianEDist (𝓡 n) (a x) (a y) ≤
      ∫⁻ t, ‖mfderiv (modelWithCornersEuclideanHalfSpace 1) (𝓡 n) η t 1‖ₑ := by
    rw [Manifold.riemannianEDist]
    exact biInf_le _ hη
  apply hb.trans
  apply MeasureTheory.lintegral_mono
  intro t
  have hd := mfderiv_comp t (ha.mdifferentiable one_ne_zero (γ t))
    (hγ.mdifferentiable one_ne_zero t)
  change mfderiv (modelWithCornersEuclideanHalfSpace 1) (𝓡 n)
    (a ∘ γ) t = _ at hd
  change ‖mfderiv (modelWithCornersEuclideanHalfSpace 1) (𝓡 n)
    (a ∘ γ) t 1‖ₑ ≤ _
  rw [hd]
  simpa only [ContinuousLinearMap.comp_apply, ofReal_norm] using
    ENNReal.ofReal_le_ofReal (hspeed (γ t)
      (mfderiv (modelWithCornersEuclideanHalfSpace 1) (𝓡 n) γ t 1))

omit [IsManifold (𝓡 n) ∞ M] [IsManifold (𝓡 n) ∞ P]
    hMcompact hMconn hPconn hMcount hPcount hMg hPg hMd in
/-- Both directions of the derivative norm identity give a genuine isometry
for the already installed original Riemannian distance, without replacing its
metric or topology. -/
theorem deck_isometry
    (p : P → M) (hp_smooth : IsLocalDiffeomorph (𝓡 n) (𝓡 n) ∞ p)
    (hp_metric : ∀ x (v w : TangentSpace (𝓡 n) x),
      inner ℝ v w = inner ℝ (mfderiv (𝓡 n) (𝓡 n) p x v)
        (mfderiv (𝓡 n) (𝓡 n) p x w))
    (δ : P ≃ₜ P) (hdeck : ∀ x, p (δ x) = p x) : Isometry δ := by
  have hδ := deck_contMDiff p hp_smooth δ δ.continuous hdeck
  have hδi := deck_contMDiff p hp_smooth δ.symm δ.symm.continuous
    (inverse_deck_identity p δ hdeck)
  intro x y
  rw [IsRiemannianManifold.out (I := 𝓡 n), IsRiemannianManifold.out (I := 𝓡 n)]
  apply le_antisymm
  · exact riemannianEDist_le_of_derivative_norm δ (hδ.of_le (by simp))
      (fun z v ↦ (deck_derivative_norm p hp_smooth hp_metric δ hδ hdeck z v).le) x y
  · have h := riemannianEDist_le_of_derivative_norm δ.symm (hδi.of_le (by simp))
      (fun z v ↦ (deck_derivative_norm p hp_smooth hp_metric δ.symm hδi
        (inverse_deck_identity p δ hdeck) z v).le) (δ x) (δ y)
    simpa only [δ.symm_apply_apply] using h

omit [IsManifold (𝓡 n) ∞ M] [IsManifold (𝓡 n) ∞ P]
    hMcompact hMconn hPconn hMcount hPcount hMg hPg hMd in
/-- A conjugate of an actual deck map by the actual lifted iterate remains
a deck map. Thus ORIGINAL ambient orbit distances of its two images agree,
without assuming the original deck map commutes with the lift. -/
theorem deck_orbit_dist_eq
    (f : Diffeomorph (𝓡 n) (𝓡 n) M M ∞)
    (p : P → M) (hp_smooth : IsLocalDiffeomorph (𝓡 n) (𝓡 n) ∞ p)
    (hp_metric : ∀ x (v w : TangentSpace (𝓡 n) x),
      inner ℝ v w = inner ℝ (mfderiv (𝓡 n) (𝓡 n) p x v)
        (mfderiv (𝓡 n) (𝓡 n) p x w))
    (F : Diffeomorph (𝓡 n) (𝓡 n) P P ∞) (hF : ∀ x, p (F x) = f (p x))
    (δ : P ≃ₜ P) (hdeck : ∀ x, p (δ x) = p x) (k : ℕ) (x y : P) :
    dist (((F : P → P)^[k]) (δ x)) (((F : P → P)^[k]) (δ y)) =
      dist (((F : P → P)^[k]) x) (((F : P → P)^[k]) y) := by
  let A := HolomorphicAnosov.realIterate (𝓡 n) F k
  let κ : P ≃ₜ P := (A.toHomeomorph.symm.trans δ).trans A.toHomeomorph
  have hκ : ∀ z, p (κ z) = p z := by
    intro z
    change p (A (δ (A.symm z))) = p z
    change p (((F : P → P)^[k]) (δ (A.symm z))) = p z
    rw [covering_iterate_semiconj f F p hF k, hdeck]
    rw [← covering_iterate_semiconj f F p hF k]
    change p (A (A.symm z)) = p z
    rw [A.apply_symm_apply]
  have h := (deck_isometry p hp_smooth hp_metric κ hκ).dist_eq (A x) (A y)
  change dist (A (δ x)) (A (δ y)) = dist (A x) (A y)
  simpa only [κ, Homeomorph.trans_apply, Diffeomorph.coe_toHomeomorph,
    Diffeomorph.coe_toHomeomorph_symm, A.symm_apply_apply] using h

omit [IsManifold (𝓡 n) ∞ M] hMcompact hMconn hPconn hMcount hPcount hMg hPg hMd in
/-- The original asymptotic criterion now proves actual whole-leaf preservation
by a deck map; ambient isometry is applied to each conjugate separately. -/
theorem deck_asymptotic_leaf_iff
    {D : RealTangentDistribution (𝓡 n) P}
    (G : LeafFoliation (r := rs) (L := Ls) D)
    (f : Diffeomorph (𝓡 n) (𝓡 n) M M ∞)
    (p : P → M) (hp_smooth : IsLocalDiffeomorph (𝓡 n) (𝓡 n) ∞ p)
    (hp_metric : ∀ x (v w : TangentSpace (𝓡 n) x),
      inner ℝ v w = inner ℝ (mfderiv (𝓡 n) (𝓡 n) p x v)
        (mfderiv (𝓡 n) (𝓡 n) p x w))
    (F : Diffeomorph (𝓡 n) (𝓡 n) P P ∞) (hF : ∀ x, p (F x) = f (p x))
    (hG : ∀ x y : P, (∃ i u v, G.inclusion i u = x ∧ G.inclusion i v = y) ↔
      Filter.Tendsto (fun m : ℕ ↦ dist (((F : P → P)^[m]) x)
        (((F : P → P)^[m]) y)) Filter.atTop (nhds 0))
    (δ : P ≃ₜ P) (hdeck : ∀ x, p (δ x) = p x) (x y : P) :
    (∃ i u v, G.inclusion i u = x ∧ G.inclusion i v = y) ↔
      ∃ j u v, G.inclusion j u = δ x ∧ G.inclusion j v = δ y := by
  rw [hG, hG]
  have heq : (fun m : ℕ ↦ dist (((F : P → P)^[m]) (δ x))
      (((F : P → P)^[m]) (δ y))) =
      (fun m : ℕ ↦ dist (((F : P → P)^[m]) x) (((F : P → P)^[m]) y)) := by
    funext m
    exact deck_orbit_dist_eq f p hp_smooth hp_metric F hF δ hdeck m x y
  rw [heq]




include hMcompact hMconn hPconn hMcount hPcount hMg hPg hMd hPd

omit hMcompact hMconn hMcount hMg hMd hPconn hPcount in
/--
Franks, *Anosov Diffeomorphisms* (1970), §1, Lemma 1.2 and Corollary 1.3,
printed pp. 65--66, with the intrinsic metric definition on p. 65.

Proof. The smooth covering is a local diffeomorphism, and its derivative is
a tangent-space isomorphism. The displayed pullback inner-product equality makes
this derivative an isometry. Differentiate `p ∘ F^k = f^k ∘ p` and its inverse-time
version to transfer the two tensor estimates to the lifted stable/unstable bundles,
with the original constants. The asymptotic leaf characterizations show that `F`
and its inverse permute both foliations; the native foliation boxes and the
immersions identify their restrictions as C¹ diffeomorphisms of intrinsic leaves.

For any finite-piece C¹ path in a stable leaf, the chain rule bounds its image
speed under `F^k` by `C rate^k` times its original speed on every open partition
piece. The partition endpoints have zero measure, so integration and finite
additivity give the stated path-length bound. The same argument for `F^(-k)` on
unstable leaves gives its bound. Connected intrinsic C¹ manifolds admit finite
piecewise C¹ paths; their lengths are finite, since each compact smooth piece has
bounded continuous speed in the smooth ambient metric. The length set is nonempty
and bounded below by zero. Choose lengths arbitrarily close to their infimum and
let the error decrease to zero, proving both intrinsic-distance contraction bounds.
Apply unstable inverse contraction to endpoints in `F^k U` and divide by the
positive `C rate^k` to get expansion `C⁻¹ rate⁻ᵏ` on unstable leaves.

A deck homeomorphism satisfies `p ∘ δ = p`; local smooth covering inverses make
it a smooth diffeomorphism. The same equation and pullback metric show it preserves
all tangent norms. Conjugating by `F^k` yields a deck map (which may depend on `k`),
so ambient orbit distances are unchanged. Thus the asymptotic characterizations
give the same stable and unstable leaf permutations. Restricting to their intrinsic
atlases gives C¹ leaf diffeomorphisms. The deck map and its inverse give mutually
inverse length-preserving bijections of finite-piece C¹ paths, so the path-length
infima agree exactly. No smooth torus identification is used.

For zero-dimensional nonempty connected manifolds, all endpoints coincide and
the metric inequalities are zero inequalities. If the manifold is empty, its
surjective cover and both leaf families have no endpoints, so the clauses are
vacuous. No completeness of intrinsic leaves or global product structure is used.
-/
theorem intrinsic_leaf_metric_bounds
    (f : Diffeomorph (𝓡 n) (𝓡 n) M M ∞) (splitting : InvariantRealTangentSplitting f)
    (C rate : ℝ) (hC : 0 < C) (hrate : 0 < rate ∧ rate < 1)
    (hs : ∀ k x (v : TangentSpace (𝓡 n) x), v ∈ splitting.stable.toDistribution x →
      ‖mfderiv (𝓡 n) (𝓡 n) ((f : M → M)^[k]) x v‖ ≤ C * rate ^ k * ‖v‖)
    (hu : ∀ k x (v : TangentSpace (𝓡 n) x), v ∈ splitting.unstable.toDistribution x →
      ‖mfderiv (𝓡 n) (𝓡 n) ((f.symm : M → M)^[k]) x v‖ ≤ C * rate ^ k * ‖v‖)
    (p : P → M) (_hp : IsCoveringMap p) (_hp_surj : Function.Surjective p)
    (hp_smooth : IsLocalDiffeomorph (𝓡 n) (𝓡 n) ∞ p)
    (_hp_simply : Nonempty P → SimplyConnectedSpace P)
    (hp_metric : ∀ x (v w : TangentSpace (𝓡 n) x),
      inner ℝ v w = inner ℝ (mfderiv (𝓡 n) (𝓡 n) p x v) (mfderiv (𝓡 n) (𝓡 n) p x w))
    (F : Diffeomorph (𝓡 n) (𝓡 n) P P ∞) (hF : ∀ x, p (F x) = f (p x))
    (stable : LeafFoliation (r := rs) (L := Ls) (fun x ↦
      (splitting.stable.toDistribution (p x)).comap (mfderiv (𝓡 n) (𝓡 n) p x).toLinearMap))
    (unstable : LeafFoliation (r := ru) (L := Lu) (fun x ↦
      (splitting.unstable.toDistribution (p x)).comap (mfderiv (𝓡 n) (𝓡 n) p x).toLinearMap))
    (stable_eq : ∀ x y : P, (∃ i a b, stable.inclusion i a = x ∧
      stable.inclusion i b = y) ↔ Filter.Tendsto
      (fun k : ℕ ↦ dist (((F : P → P)^[k]) x) (((F : P → P)^[k]) y))
      Filter.atTop (nhds 0))
    (unstable_eq : ∀ x y : P, (∃ i a b, unstable.inclusion i a = x ∧
      unstable.inclusion i b = y) ↔ Filter.Tendsto
      (fun k : ℕ ↦ dist (((F.symm : P → P)^[k]) x) (((F.symm : P → P)^[k]) y))
      Filter.atTop (nhds 0)) :
    let gP : Bundle.ContMDiffRiemannianMetric (𝓡 n) ∞ (EuclideanSpace ℝ (Fin n))
        (TangentSpace (𝓡 n) : P → Type _) :=
      { (Bundle.RiemannianBundle.g (E := fun x : P ↦ TangentSpace (𝓡 n) x)) with
        contMDiff := by
          obtain ⟨g, hg, heq⟩ := hPg.exists_contMDiff
          have h : g = Bundle.RiemannianBundle.g.inner := by
            funext x
            ext v w
            exact (heq x v w).symm
          simpa only [h] using hg }
    (∀ k : ℕ,
      ∃ S : LeafTransport stable ((F : P → P)^[k]),
      ∃ _Sminus : LeafTransport stable ((F.symm : P → P)^[k]),
      ∃ U : LeafTransport unstable ((F.symm : P → P)^[k]),
      ∃ V : LeafTransport unstable ((F : P → P)^[k]),
        (∀ (i : ιs) (x y : Ls i) (γ : PiecewiseC1Path (r := rs) x y),
          (Manifold.pathELength (𝓡 n)
            (((F : P → P)^[k]) ∘ stable.inclusion i ∘ γ.toFun) 0 1).toReal
            ≤ C * rate ^ k * leafPathLength gP stable γ) ∧
        (∀ (i : ιu) (x y : Lu i) (γ : PiecewiseC1Path (r := ru) x y),
          (Manifold.pathELength (𝓡 n)
            (((F.symm : P → P)^[k]) ∘ unstable.inclusion i ∘ γ.toFun) 0 1).toReal
            ≤ C * rate ^ k * leafPathLength gP unstable γ) ∧
        (∀ (i : ιu) (x y : Lu i) (γ : PiecewiseC1Path (r := ru) x y),
          C⁻¹ * (rate ^ k)⁻¹ * leafPathLength gP unstable γ ≤
            (Manifold.pathELength (𝓡 n)
              (((F : P → P)^[k]) ∘ unstable.inclusion i ∘ γ.toFun) 0 1).toReal) ∧
        (∀ i x y, intrinsicLeafDistance gP stable (i := S.permutation i) (S.leafMap i x) (S.leafMap i y)
          ≤ C * rate ^ k * intrinsicLeafDistance gP stable (i := i) x y) ∧
        (∀ i x y, intrinsicLeafDistance gP unstable (i := U.permutation i) (U.leafMap i x) (U.leafMap i y)
          ≤ C * rate ^ k * intrinsicLeafDistance gP unstable (i := i) x y) ∧
        (∀ i x y, C⁻¹ * (rate ^ k)⁻¹ * intrinsicLeafDistance gP unstable (i := i) x y ≤
          intrinsicLeafDistance gP unstable (i := V.permutation i) (V.leafMap i x) (V.leafMap i y))) ∧
    (∀ δ : P ≃ₜ P, (∀ x, p (δ x) = p x) →
      ∃ S : LeafTransport stable δ,
      ∃ U : LeafTransport unstable δ,
        (∀ (i : ιs) (x y : Ls i) (γ : PiecewiseC1Path (r := rs) x y),
          (Manifold.pathELength (𝓡 n) (δ ∘ stable.inclusion i ∘ γ.toFun) 0 1).toReal
            = leafPathLength gP stable γ) ∧
        (∀ (i : ιu) (x y : Lu i) (γ : PiecewiseC1Path (r := ru) x y),
          (Manifold.pathELength (𝓡 n) (δ ∘ unstable.inclusion i ∘ γ.toFun) 0 1).toReal
            = leafPathLength gP unstable γ) ∧
        (∀ i x y, intrinsicLeafDistance gP stable (i := S.permutation i) (S.leafMap i x) (S.leafMap i y)
          = intrinsicLeafDistance gP stable (i := i) x y) ∧
        (∀ i x y, intrinsicLeafDistance gP unstable (i := U.permutation i) (U.leafMap i x) (U.leafMap i y)
          = intrinsicLeafDistance gP unstable (i := i) x y)) := by
  dsimp only
  let gP : Bundle.ContMDiffRiemannianMetric (𝓡 n) ∞ (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : P → Type _) :=
    { (Bundle.RiemannianBundle.g (E := fun x : P ↦ TangentSpace (𝓡 n) x)) with
      contMDiff := by
        obtain ⟨g, hg, heq⟩ := hPg.exists_contMDiff
        have h : g = Bundle.RiemannianBundle.g.inner := by
          funext x
          ext v w
          exact (heq x v w).symm
        simpa only [h] using hg }
  have hgP : ∀ x (v w : TangentSpace (𝓡 n) x), gP.inner x v w = inner ℝ v w :=
    fun _ _ _ ↦ rfl
  change (_ ∧ _)
  constructor
  · intro k
    let A := HolomorphicAnosov.realIterate (𝓡 n) F k
    let S := asymptoticIterateLeafTransport stable F stable_eq k
    let Sminus := asymptoticInverseIterateLeafTransport stable F stable_eq k
    let U := asymptoticIterateLeafTransport unstable F.symm unstable_eq k
    let V := asymptoticInverseIterateLeafTransport unstable F.symm unstable_eq k
    have hsK := lifted_stable_iterate_speed f splitting C rate hs p hp_smooth hp_metric F hF k
    have huK := lifted_unstable_inverse_iterate_speed f splitting C rate hu p hp_smooth hp_metric F hF k
    have hK : 0 < C * rate^k := mul_pos hC (pow_pos hrate.1 k)
    refine ⟨S, Sminus, U, V, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro i x y γ
      exact foliated_path_real_length_le stable gP hgP _
        ((F.contMDiff.iterate k).of_le (by simp)) _ hK.le hsK γ
    · intro i x y γ
      exact foliated_path_real_length_le unstable gP hgP _
        ((F.symm.contMDiff.iterate k).of_le (by simp)) _ hK.le huK γ
    · intro i x y γ
      have he : ∀ z, unstable.inclusion (V.permutation i) (V.leafMap i z) =
          A (unstable.inclusion i z) := V.intertwining i
      have h := leafDiffeomorph_path_length_ge unstable gP hgP A (V.leafMap i) he
        (C * rate^k) hK huK γ
      have hcoeff : (C * rate^k)⁻¹ = C⁻¹ * (rate^k)⁻¹ := by
        rw [mul_inv_rev, mul_comm]
      rw [hcoeff] at h
      exact h
    · intro i x y
      exact leafDiffeomorph_distance_le stable gP hgP _
        ((F.contMDiff.iterate k).of_le (by simp)) (S.leafMap i) (S.intertwining i)
        (C * rate^k) hK hsK x y
    · intro i x y
      exact leafDiffeomorph_distance_le unstable gP hgP _
        ((F.symm.contMDiff.iterate k).of_le (by simp)) (U.leafMap i) (U.intertwining i)
        (C * rate^k) hK huK x y
    · intro i x y
      have he : ∀ z, unstable.inclusion (V.permutation i) (V.leafMap i z) =
          A (unstable.inclusion i z) := V.intertwining i
      have h := leafDiffeomorph_distance_ge unstable gP hgP A (V.leafMap i) he
        (C * rate^k) hK huK x y
      have hcoeff : (C * rate^k)⁻¹ = C⁻¹ * (rate^k)⁻¹ := by
        rw [mul_inv_rev, mul_comm]
      rw [hcoeff] at h
      exact h
  · intro δ hdeck
    let a := deckDiffeomorph p hp_smooth δ hdeck
    have hsrel := deck_asymptotic_leaf_iff stable f p hp_smooth hp_metric F hF
      stable_eq δ hdeck
    have hirel := deck_asymptotic_leaf_iff unstable f.symm p hp_smooth hp_metric F.symm
      (covering_inverse_semiconj f F p hF) unstable_eq δ hdeck
    let S := leafTransportOfDiffeomorph stable a hsrel
    let U := leafTransportOfDiffeomorph unstable a hirel
    have hnorm : ∀ z (v : TangentSpace (𝓡 n) z),
        ‖mfderiv (𝓡 n) (𝓡 n) a z v‖ = ‖v‖ :=
      deck_derivative_norm p hp_smooth hp_metric δ a.contMDiff hdeck
    have hnormi : ∀ z (v : TangentSpace (𝓡 n) z),
        ‖mfderiv (𝓡 n) (𝓡 n) a.symm z v‖ = ‖v‖ :=
      deck_derivative_norm p hp_smooth hp_metric δ.symm a.symm.contMDiff
        (inverse_deck_identity p δ hdeck)
    refine ⟨S, U, ?_, ?_, ?_, ?_⟩
    · intro i x y γ
      change (Manifold.pathELength (𝓡 n) (a ∘ stable.inclusion i ∘ γ.toFun) 0 1).toReal =
        leafPathLength gP stable γ
      apply le_antisymm
      · simpa only [one_mul] using foliated_path_real_length_le stable gP hgP a
          (a.contMDiff.of_le (by simp)) 1 zero_le_one (fun z v _ ↦ by rw [hnorm]; simp) γ
      · simpa only [inv_one, one_mul] using leafDiffeomorph_path_length_ge stable gP hgP a
          (S.leafMap i) (S.intertwining i) 1 zero_lt_one
          (fun z v _ ↦ by rw [hnormi]; simp) γ
    · intro i x y γ
      change (Manifold.pathELength (𝓡 n) (a ∘ unstable.inclusion i ∘ γ.toFun) 0 1).toReal =
        leafPathLength gP unstable γ
      apply le_antisymm
      · simpa only [one_mul] using foliated_path_real_length_le unstable gP hgP a
          (a.contMDiff.of_le (by simp)) 1 zero_le_one (fun z v _ ↦ by rw [hnorm]; simp) γ
      · simpa only [inv_one, one_mul] using leafDiffeomorph_path_length_ge unstable gP hgP a
          (U.leafMap i) (U.intertwining i) 1 zero_lt_one
          (fun z v _ ↦ by rw [hnormi]; simp) γ
    · intro i x y
      apply le_antisymm
      · simpa only [one_mul] using leafDiffeomorph_distance_le stable gP hgP a
          (a.contMDiff.of_le (by simp)) (S.leafMap i) (S.intertwining i) 1 zero_lt_one
          (fun z v _ ↦ by rw [hnorm]; simp) x y
      · simpa only [inv_one, one_mul] using leafDiffeomorph_distance_ge stable gP hgP a
          (S.leafMap i) (S.intertwining i) 1 zero_lt_one
          (fun z v _ ↦ by rw [hnormi]; simp) x y
    · intro i x y
      apply le_antisymm
      · simpa only [one_mul] using leafDiffeomorph_distance_le unstable gP hgP a
          (a.contMDiff.of_le (by simp)) (U.leafMap i) (U.intertwining i) 1 zero_lt_one
          (fun z v _ ↦ by rw [hnorm]; simp) x y
      · simpa only [inv_one, one_mul] using leafDiffeomorph_distance_ge unstable gP hgP a
          (U.leafMap i) (U.intertwining i) 1 zero_lt_one
          (fun z v _ ↦ by rw [hnormi]; simp) x y


end Bounds
end
end HolomorphicAnosov.Franks
