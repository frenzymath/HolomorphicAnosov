import HolomorphicAnosov.Dynamics.Anosov.NativeSmoothLamination
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.Separation.Hausdorff

noncomputable section
open Set

namespace HolomorphicAnosov.HPS

/-- Two continuous sections of the same projection on a connected domain agree
once they meet, provided the first section has open image in the Hausdorff
receiving space.

DAG node: `topo.connected_sections_eq_of_open_range_g4`.

Source: the open-and-closed plaque continuation argument in HPS, Invariant
Manifolds (1977), §7, pp.115–116. The equalizer is closed by Hausdorffness. It
is also the inverse image under the second section of the first section's
open image: applying the shared projection to an intersection identifies the
parameters. The nonempty equalizer is therefore the entire connected domain.
This uses the intrinsic leaf topology, with no ambient openness assumption. -/
theorem connected_sections_eq_of_open_range
    {A B : Type*} [TopologicalSpace A] [PreconnectedSpace A]
    [TopologicalSpace B] [T2Space B]
    (f g : A → B) (P : B → A) (hf : Continuous f) (hg : Continuous g)
    (hfo : IsOpen (range f)) (hPf : Function.LeftInverse P f)
    (hPg : Function.LeftInverse P g) (hmeet : ∃ a, f a = g a) : f = g := by
  have he : {a | f a = g a} = g ⁻¹' range f := by
    ext a
    constructor
    · intro h
      exact ⟨a, h⟩
    · rintro ⟨b, hb⟩
      have hba : b = a := by
        simpa only [hPf b, hPg a] using congrArg P hb
      change f a = g a
      simpa only [hba] using hb
  have hc : IsClopen {a | f a = g a} :=
    ⟨isClosed_eq hf hg, he ▸ hfo.preimage hg⟩
  have hall := hc.eq_univ hmeet
  funext a
  exact show a ∈ {a | f a = g a} from hall ▸ mem_univ a



open TopologicalSpace _root_.Topology
open scoped ContDiff Manifold Topology

universe u
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace E M]
variable [IsManifold 𝓘(ℝ, E) ∞ M]
variable {D : RealTangentDistribution 𝓘(ℝ, E) M}
variable {ι : Type u} {L : ι → Type u} {r : ι → ℕ}
variable [∀ i, TopologicalSpace (L i)]
variable [∀ i, ChartedSpace (Fin (r i) → ℝ) (L i)]
variable [∀ i, IsManifold 𝓘(ℝ, Fin (r i) → ℝ) ∞ (L i)]

/-- Local data obtained by projecting a finite-C¹ plaque family onto fixed
stable coordinates and applying the parameter inverse theorem. All maps and
intrinsic charts are supplied as actual data. -/
structure ProjectedNativePlaqueFamily
    (F : LeafPartition D ι L r) (x : M) (d k : ℕ) where
  centers : Opens M
  center_mem : x ∈ centers
  ambientChart : OpenPartialHomeomorph M ((Fin d → ℝ) × (Fin k → ℝ))
  centers_source : (centers : Set M) ⊆ ambientChart.source
  chart_center : ambientChart x = (0, 0)
  radius : ℝ
  radius_pos : 0 < radius
  label : centers → ι
  plaque : ∀ p, Opens (L (label p))
  chart : ∀ p, Diffeomorph 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, Fin (r (label p)) → ℝ)
    (⟨Metric.ball 0 radius, Metric.isOpen_ball⟩ : Opens (Fin d → ℝ)) (plaque p) ∞
  continuous_values : Continuous (fun z : centers × Metric.ball (0 : Fin d → ℝ) radius ↦
    (F.leaf (label z.1)).inclusion (chart z.1 z.2))
  values_source : ∀ p v, (F.leaf (label p)).inclusion (chart p v) ∈ ambientChart.source
  projection : ∀ p v, (ambientChart ((F.leaf (label p)).inclusion (chart p v))).1 = v.val
  center_projection_mem : ∀ p : centers, (ambientChart p.val).1 ∈ Metric.ball 0 radius
  centered : ∀ p : centers,
    (F.leaf (label p)).inclusion (chart p ⟨(ambientChart p.val).1, center_projection_mem p⟩) = p.val

namespace ProjectedNativePlaqueFamily
variable {F : LeafPartition D ι L r} {x : M} {d k : ℕ}
variable (A : ProjectedNativePlaqueFamily F x d k)

abbrev value (p : A.centers) (v : Metric.ball (0 : Fin d → ℝ) A.radius) : M :=
  (F.leaf (A.label p)).inclusion (A.chart p v)

omit [IsManifold 𝓘(ℝ, E) ∞ M] in
/-- Intrinsic open plaque charts over the same connected projection domain
agree everywhere if they meet. This is the local continuation step, including
identification of the receiving leaf by the partition law. -/
theorem values_eq_of_meet (p q : A.centers)
    (hmeet : ∃ v w, A.value p v = A.value q w) : A.value p = A.value q := by
  classical
  let B := Metric.ball (0 : Fin d → ℝ) A.radius
  let : PreconnectedSpace B := Subtype.preconnectedSpace (convex_ball (0 : Fin d → ℝ) A.radius).isPreconnected
  let z : B := ⟨0, Metric.mem_ball_self A.radius_pos⟩
  let P : M → B := fun y ↦ if h : (A.ambientChart y).1 ∈ B then ⟨_, h⟩ else z
  have hpP (a : A.centers) : Function.LeftInverse P (A.value a) := by
    intro v
    apply Subtype.ext
    dsimp only [P]
    rw [dite_eq_left (by rw [A.projection]; exact v.property)]
    exact A.projection a v
  obtain ⟨v, w, hvw⟩ := hmeet
  have hv : v = w := by
    apply Subtype.ext
    exact ((A.projection p v).symm.trans (congrArg (fun y ↦ (A.ambientChart y).1) hvw)).trans
      (A.projection q w)
  subst w
  have hlabels := F.disjoint (A.label p) (A.label q) (A.chart p v).val (A.chart q v).val hvw
  have hlocal (i j : ι) (U : Opens (L i)) (V : Opens (L j))
      (c : B ≃ₜ U) (e : B ≃ₜ V) (hij : i = j)
      (hcP : Function.LeftInverse P (fun a ↦ (F.leaf i).inclusion (c a)))
      (heP : Function.LeftInverse P (fun a ↦ (F.leaf j).inclusion (e a)))
      (hv : (F.leaf i).inclusion (c v) = (F.leaf j).inclusion (e v)) :
      (fun a ↦ (F.leaf i).inclusion (c a)) = (fun a ↦ (F.leaf j).inclusion (e a)) := by
    subst j
    let : T2Space (L i) := (F.leaf i).hausdorff
    have hopen : IsOpen (range (fun a : B ↦ (c a).val)) := by
      have heq : range (fun a : B ↦ (c a).val) = U := by
        ext y
        constructor
        · rintro ⟨a, rfl⟩; exact (c a).property
        · intro hy
          exact ⟨c.symm ⟨y, hy⟩, congrArg Subtype.val (c.apply_symm_apply _)⟩
      rw [heq]
      exact U.isOpen
    have hce := connected_sections_eq_of_open_range
      (fun a : B ↦ (c a).val) (fun a : B ↦ (e a).val) (P ∘ (F.leaf i).inclusion)
      (continuous_subtype_val.comp c.continuous) (continuous_subtype_val.comp e.continuous)
      hopen hcP heP ⟨v, (F.leaf i).injective hv⟩
    exact congrArg (fun h : B → L i ↦ (F.leaf i).inclusion ∘ h) hce
  exact hlocal _ _ (A.plaque p) (A.plaque q) (A.chart p).toHomeomorph
    (A.chart q).toHomeomorph hlabels (hpP p) (hpP q) hvw

/-- The fixed transverse slice on which the projected charts have centers. -/
def transverseDomain : Opens (Fin k → ℝ) :=
  ⟨{t | ((0 : Fin d → ℝ), t) ∈ A.ambientChart.target ∧
      A.ambientChart.symm (0, t) ∈ A.centers},
    (A.ambientChart.isOpen_inter_preimage_symm A.centers.isOpen).preimage
      (continuous_const.prodMk continuous_id)⟩

/-- The corresponding actual ambient center. -/
def transverseCenter (t : A.transverseDomain) : A.centers :=
  ⟨A.ambientChart.symm (0, t.val), t.property.2⟩

omit [IsManifold 𝓘(ℝ, E) ∞ M] in
/-- The transverse-slice centers vary continuously. -/
theorem transverseCenter_continuous : Continuous A.transverseCenter := by
  apply Continuous.subtype_mk
  exact A.ambientChart.symm.continuousOn.comp_continuous
    (continuous_const.prodMk continuous_subtype_val) (fun t ↦ t.property.1)

omit [IsManifold 𝓘(ℝ, E) ∞ M] in
/-- The slice centers have precisely the original transverse coordinates. -/
theorem transverseCenter_coordinates (t : A.transverseDomain) :
    A.ambientChart (A.transverseCenter t).val = (0, t.val) :=
  A.ambientChart.right_inv t.property.1

omit [IsManifold 𝓘(ℝ, E) ∞ M] in
/-- The central transversal parameter is available. -/
theorem zero_mem_transverseDomain : (0 : Fin k → ℝ) ∈ A.transverseDomain := by
  have hs : x ∈ A.ambientChart.source := A.centers_source A.center_mem
  have ht : ((0 : Fin d → ℝ), (0 : Fin k → ℝ)) ∈ A.ambientChart.target :=
    A.chart_center ▸ A.ambientChart.map_source hs
  refine ⟨ht, ?_⟩
  rw [← A.chart_center, A.ambientChart.left_inv hs]
  exact A.center_mem

/-- The common distinguished stable coordinate. -/
def zero : Metric.ball (0 : Fin d → ℝ) A.radius :=
  ⟨0, Metric.mem_ball_self A.radius_pos⟩

/-- Nearby centers whose plaque intersection with the fixed transverse plane
is itself still an allowed center. -/
def regularCenters : Opens A.centers :=
  ⟨{p | A.value p A.zero ∈ A.centers}, A.centers.isOpen.preimage
    (A.continuous_values.comp (continuous_id.prodMk continuous_const))⟩

/-- The projected product map, on its full available parameter domain. -/
def productMap (z : Metric.ball (0 : Fin d → ℝ) A.radius × A.transverseDomain) : M :=
  A.value (A.transverseCenter z.2) z.1

/-- The part of the product whose image remains an allowed center. -/
def productSource : Opens (Metric.ball (0 : Fin d → ℝ) A.radius × A.transverseDomain) :=
  ⟨A.productMap ⁻¹' A.centers, A.centers.isOpen.preimage
    (A.continuous_values.comp
      ((A.transverseCenter_continuous.comp continuous_snd).prodMk continuous_fst))⟩

/-- Explicit product coordinates on an open neighborhood of the central point.
The inverse takes a point's stable coordinate and the transverse coordinate
of its own plaque's intersection with the fixed transverse plane. -/
def productHomeomorph : A.productSource ≃ₜ A.regularCenters := by
  classical
  have hrec (p : A.centers) (v : Metric.ball (0 : Fin d → ℝ) A.radius)
      (h : A.value p v ∈ A.centers) : A.value ⟨A.value p v, h⟩ = A.value p := by
    apply A.values_eq_of_meet
    exact ⟨⟨_, A.center_projection_mem ⟨A.value p v, h⟩⟩, v, A.centered _⟩
  have ht0 (t : A.transverseDomain) : A.value (A.transverseCenter t) A.zero =
      (A.transverseCenter t).val := by
    have hc := A.centered (A.transverseCenter t)
    have hz : (⟨(A.ambientChart (A.transverseCenter t).val).1,
        A.center_projection_mem _⟩ : Metric.ball (0 : Fin d → ℝ) A.radius) = A.zero := by
      apply Subtype.ext
      exact congrArg Prod.fst (A.transverseCenter_coordinates t)
    rwa [hz] at hc
  let forward (z : A.productSource) : A.regularCenters :=
    ⟨⟨A.productMap z.val, z.property⟩, by
      change A.value ⟨A.value (A.transverseCenter z.val.2) z.val.1, z.property⟩ A.zero ∈ A.centers
      have he := congrFun (hrec (A.transverseCenter z.val.2) z.val.1 z.property) A.zero
      exact (he.trans (ht0 z.val.2)).symm ▸ (A.transverseCenter z.val.2).property⟩
  let tc (p : A.regularCenters) : A.transverseDomain :=
    ⟨(A.ambientChart (A.value p.val A.zero)).2, by
      have hc : A.ambientChart (A.value p.val A.zero) =
          (0, (A.ambientChart (A.value p.val A.zero)).2) := by
        apply Prod.ext
        · exact A.projection p.val A.zero
        · rfl
      constructor
      · rw [← hc]
        exact A.ambientChart.map_source (A.values_source p.val A.zero)
      · rw [← hc, A.ambientChart.left_inv (A.values_source p.val A.zero)]
        exact p.property⟩
  have htc (p : A.regularCenters) : (A.transverseCenter (tc p)).val = A.value p.val A.zero := by
    change A.ambientChart.symm (0, (A.ambientChart (A.value p.val A.zero)).2) = _
    have hc : (0, (A.ambientChart (A.value p.val A.zero)).2) =
        A.ambientChart (A.value p.val A.zero) := by
      apply Prod.ext
      · exact (A.projection p.val A.zero).symm
      · rfl
    rw [hc, A.ambientChart.left_inv (A.values_source p.val A.zero)]
  have htcval (p : A.regularCenters) : A.value (A.transverseCenter (tc p)) = A.value p.val := by
    have he : A.transverseCenter (tc p) = ⟨A.value p.val A.zero, p.property⟩ :=
      Subtype.ext (htc p)
    rw [he]
    exact hrec p.val A.zero p.property
  let inv (p : A.regularCenters) : A.productSource :=
    ⟨(⟨(A.ambientChart p.val.val).1, A.center_projection_mem p.val⟩, tc p), by
      change A.value (A.transverseCenter (tc p)) _ ∈ A.centers
      rw [htcval]
      exact Eq.mpr (congrArg (fun y : M ↦ y ∈ A.centers) (A.centered p.val)) p.val.property⟩
  have hto : Continuous forward := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    exact (A.continuous_values.comp
      ((A.transverseCenter_continuous.comp continuous_snd).prodMk continuous_fst)).comp
        continuous_subtype_val
  have htccont : Continuous tc := by
    apply Continuous.subtype_mk
    exact (A.ambientChart.continuousOn.comp_continuous
      (A.continuous_values.comp (continuous_subtype_val.prodMk continuous_const))
      (fun p ↦ A.values_source p.val A.zero)).snd
  have hinv : Continuous inv := by
    apply Continuous.subtype_mk
    apply Continuous.prodMk
    · apply Continuous.subtype_mk
      exact (A.ambientChart.continuousOn.comp_continuous
        (continuous_subtype_val.comp continuous_subtype_val)
        (fun p ↦ A.centers_source p.val.property)).fst
    · exact htccont
  refine { toEquiv := { toFun := forward, invFun := inv, left_inv := ?_, right_inv := ?_ }
           continuous_toFun := hto, continuous_invFun := hinv }
  · intro z
    apply Subtype.ext
    apply Prod.ext
    · apply Subtype.ext
      exact A.projection (A.transverseCenter z.val.2) z.val.1
    · apply Subtype.ext
      change (A.ambientChart (A.value ⟨A.value (A.transverseCenter z.val.2) z.val.1,
        z.property⟩ A.zero)).2 = z.val.2.val
      have he := congrFun (hrec (A.transverseCenter z.val.2) z.val.1 z.property) A.zero
      exact congrArg (fun y ↦ (A.ambientChart y).2) (he.trans (ht0 z.val.2)) |>.trans
        (congrArg Prod.snd (A.transverseCenter_coordinates z.val.2))
  · intro p
    apply Subtype.ext
    apply Subtype.ext
    change A.value (A.transverseCenter (tc p)) _ = p.val.val
    rw [htcval]
    exact A.centered p.val

omit [IsManifold 𝓘(ℝ, E) ∞ M] in
/-- The product parametrization is open in the original ambient topology. -/
theorem productMap_isOpenEmbedding :
    IsOpenEmbedding (fun z : A.productSource ↦ A.productMap z.val) := by
  have hi : IsOpenEmbedding (fun p : A.regularCenters ↦ p.val.val) :=
    A.centers.isOpen.isOpenEmbedding_subtypeVal.comp
      A.regularCenters.isOpen.isOpenEmbedding_subtypeVal
  exact hi.comp A.productHomeomorph.isOpenEmbedding

omit [IsManifold 𝓘(ℝ, E) ∞ M] in
/-- The central parameter is carried to the central ambient point. -/
theorem productMap_zero :
    A.productMap (A.zero, ⟨0, A.zero_mem_transverseDomain⟩) = x := by
  have hc : A.transverseCenter ⟨0, A.zero_mem_transverseDomain⟩ = ⟨x, A.center_mem⟩ := by
    apply Subtype.ext
    change A.ambientChart.symm (0, 0) = x
    rw [← A.chart_center, A.ambientChart.left_inv (A.centers_source A.center_mem)]
  change A.value (A.transverseCenter _) A.zero = x
  rw [hc]
  have hz : (⟨(A.ambientChart x).1, A.center_projection_mem ⟨x, A.center_mem⟩⟩ :
      Metric.ball (0 : Fin d → ℝ) A.radius) = A.zero := by
    apply Subtype.ext
    exact congrArg Prod.fst A.chart_center
  exact hz ▸ A.centered ⟨x, A.center_mem⟩

omit [IsManifold 𝓘(ℝ, E) ∞ M] in
/-- A rectangle of Euclidean balls fits inside the open product source.
The proof uses its original product topology and applies also in rank zero. -/
theorem exists_product_radius : ∃ ε : ℝ, 0 < ε ∧
    (Metric.ball (0 : Fin d → ℝ) ε ⊆ Metric.ball 0 A.radius) ∧
    (Metric.ball (0 : Fin k → ℝ) ε ⊆ A.transverseDomain) ∧
    ∀ (v : Fin d → ℝ) (t : Fin k → ℝ),
      v ∈ Metric.ball 0 ε → t ∈ Metric.ball 0 ε →
      ∃ z : A.productSource, z.val.1.val = v ∧ z.val.2.val = t := by
  let J : Metric.ball (0 : Fin d → ℝ) A.radius × A.transverseDomain →
      (Fin d → ℝ) × (Fin k → ℝ) := fun z ↦ (z.1.val, z.2.val)
  have hJ : IsOpenEmbedding J :=
    Metric.isOpen_ball.isOpenEmbedding_subtypeVal.prodMap
      A.transverseDomain.isOpen.isOpenEmbedding_subtypeVal
  have hQ : IsOpen (J '' (A.productSource : Set _)) :=
    hJ.isOpenMap _ A.productSource.isOpen
  have h0 : ((0 : Fin d → ℝ), (0 : Fin k → ℝ)) ∈ J '' (A.productSource : Set _) := by
    refine ⟨(A.zero, ⟨0, A.zero_mem_transverseDomain⟩), ?_, rfl⟩
    change A.productMap (A.zero, ⟨0, A.zero_mem_transverseDomain⟩) ∈ A.centers
    rw [A.productMap_zero]
    exact A.center_mem
  obtain ⟨ε, hε, hεQ⟩ := Metric.mem_nhds_iff.mp (hQ.mem_nhds h0)
  have hpair (v : Fin d → ℝ) (t : Fin k → ℝ)
      (hv : v ∈ Metric.ball 0 ε) (ht : t ∈ Metric.ball 0 ε) :
      ∃ z : A.productSource, z.val.1.val = v ∧ z.val.2.val = t := by
    have hp : (v, t) ∈ Metric.ball ((0 : Fin d → ℝ), (0 : Fin k → ℝ)) ε := by
      simpa only [Metric.mem_ball, Prod.dist_eq, max_lt_iff] using And.intro hv ht
    obtain ⟨z, hz, he⟩ := hεQ hp
    exact ⟨⟨z, hz⟩, congrArg Prod.fst he, congrArg Prod.snd he⟩
  refine ⟨ε, hε, ?_, ?_, hpair⟩
  · intro v hv
    obtain ⟨z, hz, _⟩ := hpair v 0 hv (Metric.mem_ball_self hε)
    exact hz ▸ z.val.1.property
  · intro t ht
    obtain ⟨z, _, hz⟩ := hpair 0 t (Metric.mem_ball_self hε) ht
    exact hz ▸ z.val.2.property

omit [IsManifold 𝓘(ℝ, E) ∞ M] in
/-- A normalized projected plaque family supplies a genuine connected ambient
product box at its central point. This restricts the explicit open product
homeomorphism to a rectangle of balls and restricts each intrinsic smooth
chart to the same stable ball. -/
theorem exists_native_box (A : ProjectedNativePlaqueFamily F x d k) : ∃ ε : ℝ, 0 < ε ∧
    ∃ B : NativeProductBox F d (ULift.{u} (Metric.ball (0 : Fin k → ℝ) ε)),
      x ∈ B.ambient := by
  classical
  obtain ⟨ε, hε, hεs, hεt, hεprod⟩ := exists_product_radius A
  let S : Opens (Fin d → ℝ) := ⟨Metric.ball 0 ε, Metric.isOpen_ball⟩
  let T : Opens (Fin k → ℝ) := ⟨Metric.ball 0 ε, Metric.isOpen_ball⟩
  let big : Opens (Fin d → ℝ) := ⟨Metric.ball 0 A.radius, Metric.isOpen_ball⟩
  let jS : S → big := fun v ↦ ⟨v.val, hεs v.property⟩
  let jT : T → A.transverseDomain := fun t ↦ ⟨t.val, hεt t.property⟩
  have hjS : IsOpenEmbedding jS := IsOpenEmbedding.of_comp jS
    Metric.isOpen_ball.isOpenEmbedding_subtypeVal S.isOpen.isOpenEmbedding_subtypeVal
  have hjT : IsOpenEmbedding jT := IsOpenEmbedding.of_comp jT
    A.transverseDomain.isOpen.isOpenEmbedding_subtypeVal T.isOpen.isOpenEmbedding_subtypeVal
  let J : S × ULift.{u} T → A.productSource := fun z ↦
    ⟨(jS z.1, jT z.2.down), by
      obtain ⟨q, hq1, hq2⟩ := hεprod z.1.val z.2.down.val z.1.property z.2.down.property
      have he : (jS z.1, jT z.2.down) = q.val := by
        apply Prod.ext
        · exact Subtype.ext hq1.symm
        · exact Subtype.ext hq2.symm
      exact he ▸ q.property⟩
  have hJ : IsOpenEmbedding J := IsOpenEmbedding.of_comp J
    A.productSource.isOpen.isOpenEmbedding_subtypeVal
    (hjS.prodMap (hjT.comp Homeomorph.ulift.isOpenEmbedding))
  let H : S × ULift.{u} T → M := fun z ↦ A.productMap (J z).val
  have hH : IsOpenEmbedding H := A.productMap_isOpenEmbedding.comp hJ
  let O : Opens M := ⟨range H, hH.isOpen_range⟩
  have hjSm : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, Fin d → ℝ) ∞ jS := by
    apply (ContMDiff.subtypeVal_comp_iff _ _).mp
    exact contMDiff_subtype_val
  have hchart (p : A.centers) : ∃ U : Opens (L (A.label p)),
      ∃ e : Diffeomorph 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, Fin (r (A.label p)) → ℝ) S U ∞,
        ∀ v : S, (e v).val = (A.chart p (jS v)).val := by
    let h : S → L (A.label p) := fun v ↦ (A.chart p (jS v)).val
    have hh : IsOpenEmbedding h := A.plaque p |>.isOpen.isOpenEmbedding_subtypeVal.comp
      ((A.chart p).toHomeomorph.isOpenEmbedding.comp hjS)
    let U : Opens (L (A.label p)) := ⟨range h, hh.isOpen_range⟩
    have hU (q : U) : q.val ∈ A.plaque p := by
      obtain ⟨v, hv⟩ := q.property
      exact hv ▸ (A.chart p (jS v)).property
    let iU : U → A.plaque p := fun q ↦ ⟨q.val, hU q⟩
    have hiU : ContMDiff 𝓘(ℝ, Fin (r (A.label p)) → ℝ)
        𝓘(ℝ, Fin (r (A.label p)) → ℝ) ∞ iU := by
      apply (ContMDiff.subtypeVal_comp_iff _ _).mp
      exact contMDiff_subtype_val
    have hinv (q : U) : ((A.chart p).symm (iU q)).val ∈ S := by
      obtain ⟨v, hv⟩ := q.property
      have he : iU q = A.chart p (jS v) := Subtype.ext hv.symm
      rw [he, (A.chart p).symm_apply_apply]
      exact v.property
    let e : Diffeomorph 𝓘(ℝ, Fin d → ℝ)
        𝓘(ℝ, Fin (r (A.label p)) → ℝ) S U ∞ := {
      toEquiv := {
        toFun := fun v ↦ ⟨h v, ⟨v, rfl⟩⟩
        invFun := fun q ↦ ⟨((A.chart p).symm (iU q)).val, hinv q⟩
        left_inv := by
          intro v
          apply Subtype.ext
          have he : iU ⟨h v, ⟨v, rfl⟩⟩ = A.chart p (jS v) := rfl
          change ((A.chart p).symm (iU ⟨h v, ⟨v, rfl⟩⟩)).val = v.val
          rw [he, (A.chart p).symm_apply_apply]
        right_inv := by
          intro q
          apply Subtype.ext
          change (A.chart p (jS ⟨((A.chart p).symm (iU q)).val, hinv q⟩)).val = q.val
          have he : jS ⟨((A.chart p).symm (iU q)).val, hinv q⟩ =
              (A.chart p).symm (iU q) := rfl
          rw [he, (A.chart p).apply_symm_apply] }
      contMDiff_toFun := by
        apply (ContMDiff.subtypeVal_comp_iff U _).mp
        convert (ContMDiff.subtypeVal_comp_iff _ _).mpr ((A.chart p).contMDiff.comp hjSm) using 1 ; rfl
      contMDiff_invFun := by
        apply (ContMDiff.subtypeVal_comp_iff S _).mp
        convert (ContMDiff.subtypeVal_comp_iff _ _).mpr ((A.chart p).symm.contMDiff.comp hiU) using 1 ; rfl }
    exact ⟨U, e, fun _ ↦ rfl⟩
  choose U e he using hchart
  let box : NativeProductBox F d (ULift.{u} T) := {
    transverseRank := k
    transverseDisc := T
    transverse_connected := (convex_ball (0 : Fin k → ℝ) ε).isConnected
      ⟨0, Metric.mem_ball_self hε⟩
    transverse_chart := Homeomorph.ulift
    disc := S
    disc_connected := (convex_ball (0 : Fin d → ℝ) ε).isConnected
      ⟨0, Metric.mem_ball_self hε⟩
    ambient := O
    box := hH.isEmbedding.toHomeomorph
    label := fun t ↦ A.label (A.transverseCenter (jT t.down))
    plaque := fun t ↦ U (A.transverseCenter (jT t.down))
    chart := fun t ↦ e (A.transverseCenter (jT t.down))
    factorization := by
      intro t v
      change A.value (A.transverseCenter (jT t.down)) (jS v) = _
      exact congrArg (F.leaf (A.label (A.transverseCenter (jT t.down)))).inclusion
        (he (A.transverseCenter (jT t.down)) v).symm }
  refine ⟨ε, hε, box, ?_⟩
  change x ∈ range H
  refine ⟨(⟨0, Metric.mem_ball_self hε⟩, ⟨⟨0, Metric.mem_ball_self hε⟩⟩), ?_⟩
  exact A.productMap_zero

end ProjectedNativePlaqueFamily
end HolomorphicAnosov.HPS
