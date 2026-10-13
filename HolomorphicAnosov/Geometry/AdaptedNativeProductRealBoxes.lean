import HolomorphicAnosov.Dynamics.HirschPughNativeLeafSystem
noncomputable section
open Set
open scoped ContDiff Manifold Topology
namespace HolomorphicAnosov.Ghys
universe u
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]
variable (f : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞)
  (Ds Du : ∀ x : M, Submodule ℝ (TangentSpace 𝓘(ℝ, E) x))
  (m : MetricSpace M) {β γ ε : ℝ}
  (S : NativeInvariantLeafSystem 𝓘(ℝ, E) Ds f)
  (U : NativeInvariantLeafSystem 𝓘(ℝ, E) Du f.symm)

/-- Two points of one closed orbit core are in the same wider orbit plaque; when their initial distance is at most the core radius, the stored core equation places them in each other's core. -/
theorem orbitCore_recenter
    (P : AdaptedNativeOrbitPlaques 𝓘(ℝ, E) f Ds m β γ S)
    (hβ : 2 * γ < β) {x y z : M}
    (hy : y ∈ adaptedClosedOrbitCore 𝓘(ℝ, E) f m γ x)
    (hz : z ∈ adaptedClosedOrbitCore 𝓘(ℝ, E) f m γ x)
    (hd : m.dist y z ≤ γ) : y ∈ adaptedClosedOrbitCore 𝓘(ℝ, E) f m γ z := by
  rw [P.closed_core]
  refine ⟨?_, hd⟩
  intro n
  calc
    m.dist ((f : M → M)^[n] y) ((f : M → M)^[n] z) ≤
        m.dist ((f : M → M)^[n] y) ((f : M → M)^[n] x) +
        m.dist ((f : M → M)^[n] x) ((f : M → M)^[n] z) := m.dist_triangle _ _ _
    _ ≤ γ + γ := add_le_add (hy n) (by simpa only [m.dist_comm] using hz n)
    _ < β := by linarith

variable (hγ : 0 < γ) (hε : 0 < ε)
  (bracket : adaptedClosePairDomain (M := M) m ε → M)
  (hbracket : ∀ p : adaptedClosePairDomain (M := M) m ε,
    adaptedClosedOrbitCore 𝓘(ℝ, E) f m γ p.1.1 ∩
      adaptedClosedOrbitCore 𝓘(ℝ, E) f.symm m γ p.1.2 = {bracket p})

include hγ hε hbracket in
omit [IsManifold 𝓘(ℝ, E) ∞ M] in
/-- A point belonging to both orbit cores of another point equals that point, by uniqueness of the bracket at the diagonal pair. -/
theorem orbitCore_diagonal_unique {x y : M}
    (hs : y ∈ adaptedClosedOrbitCore 𝓘(ℝ, E) f m γ x)
    (hu : y ∈ adaptedClosedOrbitCore 𝓘(ℝ, E) f.symm m γ x) : y = x := by
  let p : adaptedClosePairDomain (M := M) m ε := ⟨(x, x), by simpa [adaptedClosePairDomain] using hε⟩
  have hy : y = bracket p := Set.mem_singleton_iff.mp ((hbracket p) ▸ ⟨hs, hu⟩)
  have hx : x = bracket p := by
    apply Set.mem_singleton_iff.mp
    rw [← hbracket]
    constructor <;> intro n <;> simpa only [p, m.dist_self] using hγ.le
  exact hy.trans hx.symm

include hγ hε hbracket in
/-- Two sufficiently near stable coordinates must agree if their product points meet one receiving unstable core. -/
theorem adaptedProduct_stable_coordinate_unique
    (PS : AdaptedNativeOrbitPlaques 𝓘(ℝ, E) f Ds m β γ S)
    (PU : AdaptedNativeOrbitPlaques 𝓘(ℝ, E) f.symm Du m β γ U)
    (hβ : 2 * γ < β) (x : M)
    (P : AdaptedNativeProduct 𝓘(ℝ, E) f Ds Du m γ ε S U bracket x)
    (s s' : P.stableDomain) (u' : P.unstableDomain)
    (hd : m.dist ((S.leaf x).inclusion s'.val) ((S.leaf x).inclusion s.val) ≤ γ)
    (hq : (P.product (s', u')).val ∈
      adaptedClosedOrbitCore 𝓘(ℝ, E) f.symm m γ ((S.leaf x).inclusion s.val)) : s' = s := by
  have hq' : (P.product (s', u')).val ∈
      adaptedClosedOrbitCore 𝓘(ℝ, E) f.symm m γ ((S.leaf x).inclusion s'.val) := by
    have hm : (P.product (s', u')).val ∈
        adaptedClosedOrbitCore 𝓘(ℝ, E) f m γ ((U.leaf x).inclusion u'.val) ∩
        adaptedClosedOrbitCore 𝓘(ℝ, E) f.symm m γ ((S.leaf x).inclusion s'.val) := by
      rw [hbracket ⟨(_, _), P.caller s' u'⟩]
      exact Set.mem_singleton_iff.mpr (P.product_eq s' u')
    exact hm.2
  have hreverse {g : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞} {a b : M}
      (h : a ∈ adaptedClosedOrbitCore 𝓘(ℝ, E) g m γ b) :
      b ∈ adaptedClosedOrbitCore 𝓘(ℝ, E) g m γ a := by
    intro n
    simpa only [m.dist_comm] using h n
  have hs := orbitCore_recenter f Ds m S PS hβ
    (P.stable_core s'.val s'.property) (P.stable_core s.val s.property) hd
  have hu := orbitCore_recenter f.symm Du m U PU hβ (hreverse hq') (hreverse hq) hd
  apply Subtype.ext
  apply (S.leaf x).inclusion_injective
  exact orbitCore_diagonal_unique f m hγ hε bracket hbracket hs hu

include hbracket in
omit [IsManifold 𝓘(ℝ, E) ∞ M] in
/-- The actual product lies in the receiving unstable core named by its stable coordinate. -/
theorem adaptedProduct_mem_unstable (x : M)
    (P : AdaptedNativeProduct 𝓘(ℝ, E) f Ds Du m γ ε S U bracket x)
    (s : P.stableDomain) (u : P.unstableDomain) :
    (P.product (s, u)).val ∈
      adaptedClosedOrbitCore 𝓘(ℝ, E) f.symm m γ ((S.leaf x).inclusion s.val) := by
  have hm : (P.product (s, u)).val ∈
      adaptedClosedOrbitCore 𝓘(ℝ, E) f m γ ((U.leaf x).inclusion u.val) ∩
      adaptedClosedOrbitCore 𝓘(ℝ, E) f.symm m γ ((S.leaf x).inclusion s.val) := by
    rw [hbracket ⟨(_, _), P.caller s u⟩]
    exact Set.mem_singleton_iff.mpr (P.product_eq s u)
  exact hm.2

include hbracket in
/-- A product slice lifts continuously and injectively to its actual receiving unstable leaf. -/
theorem adaptedProduct_unstable_lift
    (PU : AdaptedNativeOrbitPlaques 𝓘(ℝ, E) f.symm Du m β γ U)
    (x : M) (P : AdaptedNativeProduct 𝓘(ℝ, E) f Ds Du m γ ε S U bracket x)
    (s : P.stableDomain) :
    ∃ j : P.unstableDomain → (U.leaf ((S.leaf x).inclusion s.val)).Carrier,
      Continuous j ∧ Function.Injective j ∧
      ∀ u, (U.leaf ((S.leaf x).inclusion s.val)).inclusion (j u) =
        (P.product (s, u)).val := by
  classical
  let b := (S.leaf x).inclusion s.val
  have hmem (u : P.unstableDomain) : (P.product (s, u)).val ∈
      adaptedOpenOrbitPlaque 𝓘(ℝ, E) f.symm m β b := by
    have hm := adaptedProduct_mem_unstable f Ds Du m S U bracket hbracket x P s u
    rw [PU.closed_core] at hm
    exact hm.1
  choose j hj using fun u ↦ PU.plaque_in_leaf b (hmem u)
  let lift : P.unstableDomain →
      (U.leaf b).inclusion ⁻¹' adaptedOpenOrbitPlaque 𝓘(ℝ, E) f.symm m β b :=
    fun u ↦ ⟨j u, by
      change (U.leaf b).inclusion (j u) ∈ adaptedOpenOrbitPlaque 𝓘(ℝ, E) f.symm m β b
      rw [hj]; exact hmem u⟩
  have hlift : Continuous lift := by
    apply (PU.plaque_embedded b).isInducing.continuous_iff.mpr
    have heq : (fun y : (U.leaf b).inclusion ⁻¹'
        adaptedOpenOrbitPlaque 𝓘(ℝ, E) f.symm m β b ↦ (U.leaf b).inclusion y.val) ∘ lift =
        fun u ↦ (P.product (s, u)).val := funext hj
    rw [heq]
    exact continuous_subtype_val.comp (P.product.continuous.comp
      (continuous_const.prodMk continuous_id))
  refine ⟨j, continuous_subtype_val.comp hlift, ?_, hj⟩
  intro u v huv
  have he : P.product (s, u) = P.product (s, v) := by
    apply Subtype.ext
    rw [← hj, ← hj, huv]
  exact congrArg Prod.snd (P.product.injective he)

include hγ hε hbracket in
/-- A sufficiently small product slice has intrinsically open image in the receiving unstable leaf. -/
theorem adaptedProduct_unstable_lift_open
    (PS : AdaptedNativeOrbitPlaques 𝓘(ℝ, E) f Ds m β γ S)
    (PU : AdaptedNativeOrbitPlaques 𝓘(ℝ, E) f.symm Du m β γ U)
    (hβ : 2 * γ < β)
    (htop : m.toUniformSpace.toTopologicalSpace = (inferInstance : TopologicalSpace M))
    (x : M) (P : AdaptedNativeProduct 𝓘(ℝ, E) f Ds Du m γ ε S U bracket x)
    (A : TopologicalSpace.Opens P.stableDomain)
    (B : TopologicalSpace.Opens P.unstableDomain)
    (hdiam : ∀ s s' : A,
      m.dist ((S.leaf x).inclusion s'.val.val) ((S.leaf x).inclusion s.val.val) ≤ γ)
    (hstrict : ∀ (s : A) (u : B),
      m.dist (P.product (s.val, u.val)).val ((S.leaf x).inclusion s.val.val) < γ)
    (s : A)
    (j : P.unstableDomain → (U.leaf ((S.leaf x).inclusion s.val.val)).Carrier)
    (hj : ∀ u, (U.leaf ((S.leaf x).inclusion s.val.val)).inclusion (j u) =
        (P.product (s.val, u)).val) :
    IsOpen (Set.range (fun u : B ↦ j u.val)) := by
  let : MetricSpace M := m.replaceTopology htop.symm
  let b := (S.leaf x).inclusion s.val.val
  let inc := (U.leaf b).inclusion
  let V : Set P.neighborhood := P.product '' ((A : Set P.stableDomain) ×ˢ B)
  have hV : IsOpen V := P.product.isOpenMap _ (A.isOpen.prod B.isOpen)
  let O : Set M := Subtype.val '' V
  have hO : IsOpen O := P.neighborhood_open.isOpenMap_subtype_val _ hV
  let Q : Set (U.leaf b).Carrier :=
    (inc ⁻¹' adaptedOpenOrbitPlaque 𝓘(ℝ, E) f.symm m β b) ∩
      (inc ⁻¹' O) ∩ {y | m.dist (inc y) b < γ}
  have hQ : IsOpen Q := by
    exact ((PU.plaque_intrinsic_open b).inter
      (hO.preimage (U.leaf b).inclusion_smooth.continuous)).inter
      (isOpen_lt ((U.leaf b).inclusion_smooth.continuous.dist continuous_const) continuous_const)
  have heq : Set.range (fun u : B ↦ j u.val) = Q := by
    ext y
    constructor
    · rintro ⟨u, rfl⟩
      have hm := adaptedProduct_mem_unstable f Ds Du m S U bracket hbracket x P s.val u.val
      rw [PU.closed_core] at hm
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · change inc (j u.val) ∈ adaptedOpenOrbitPlaque 𝓘(ℝ, E) f.symm m β b
        dsimp only [inc, b]
        rw [hj]
        exact hm.1
      · refine ⟨P.product (s.val, u.val), ⟨(s.val, u.val), ⟨s.property, u.property⟩, rfl⟩, ?_⟩
        exact (hj u.val).symm
      · change m.dist ((U.leaf b).inclusion (j u.val)) b < γ
        rw [hj]
        exact hstrict s u
    · rintro ⟨⟨hplaque, hOmem⟩, hdist⟩
      obtain ⟨w, ⟨su, hsu, hsuEq⟩, hw⟩ := hOmem
      have hpoint : (P.product su).val = inc y := by rw [hsuEq]; exact hw
      have hcore : (P.product su).val ∈
          adaptedClosedOrbitCore 𝓘(ℝ, E) f.symm m γ b := by
        rw [hpoint, PU.closed_core]
        refine ⟨hplaque, ?_⟩
        exact (show m.dist (inc y) b < γ from hdist).le
      have hstable : su.1 = s.val := adaptedProduct_stable_coordinate_unique
        f Ds Du m S U hγ hε bracket hbracket PS PU hβ x P s.val su.1 su.2
        (hdiam s ⟨su.1, hsu.1⟩) hcore
      refine ⟨⟨su.2, hsu.2⟩, ?_⟩
      apply (U.leaf b).inclusion_injective
      rw [hj]
      change (P.product (s.val, su.2)).val = inc y
      rw [← hstable]
      exact hpoint
  rw [heq]
  exact hQ

include hγ hε hbracket in
/-- The intrinsically open receiving slice has the original product slice as its homeomorphic parametrization. -/
theorem adaptedProduct_unstable_homeomorph
    (PS : AdaptedNativeOrbitPlaques 𝓘(ℝ, E) f Ds m β γ S)
    (PU : AdaptedNativeOrbitPlaques 𝓘(ℝ, E) f.symm Du m β γ U)
    (hβ : 2 * γ < β)
    (htop : m.toUniformSpace.toTopologicalSpace = (inferInstance : TopologicalSpace M))
    (x : M) (P : AdaptedNativeProduct 𝓘(ℝ, E) f Ds Du m γ ε S U bracket x)
    (A : TopologicalSpace.Opens P.stableDomain)
    (B : TopologicalSpace.Opens P.unstableDomain)
    (hdiam : ∀ s s' : A,
      m.dist ((S.leaf x).inclusion s'.val.val) ((S.leaf x).inclusion s.val.val) ≤ γ)
    (hstrict : ∀ (s : A) (u : B),
      m.dist (P.product (s.val, u.val)).val ((S.leaf x).inclusion s.val.val) < γ)
    (s : A) :
    ∃ (V : TopologicalSpace.Opens (U.leaf ((S.leaf x).inclusion s.val.val)).Carrier)
      (b : B ≃ₜ V),
      ∀ u : B, (U.leaf ((S.leaf x).inclusion s.val.val)).inclusion (b u).val =
        (P.product (s.val, u.val)).val := by
  obtain ⟨j, hjcont, hjinj, hj⟩ :=
    adaptedProduct_unstable_lift f Ds Du m S U bracket hbracket PU x P s.val
  let jB : B → (U.leaf ((S.leaf x).inclusion s.val.val)).Carrier := fun u ↦ j u.val
  have hopen := adaptedProduct_unstable_lift_open f Ds Du m S U hγ hε bracket hbracket
    PS PU hβ htop x P A B hdiam hstrict s j hj
  have hcont : Continuous jB := hjcont.comp continuous_subtype_val
  have hemb : Topology.IsEmbedding jB := by
    apply Topology.IsEmbedding.of_comp hcont
      (U.leaf ((S.leaf x).inclusion s.val.val)).inclusion_smooth.continuous
    have heq : (U.leaf ((S.leaf x).inclusion s.val.val)).inclusion ∘ jB =
        fun u : B ↦ (P.product (s.val, u.val)).val := funext (fun u ↦ hj u.val)
    rw [heq]
    exact Topology.IsEmbedding.subtypeVal.comp (P.product.isEmbedding.comp
      ((isEmbedding_prodMkRight s.val).comp Topology.IsEmbedding.subtypeVal))
  exact ⟨⟨Set.range jB, hopen⟩, hemb.toHomeomorph, fun u ↦ hj u.val⟩

/-- Reverse the input order of the bracket while using the same metric and domain. -/
def reverseNativeBracket
    (b : adaptedClosePairDomain (M := M) m ε → M) :
    adaptedClosePairDomain (M := M) m ε → M :=
  fun p ↦ b ⟨(p.val.2, p.val.1), by
    change m.dist p.val.2 p.val.1 < ε
    rw [m.dist_comm]
    exact p.property⟩

include hbracket in
omit [IsManifold 𝓘(ℝ, E) ∞ M] in
theorem reverseNativeBracket_intersection (p : adaptedClosePairDomain (M := M) m ε) :
    adaptedClosedOrbitCore 𝓘(ℝ, E) f.symm m γ p.val.1 ∩
      adaptedClosedOrbitCore 𝓘(ℝ, E) f.symm.symm m γ p.val.2 =
        {reverseNativeBracket m bracket p} := by
  rw [Set.inter_comm]
  exact hbracket ⟨(p.val.2, p.val.1), by simpa [adaptedClosePairDomain, m.dist_comm] using p.property⟩

/-- The inverse system's product is the same homeomorphism with exchanged factors. -/
def reverseNativeProduct (x : M)
    (P : AdaptedNativeProduct 𝓘(ℝ, E) f Ds Du m γ ε S U bracket x) :
    AdaptedNativeProduct 𝓘(ℝ, E) f.symm Du Ds m γ ε U S
      (reverseNativeBracket m bracket) x where
  stableDomain := P.unstableDomain
  unstableDomain := P.stableDomain
  stable_open := P.unstable_open
  unstable_open := P.stable_open
  stable_center := P.unstable_center
  unstable_center := P.stable_center
  stable_core := P.unstable_core
  unstable_core := P.stable_core
  caller s u := by simpa only [m.dist_comm] using P.caller u s
  neighborhood := P.neighborhood
  neighborhood_open := P.neighborhood_open
  neighborhood_center := P.neighborhood_center
  product := (Homeomorph.prodComm _ _).trans P.product
  product_eq s u := P.product_eq u s

include hγ hε hbracket in
/-- The symmetric construction gives open stable receiving branches. -/
theorem adaptedProduct_stable_homeomorph
    (PS : AdaptedNativeOrbitPlaques 𝓘(ℝ, E) f Ds m β γ S)
    (PU : AdaptedNativeOrbitPlaques 𝓘(ℝ, E) f.symm Du m β γ U)
    (hβ : 2 * γ < β)
    (htop : m.toUniformSpace.toTopologicalSpace = (inferInstance : TopologicalSpace M))
    (x : M) (P : AdaptedNativeProduct 𝓘(ℝ, E) f Ds Du m γ ε S U bracket x)
    (A : TopologicalSpace.Opens P.stableDomain)
    (B : TopologicalSpace.Opens P.unstableDomain)
    (hdiam : ∀ u u' : B,
      m.dist ((U.leaf x).inclusion u'.val.val) ((U.leaf x).inclusion u.val.val) ≤ γ)
    (hstrict : ∀ (u : B) (s : A),
      m.dist (P.product (s.val, u.val)).val ((U.leaf x).inclusion u.val.val) < γ)
    (u : B) :
    ∃ (V : TopologicalSpace.Opens (S.leaf ((U.leaf x).inclusion u.val.val)).Carrier)
      (b : A ≃ₜ V),
      ∀ s : A, (S.leaf ((U.leaf x).inclusion u.val.val)).inclusion (b s).val =
        (P.product (s.val, u.val)).val := by
  exact adaptedProduct_unstable_homeomorph f.symm Du Ds m U S hγ hε
    (reverseNativeBracket m bracket) (reverseNativeBracket_intersection f m bracket hbracket)
    PU PS hβ htop x (reverseNativeProduct f Ds Du m S U bracket x P)
    B A hdiam hstrict u

include hγ hbracket in
omit [IsManifold 𝓘(ℝ, E) ∞ M] in
/-- The product chart is the unstable inclusion on its central horizontal slice. -/
theorem adaptedProduct_horizontal (x : M)
    (P : AdaptedNativeProduct 𝓘(ℝ, E) f Ds Du m γ ε S U bracket x)
    (u : P.unstableDomain) :
    (P.product (⟨(S.leaf x).point, P.stable_center⟩, u)).val =
      (U.leaf x).inclusion u.val := by
  rw [P.product_eq]
  apply Eq.symm
  apply Set.mem_singleton_iff.mp
  rw [← hbracket]
  constructor
  · intro n
    simpa only [m.dist_self] using hγ.le
  · change (U.leaf x).inclusion u.val ∈
      adaptedClosedOrbitCore 𝓘(ℝ, E) f.symm m γ ((S.leaf x).inclusion (S.leaf x).point)
    rw [(S.leaf x).inclusion_point]
    exact P.unstable_core u.val u.property

include hγ hbracket in
omit [IsManifold 𝓘(ℝ, E) ∞ M] in
/-- The product chart is the stable inclusion on its central vertical slice. -/
theorem adaptedProduct_vertical (x : M)
    (P : AdaptedNativeProduct 𝓘(ℝ, E) f Ds Du m γ ε S U bracket x)
    (s : P.stableDomain) :
    (P.product (s, ⟨(U.leaf x).point, P.unstable_center⟩)).val =
      (S.leaf x).inclusion s.val := by
  rw [P.product_eq]
  apply Eq.symm
  apply Set.mem_singleton_iff.mp
  rw [← hbracket]
  constructor
  · change (S.leaf x).inclusion s.val ∈
      adaptedClosedOrbitCore 𝓘(ℝ, E) f m γ ((U.leaf x).inclusion (U.leaf x).point)
    rw [(U.leaf x).inclusion_point]
    exact P.stable_core s.val s.property
  · intro n
    simpa only [m.dist_self] using hγ.le
include hγ hbracket in
omit [IsManifold 𝓘(ℝ, E) ∞ M] in
/-- A product chart can be restricted to connected neighborhoods whose ambient images all lie in a prescribed small metric ball about its center. -/
theorem adaptedProduct_small_connected
    (htop : m.toUniformSpace.toTopologicalSpace = (inferInstance : TopologicalSpace M))
    (x : M) (P : AdaptedNativeProduct 𝓘(ℝ, E) f Ds Du m γ ε S U bracket x) :
    ∃ (A : TopologicalSpace.Opens P.stableDomain)
      (B : TopologicalSpace.Opens P.unstableDomain),
      (⟨(S.leaf x).point, P.stable_center⟩ : P.stableDomain) ∈ A ∧
      (⟨(U.leaf x).point, P.unstable_center⟩ : P.unstableDomain) ∈ B ∧
      IsConnected (A : Set P.stableDomain) ∧ IsConnected (B : Set P.unstableDomain) ∧
      ∀ (s : A) (u : B), m.dist (P.product (s.val, u.val)).val x < γ / 3 := by
  let : MetricSpace M := m.replaceTopology htop.symm
  let : LocallyConnectedSpace (S.leaf x).Carrier := ChartedSpace.locallyConnectedSpace (Fin (S.leaf x).rank → ℝ) _
  let : LocallyConnectedSpace (U.leaf x).Carrier := ChartedSpace.locallyConnectedSpace (Fin (U.leaf x).rank → ℝ) _
  let : LocallyConnectedSpace P.stableDomain := P.stable_open.locallyConnectedSpace
  let : LocallyConnectedSpace P.unstableDomain := P.unstable_open.locallyConnectedSpace
  let s₀ : P.stableDomain := ⟨(S.leaf x).point, P.stable_center⟩
  let u₀ : P.unstableDomain := ⟨(U.leaf x).point, P.unstable_center⟩
  have hc : (P.product (s₀, u₀)).val = x := by
    rw [adaptedProduct_horizontal f Ds Du m S U hγ bracket hbracket x P u₀]
    exact (U.leaf x).inclusion_point
  have hn : {p : P.stableDomain × P.unstableDomain |
      m.dist (P.product p).val x < γ / 3} ∈ 𝓝 (s₀, u₀) := by
    apply (isOpen_lt ((continuous_subtype_val.comp P.product.continuous).dist
      continuous_const) continuous_const).mem_nhds
    change m.dist (P.product (s₀, u₀)).val x < γ / 3
    rw [hc, m.dist_self]
    positivity
  obtain ⟨A₀, hA₀, B₀, hB₀, hAB⟩ := mem_nhds_prod_iff.mp hn
  obtain ⟨A, hAA, hAopen, hs, hAconn⟩ :=
    locallyConnectedSpace_iff_subsets_isOpen_isConnected.mp
      (inferInstance : LocallyConnectedSpace P.stableDomain) s₀ A₀ hA₀
  obtain ⟨B, hBB, hBopen, hu, hBconn⟩ :=
    locallyConnectedSpace_iff_subsets_isOpen_isConnected.mp
      (inferInstance : LocallyConnectedSpace P.unstableDomain) u₀ B₀ hB₀
  exact ⟨⟨A, hAopen⟩, ⟨B, hBopen⟩, hs, hu, hAconn, hBconn,
    fun s u ↦ hAB ⟨hAA s.property, hBB u.property⟩⟩

include hγ hε hbracket in
/-- Rechart the small connected product in its original leaf coordinates. -/
theorem adaptedProduct_real_box
    (PS : AdaptedNativeOrbitPlaques 𝓘(ℝ, E) f Ds m β γ S)
    (PU : AdaptedNativeOrbitPlaques 𝓘(ℝ, E) f.symm Du m β γ U)
    (hβ : 2 * γ < β)
    (htop : m.toUniformSpace.toTopologicalSpace = (inferInstance : TopologicalSpace M))
    (x : M) (P : AdaptedNativeProduct 𝓘(ℝ, E) f Ds Du m γ ε S U bracket x) :
    ∃ (As : TopologicalSpace.Opens (Fin (S.leaf x).rank → ℝ))
      (Au : TopologicalSpace.Opens (Fin (U.leaf x).rank → ℝ))
      (O : TopologicalSpace.Opens M) (e : (As × Au) ≃ₜ O), x ∈ O ∧
      (∀ w : Au, ∃ (y : M) (V : TopologicalSpace.Opens (S.leaf y).Carrier)
        (c : As ≃ₜ V), ∀ z : As,
          (e (z,w)).val = (S.leaf y).inclusion (c z).val) ∧
      (∀ z : As, ∃ (y : M) (V : TopologicalSpace.Opens (U.leaf y).Carrier)
        (c : Au ≃ₜ V), ∀ w : Au,
          (e (z,w)).val = (U.leaf y).inclusion (c w).val) := by
  obtain ⟨A, B, hs, hu, hAc, hBc, hsmall⟩ :=
    adaptedProduct_small_connected f Ds Du m S U hγ bracket hbracket htop x P
  let s₀ : A := ⟨⟨(S.leaf x).point, P.stable_center⟩, hs⟩
  let u₀ : B := ⟨⟨(U.leaf x).point, P.unstable_center⟩, hu⟩
  have hsnear (s : A) : m.dist ((S.leaf x).inclusion s.val.val) x < γ / 3 := by
    rw [← adaptedProduct_vertical f Ds Du m S U hγ bracket hbracket x P s.val]
    exact hsmall s u₀
  have hunear (u : B) : m.dist ((U.leaf x).inclusion u.val.val) x < γ / 3 := by
    rw [← adaptedProduct_horizontal f Ds Du m S U hγ bracket hbracket x P u.val]
    exact hsmall s₀ u
  have hdiamS (s s' : A) :
      m.dist ((S.leaf x).inclusion s'.val.val) ((S.leaf x).inclusion s.val.val) ≤ γ := by
    have ht := m.dist_triangle ((S.leaf x).inclusion s'.val.val) x
      ((S.leaf x).inclusion s.val.val)
    rw [m.dist_comm x] at ht
    have := hsnear s; have := hsnear s'; linarith
  have hdiamU (u u' : B) :
      m.dist ((U.leaf x).inclusion u'.val.val) ((U.leaf x).inclusion u.val.val) ≤ γ := by
    have ht := m.dist_triangle ((U.leaf x).inclusion u'.val.val) x
      ((U.leaf x).inclusion u.val.val)
    rw [m.dist_comm x] at ht
    have := hunear u; have := hunear u'; linarith
  have hstrictS (s : A) (u : B) :
      m.dist (P.product (s.val, u.val)).val ((S.leaf x).inclusion s.val.val) < γ := by
    have ht := m.dist_triangle (P.product (s.val, u.val)).val x
      ((S.leaf x).inclusion s.val.val)
    rw [m.dist_comm x] at ht
    have := hsmall s u; have := hsnear s; linarith
  have hstrictU (u : B) (s : A) :
      m.dist (P.product (s.val, u.val)).val ((U.leaf x).inclusion u.val.val) < γ := by
    have ht := m.dist_triangle (P.product (s.val, u.val)).val x
      ((U.leaf x).inclusion u.val.val)
    rw [m.dist_comm x] at ht
    have := hsmall s u; have := hunear u; linarith
  let : ChartedSpace (Fin (S.leaf x).rank → ℝ) P.stableDomain :=
    inferInstanceAs (ChartedSpace _ (⟨P.stableDomain, P.stable_open⟩ : TopologicalSpace.Opens _))
  let : ChartedSpace (Fin (U.leaf x).rank → ℝ) P.unstableDomain :=
    inferInstanceAs (ChartedSpace _ (⟨P.unstableDomain, P.unstable_open⟩ : TopologicalSpace.Opens _))
  let cs := chartAt (Fin (S.leaf x).rank → ℝ) s₀
  let cu := chartAt (Fin (U.leaf x).rank → ℝ) u₀
  let As : TopologicalSpace.Opens (Fin (S.leaf x).rank → ℝ) := ⟨cs.target, cs.open_target⟩
  let Au : TopologicalSpace.Opens (Fin (U.leaf x).rank → ℝ) := ⟨cu.target, cu.open_target⟩
  let js : As → A := fun z ↦ cs.symm z
  let ju : Au → B := fun w ↦ cu.symm w
  have hjs : Topology.IsOpenEmbedding js := cs.symm.isOpenEmbedding_restrict
  have hju : Topology.IsOpenEmbedding ju := cu.symm.isOpenEmbedding_restrict
  let v : As × Au → M := fun zw ↦ (P.product ((js zw.1).val, (ju zw.2).val)).val
  have hv : Topology.IsOpenEmbedding v :=
    P.neighborhood_open.isOpenEmbedding_subtypeVal.comp
      (P.product.isOpenEmbedding.comp
        ((A.isOpen.isOpenEmbedding_subtypeVal.comp hjs).prodMap
          (B.isOpen.isOpenEmbedding_subtypeVal.comp hju)))
  let O : TopologicalSpace.Opens M := ⟨Set.range v, hv.isOpen_range⟩
  let e : (As × Au) ≃ₜ O := hv.isEmbedding.toHomeomorph
  refine ⟨As, Au, O, e, ?_, ?_, ?_⟩
  · let z : As := ⟨cs s₀, cs.map_source (mem_chart_source _ _)⟩
    let w : Au := ⟨cu u₀, cu.map_source (mem_chart_source _ _)⟩
    refine ⟨(z,w), ?_⟩
    change (P.product ((cs.symm (cs s₀)).val, (cu.symm (cu u₀)).val)).val = x
    rw [cs.left_inv (mem_chart_source _ _), cu.left_inv (mem_chart_source _ _)]
    rw [adaptedProduct_horizontal f Ds Du m S U hγ bracket hbracket x P u₀.val]
    exact (U.leaf x).inclusion_point
  · intro w
    obtain ⟨V, b, hb⟩ := adaptedProduct_stable_homeomorph f Ds Du m S U hγ hε
      bracket hbracket PS PU hβ htop x P A B hdiamU hstrictU (ju w)
    let j : As → (S.leaf ((U.leaf x).inclusion (ju w).val.val)).Carrier :=
      fun z ↦ (b (js z)).val
    have hj : Topology.IsOpenEmbedding j :=
      V.isOpen.isOpenEmbedding_subtypeVal.comp (b.isOpenEmbedding.comp hjs)
    exact ⟨_, ⟨Set.range j, hj.isOpen_range⟩, hj.isEmbedding.toHomeomorph,
      fun z ↦ (hb (js z)).symm⟩
  · intro z
    obtain ⟨V, b, hb⟩ := adaptedProduct_unstable_homeomorph f Ds Du m S U hγ hε
      bracket hbracket PS PU hβ htop x P A B hdiamS hstrictS (js z)
    let j : Au → (U.leaf ((S.leaf x).inclusion (js z).val.val)).Carrier :=
      fun w ↦ (b (ju w)).val
    have hj : Topology.IsOpenEmbedding j :=
      V.isOpen.isOpenEmbedding_subtypeVal.comp (b.isOpenEmbedding.comp hju)
    exact ⟨_, ⟨Set.range j, hj.isOpen_range⟩, hj.isEmbedding.toHomeomorph,
      fun w ↦ (hb (ju w)).symm⟩

end HolomorphicAnosov.Ghys
