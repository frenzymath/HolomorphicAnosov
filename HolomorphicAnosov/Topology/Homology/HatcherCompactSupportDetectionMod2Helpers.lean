import HolomorphicAnosov.Topology.Homology.ModTwoSupportUnionDetection
import HolomorphicAnosov.Topology.Homology.ModTwoSupportHomologyEmpty
import HolomorphicAnosov.Topology.Homology.ModTwoSupportRestrictionComparison
import HolomorphicAnosov.Topology.Homology.CompactSupportBallHomologyLiftCoefficients
import HolomorphicAnosov.Topology.Homology.FiniteCompactConvexUnionInduction
import HolomorphicAnosov.Topology.Homology.ConvexModTwoRestrictionIso
import HolomorphicAnosov.Topology.Homology.ModTwoULiftPointRelativeProfile
import HolomorphicAnosov.Topology.Homology.ModTwoSupportHomeomorphism
import HolomorphicAnosov.Topology.Homology.SupportNeighborhoodExcisionCoefficients
import HolomorphicAnosov.Topology.Homology.FullTargetChart

noncomputable section
namespace HolomorphicAnosov.HatcherCompactSupport
open Set CategoryTheory HolomorphicAnosov.Topology HolomorphicAnosov.Topology.Homology
universe u
set_option maxHeartbeats 1200000

private abbrev Profile {M : Type u} [TopologicalSpace M] (n : ℕ) (K : Set M) :=
  (∀ a : SupportHomology K n,
    (∀ x (hx : x ∈ K), supportRestriction (singleton_subset_iff.mpr hx) n a = 0) → a = 0) ∧
  (∀ q, n < q → Subsingleton (SupportHomology K q))

private theorem restrict_comp {M : Type u} [TopologicalSpace M] {K L A : Set M}
    (hLK : L ⊆ K) (hAL : A ⊆ L) (q : ℕ) (a : SupportHomology K q) :
    supportRestriction hAL q (supportRestriction hLK q a) =
      supportRestriction (hAL.trans hLK) q a := by
  change (modTwoSupportRestriction M K L hLK q ≫
    modTwoSupportRestriction M L A hAL q) a = _
  rw [← SSetPair.homologyMap_comp]
  rfl

private theorem empty_profile (M : Type u) [TopologicalSpace M] (n : ℕ) :
    Profile n (∅ : Set M) :=
  ⟨fun _ _ ↦ (modTwoSupportHomology_empty_subsingleton M n).elim _ _,
    fun q _ ↦ modTwoSupportHomology_empty_subsingleton M q⟩

private theorem union_profile {M : Type u} [TopologicalSpace M] [T2Space M]
    (n : ℕ) (A B : Set M) (hA : IsCompact A) (hB : IsCompact B)
    (hPA : Profile n A) (hPB : Profile n B) (hPAB : Profile n (A ∩ B)) :
    Profile n (A ∪ B) := by
  refine ⟨?_, modTwo_support_union_above_dimension M A B hA hB n hPA.2 hPB.2 hPAB.2⟩
  intro c hc
  apply modTwo_support_union_zero_of_restrictions M A B hA hB n
    (hPAB.2 (n+1) (Nat.lt_succ_self n)) c
  · apply hPA.1
    intro x hx
    rw [restrict_comp]
    exact hc x (Or.inl hx)
  · apply hPB.1
    intro x hx
    rw [restrict_comp]
    exact hc x (Or.inr hx)

private theorem ball_lift {E : Type u} [MetricSpace E] [ProperSpace E]
    (K : Set E) (hK : IsCompact K) (q : ℕ) (a : SupportHomology K q) :
    ∃ r : ℝ, 0 < r ∧ ∃ centers : Finset K,
      let L : Set E := ⋃ x ∈ centers, Metric.closedBall (x : E) r
      ∃ hKL : K ⊆ L, ∃ b : SupportHomology L q, supportRestriction hKL q b = a := by
  let f := Int.castRingHom (ZMod 2)
  let V := ModuleCat.of (ZMod 2) (ULift.{u} (ZMod 2))
  let W := (ModuleCat.restrictScalars.{u} f).obj V
  let e (A : Set E) :=
    (ssetPairRestrictScalarsHomologyIso f (supportSingularPair (TopCat.of E) A) V q).toLinearEquiv.toAddEquiv
  obtain ⟨r, hr, s, hKL, _, _, b, hb⟩ :=
    compact_support_ball_homology_lift_coefficients K hK W q (e K a)
  let L : Set E := ⋃ x ∈ s, Metric.closedBall (x : E) r
  refine ⟨r, hr, s, hKL, (e L).symm b, ?_⟩
  apply (e K).injective
  have hn := modTwoSupportRestriction_comparison E L K hKL q ((e L).symm b)
  change e K (supportRestriction hKL q ((e L).symm b)) =
    supportSingularHomologyRestrict (TopCat.of E) W hKL q (e L ((e L).symm b)) at hn
  rw [AddEquiv.apply_symm_apply] at hn
  apply hn.trans
  convert hb using 1
  simp [supportSingularHomologyRestrict, supportSingularHomologyMap,
    supportSingularPairMap]

private theorem euclidean_profile (n : ℕ)
    (K : Set (ULift.{u} (EuclideanSpace ℝ (Fin n)))) (hK : IsCompact K) :
    Profile n K := by
  classical
  let E := ULift.{u} (EuclideanSpace ℝ (Fin n))
  have hconv (A : Set E) (hc : IsCompact A) (hv : Convex ℝ A) : Profile n A := by
    by_cases hne : A.Nonempty
    · obtain ⟨x, hx⟩ := hne
      have hinj (q : ℕ) : Function.Injective (supportRestriction
          (singleton_subset_iff.mpr hx) q : SupportHomology A q → SupportHomology {x} q) := by
        have := convex_compact_modTwo_support_restriction_isIso A hv hc x hx q
        exact ConcreteCategory.bijective_of_isIso _ |>.1
      refine ⟨?_, ?_⟩
      · intro a ha
        apply hinj n
        simpa only [map_zero] using ha x hx
      · intro q hq
        have := (modTwo_ulift_point_relative_profile n x).2 q (ne_of_gt hq)
        exact Function.Injective.subsingleton (hinj q)
    · rw [not_nonempty_iff_eq_empty.mp hne]
      exact empty_profile E n
  have hfinite (r : ℝ) (s : Finset E) : Profile n (⋃ c ∈ s, Metric.closedBall c r) :=
    finite_compact_convex_union_induction (Profile n) hconv (union_profile n) s
      (fun c ↦ Metric.closedBall c r) (fun _ _ ↦ isCompact_closedBall _ _)
      (fun _ _ ↦ convex_closedBall _ _)
  constructor
  · intro a ha
    obtain ⟨r, hr, s, hKL, b, hb⟩ := ball_lift K hK n a
    let L : Set E := ⋃ c ∈ s, Metric.closedBall (c : E) r
    have hLi : L = ⋃ c ∈ s.image (fun z : K ↦ (z : E)), Metric.closedBall c r := by
      ext x; simp [L]
    have hPL : Profile n L := by rw [hLi]; exact hfinite _ _
    have hbzero : b = 0 := by
      apply hPL.1
      intro x hx
      obtain ⟨c, hc, hxc⟩ := Set.mem_iUnion₂.mp hx
      have hball : Metric.closedBall (c : E) r ⊆ L :=
        fun y hy ↦ Set.mem_iUnion₂.mpr ⟨c, hc, hy⟩
      have hcenter : (c : E) ∈ Metric.closedBall (c : E) r :=
        Metric.mem_closedBall_self hr.le
      have hbball : supportRestriction hball n b = 0 := by
        have := convex_compact_modTwo_support_restriction_isIso
          (Metric.closedBall (c : E) r) (convex_closedBall _ _)
          (isCompact_closedBall _ _) c hcenter n
        apply (ConcreteCategory.bijective_of_isIso
          (modTwoSupportRestriction E (Metric.closedBall (c : E) r) {c.val}
            (singleton_subset_iff.mpr hcenter) n)).1
        change supportRestriction (singleton_subset_iff.mpr hcenter) n
          (supportRestriction hball n b) = supportRestriction _ n 0
        rw [map_zero, restrict_comp]
        have hh := restrict_comp hKL (singleton_subset_iff.mpr c.property) n b
        rw [hb] at hh
        exact hh.symm.trans (ha c c.property)
      have hh := restrict_comp hball (singleton_subset_iff.mpr hxc) n b
      rw [hbball, map_zero] at hh
      exact hh.symm
    rw [hbzero, map_zero] at hb
    exact hb.symm
  · intro q hq
    have hz (a : SupportHomology K q) : a = 0 := by
      obtain ⟨r, hr, s, hKL, b, hb⟩ := ball_lift K hK q a
      let L : Set E := ⋃ c ∈ s, Metric.closedBall (c : E) r
      have hLi : L = ⋃ c ∈ s.image (fun z : K ↦ (z : E)), Metric.closedBall c r := by
        ext x; simp [L]
      have hPL : Profile n L := by rw [hLi]; exact hfinite _ _
      have hbzero : b = 0 := (hPL.2 q hq).elim _ _
      rw [hbzero, map_zero] at hb
      exact hb.symm
    exact ⟨fun a b ↦ (hz a).trans (hz b).symm⟩

private theorem homeomorph_profile {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) (K : Set X) (L : Set Y) (hKL : ∀ x, x ∈ K ↔ e x ∈ L)
    (n : ℕ) (hP : Profile n L) : Profile n K := by
  let V := ModuleCat.of (ZMod 2) (ULift.{u} (ZMod 2))
  let f (A : Set X) (B : Set Y) (hAB : ∀ x, x ∈ A ↔ e x ∈ B) (q : ℕ) :
      modTwoSupportHomology X A q ⟶ modTwoSupportHomology Y B q :=
    SSetPair.homologyMap
      (supportSingularPairMap (X := TopCat.of X) (Y := TopCat.of Y) A B
        (TopCat.ofHom ⟨e, e.continuous⟩) (fun x hx hB ↦ hx ((hAB x).mpr hB))) V q
  have hinj (q : ℕ) : Function.Injective (f K L hKL q) := by
    have : IsIso (f K L hKL q) := modTwo_support_homeomorph_homology_isIso e K L hKL q
    exact ConcreteCategory.bijective_of_isIso _ |>.1
  constructor
  · intro a ha
    apply hinj n
    rw [map_zero]
    apply hP.1
    intro y hy
    let x := e.symm y
    have hx : x ∈ K := (hKL x).mpr (by simpa [x] using hy)
    have hxy : e x = y := e.apply_symm_apply y
    have hp : ∀ z, z ∈ ({x} : Set X) ↔ e z ∈ ({y} : Set Y) := by
      intro z
      simp only [mem_singleton_iff, ← hxy, e.injective.eq_iff]
    have hnat : f K L hKL n ≫ modTwoSupportRestriction Y L {y}
        (singleton_subset_iff.mpr hy) n =
      modTwoSupportRestriction X K {x} (singleton_subset_iff.mpr hx) n ≫
        f {x} {y} hp n := by
      dsimp only [f, modTwoSupportRestriction]
      erw [← SSetPair.homologyMap_comp, ← SSetPair.homologyMap_comp]
      congr 1
    have ht := congrArg (fun m ↦ m a) hnat
    change supportRestriction _ n (f K L hKL n a) =
      f {x} {y} hp n (supportRestriction _ n a) at ht
    rw [ha x hx, map_zero] at ht
    exact ht
  · intro q hq
    have := hP.2 q hq
    exact Function.Injective.subsingleton (hinj q)

private theorem neighborhood_profile
    (M : Type u) [TopologicalSpace M] [T2Space M]
    (K U : Set M) (hK : IsClosed K) (hU : IsOpen U) (hKU : K ⊆ U) (n : ℕ)
    (hP : Profile n {z : U | z.val ∈ K}) : Profile n K := by
  let V := ModuleCat.of (ZMod 2) (ULift.{u} (ZMod 2))
  let f (A : Set M) (q : ℕ) :
      modTwoSupportHomology U {z : U | z.val ∈ A} q ⟶ modTwoSupportHomology M A q :=
    SSetPair.homologyMap
    (supportSingularPairMap (X := TopCat.of U) (Y := TopCat.of M)
      {z : U | z.val ∈ A} A
      (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩)
      (fun _ hz hA ↦ hz hA)) V q
  have hi (A : Set M) (hA : IsClosed A) (hAU : A ⊆ U) (q : ℕ) : IsIso (f A q) := by
    exact support_neighborhood_excision_isIso_coefficients (TopCat.of M) A U hU
      (by rwa [hA.closure_eq]) V q
  have hbij (q : ℕ) : Function.Bijective (f K q) := by
    have : IsIso (f K q) := hi K hK hKU q
    exact ConcreteCategory.bijective_of_isIso _
  constructor
  · intro a ha
    obtain ⟨b, hb⟩ := (hbij n).2 a
    have hbzero : b = 0 := by
      apply hP.1
      intro z hz
      let g : modTwoSupportHomology U {z} n ⟶ modTwoSupportHomology M {z.val} n :=
        SSetPair.homologyMap
        (supportSingularPairMap (X := TopCat.of U) (Y := TopCat.of M)
          ({z} : Set U) ({z.val} : Set M)
          (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩)
          (fun y hy hval ↦ hy (Subtype.ext hval))) V n
      have hig : IsIso g := by
        have hgen (W : Set U) (hW : ∀ y : U, y ∈ W ↔ y.val ∈ ({z.val} : Set M)) :
            IsIso (SSetPair.homologyMap
              (supportSingularPairMap (X := TopCat.of U) (Y := TopCat.of M)
                W {z.val} (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩)
                (fun y hy hv ↦ hy ((hW y).mpr hv))) V n) := by
          have he : W = {y : U | y.val ∈ ({z.val} : Set M)} := Set.ext hW
          subst W
          exact hi {z.val} isClosed_singleton (singleton_subset_iff.mpr z.property) n
        exact hgen {z} (fun y ↦ by simp only [mem_singleton_iff]; exact Subtype.ext_iff)
      apply (ConcreteCategory.bijective_of_isIso g).1
      rw [map_zero]
      have hnat : f K n ≫ modTwoSupportRestriction M K {z.val}
          (singleton_subset_iff.mpr hz) n =
        modTwoSupportRestriction U {y : U | y.val ∈ K} {z}
          (singleton_subset_iff.mpr hz) n ≫ g := by
        dsimp only [f, g, modTwoSupportRestriction]
        erw [← SSetPair.homologyMap_comp, ← SSetPair.homologyMap_comp]
        congr 1
      have ht := congrArg (fun m ↦ m b) hnat
      change supportRestriction _ n (f K n b) = g (supportRestriction _ n b) at ht
      rw [hb, ha z.val hz] at ht
      exact ht.symm
    rw [hbzero, map_zero] at hb
    exact hb.symm
  · intro q hq
    have := hP.2 q hq
    exact Function.Surjective.subsingleton (hbij q).2

private theorem chart_profile (n : ℕ) (M : Type u) [TopologicalSpace M] [T2Space M]
    (A U : Set M) (hA : IsCompact A) (hU : IsOpen U)
    (e : U ≃ₜ EuclideanSpace ℝ (Fin n)) (hAU : A ⊆ U) : Profile n A := by
  let e' : U ≃ₜ ULift.{u} (EuclideanSpace ℝ (Fin n)) := e.trans Homeomorph.ulift.symm
  have hc : IsCompact {z : U | z.val ∈ A} := by
    apply _root_.Topology.IsEmbedding.subtypeVal.isInducing.isCompact_preimage' hA
    simpa using hAU
  have he : ∀ z : U, z ∈ {z : U | z.val ∈ A} ↔
      e' z ∈ e' '' {z : U | z.val ∈ A} := fun _ ↦ e'.injective.mem_set_image.symm
  exact neighborhood_profile M A U hA.isClosed hU hAU n
    (homeomorph_profile e' _ _ he n (euclidean_profile n _ (hc.image e'.continuous)))

/-- Convex supports have the mod-two point profile. (Hatcher, Lemma 3.27) -/
private theorem compact_profile (n : ℕ) (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    (K : Set M) (hK : IsCompact K) : Profile n K := by
  classical
  let E := EuclideanSpace ℝ (Fin n)
  have hchart (x : M) := fullTargetChart (n := n) x
  choose c hx hc using hchart
  let : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace E M
  have hn (x : K) : ∃ C : Set M, IsCompact C ∧ x.val ∈ interior C ∧ C ⊆ (c x.val).source :=
    exists_compact_subset (c x.val).open_source (hx x.val)
  choose C hCc hxC hCe using hn
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover (fun x : K ↦ interior (C x))
    (fun _ ↦ isOpen_interior)
    (fun x hx ↦ Set.mem_iUnion.mpr ⟨⟨x,hx⟩, hxC ⟨x,hx⟩⟩)
  let Good (A : Set M) := IsCompact A ∧
    ∃ U : Set M, IsOpen U ∧ ∃ e : U ≃ₜ E, A ⊆ U
  have hgood (x : K) : Good (K ∩ C x) := by
    refine ⟨hK.inter_right (hCc x).isClosed, (c x.val).source,
      (c x.val).open_source, ?_, Set.inter_subset_right.trans (hCe x)⟩
    exact (c x.val).toHomeomorphSourceTarget.trans
      ((Homeomorph.setCongr (hc x.val)).trans (Homeomorph.Set.univ _))
  have hind (s : Finset K) : ∀ F : K → Set M, (∀ i ∈ s, Good (F i)) →
      Profile n (⋃ i ∈ s, F i) := by
    induction s using Finset.induction_on with
    | empty =>
      intro F hF
      simpa using empty_profile M n
    | @insert a s ha ih =>
      intro F hF
      obtain ⟨hcA, U, hU, e, he⟩ := hF a (Finset.mem_insert_self a s)
      have hFs (i) (hi : i ∈ s) := hF i (Finset.mem_insert_of_mem hi)
      have hrest := ih F hFs
      have hinter : Profile n (F a ∩ ⋃ i ∈ s, F i) := by
        have ht := ih (fun i ↦ F a ∩ F i) (by
          intro i hi
          obtain ⟨hc, V, hV, eV, heV⟩ := hFs i hi
          exact ⟨hcA.inter_right hc.isClosed, V, hV, eV, Set.inter_subset_right.trans heV⟩)
        simpa only [Set.inter_iUnion] using ht
      have hcRest : IsCompact (⋃ i ∈ s, F i) :=
        s.isCompact_biUnion (fun i hi ↦ (hFs i hi).1)
      simpa only [Finset.set_biUnion_insert] using
        union_profile n (F a) (⋃ i ∈ s, F i) hcA hcRest
          (chart_profile n M (F a) U hcA hU e he) hrest hinter
  have hcover : K = ⋃ x ∈ s, K ∩ C x := by
    apply Set.Subset.antisymm
    · intro x hx
      obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.mp (hs hx)
      exact Set.mem_iUnion₂.mpr ⟨y, hy, hx, interior_subset hxy⟩
    · intro x hx
      obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.mp hx
      exact hxy.1
  rw [hcover]
  exact hind s (fun x ↦ K ∩ C x) (fun i _ ↦ hgood i)

/-- Top-degree point restrictions detect a compactly supported mod-two class on a nonempty compact support in a topological Euclidean n-manifold. (Hatcher) -/
theorem hatcher_compact_support_section_mod2_nonempty_detection
    (n : ℕ) (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    (A : Set M) (hA : IsCompact A) (_hAne : A.Nonempty) :
    ∀ a : SupportHomology A n,
      (∀ x : A, supportToPoint A n x a = 0) → a = 0 := by
  clear _hAne
  intro a ha
  exact (compact_profile n M A hA).1 a (fun x hx ↦ ha ⟨x, hx⟩)

/-- Supported mod-two homology above the manifold dimension vanishes on a nonempty compact support. (Hatcher) -/
theorem hatcher_compact_support_section_mod2_nonempty_vanishing
    (n : ℕ) (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    (A : Set M) (hA : IsCompact A) (_hAne : A.Nonempty) :
    ∀ i : ℕ, n < i → Subsingleton (SupportHomology A i) := by
  clear _hAne
  exact (compact_profile n M A hA).2

end HolomorphicAnosov.HatcherCompactSupport

