import HolomorphicAnosov.Topology.ENRLocalFixedPointIndexConjugacy
import Mathlib.Topology.Metrizable.Basic
import Mathlib.Topology.IsLocalHomeomorph
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import HolomorphicAnosov.Topology.FiniteFixedPointDomains
import HolomorphicAnosov.Topology.Franks.LocalLinearization

open TopologicalSpace
open scoped _root_.Topology

namespace HolomorphicAnosov.FixedPointIndexInterface
noncomputable section
universe u v

/-- An open subspace of a specified ENR is represented by the inverse image of
that subspace under the same retraction. Source: Dold (1965), (2.3), p.3.
Both maps are literal restrictions of the original section and retraction. -/
def openENRRepresentation {X : Type*} [TopologicalSpace X]
    (e : ENRRepresentation X) (S : Opens X) : ENRRepresentation S where
  dimension := e.dimension
  domain := retractedDomain e S
  domain_open := (enrRetractedOpenDomain e S).isOpen
  sectionMap := ⟨fun x ↦ ⟨(e.sectionMap x.val).val,
    ⟨(e.sectionMap x.val).property, by
      change e.retraction (e.sectionMap x.val) ∈ S
      rw [e.retraction_section]
      exact x.property⟩⟩,
    by fun_prop⟩
  retraction := ⟨fun z ↦ ⟨e.retraction (retractedDomainInclusion e S z),
    z.property.choose_spec⟩, by fun_prop⟩
  retraction_section := by intro x; apply Subtype.ext; exact e.retraction_section x.val

/-- Equality of the actual Euclidean domains and maps preserves the native index. -/
theorem euclidean_index_congr_domain {n : ℕ} (U V : Opens (Euclidean n)) (hUV : U = V)
    (f : C(U, Euclidean n)) (g : C(V, Euclidean n))
    (hf : IsCompact (euclideanFixedSet f)) (hg : IsCompact (euclideanFixedSet g))
    (heq : ∀ x : U, f x = g ⟨x.val, hUV ▸ x.property⟩) :
    euclideanFixedPointIndex f hf = euclideanFixedPointIndex g hg := by
  subst V
  have h : f = g := ContinuousMap.ext heq
  subst g
  rfl

/-- Restricting the ambient ENR to an open subspace does not change the local
fixed-point index when the map's domain and image already lie there. This is
Dold's codomain localization: the actual Euclidean retracted map is unchanged. -/
theorem enr_open_codomain_index {X : Type*} [TopologicalSpace X]
    (e : ENRRepresentation X) (S U : Opens X) (hUS : U ≤ S)
    (f : C(U, X)) (hfS : ∀ x, f x ∈ S) (hK : IsCompact (enrLocalFixedSet f)) :
    let V : Opens S := ⟨Subtype.val ⁻¹' (U : Set X), U.isOpen.preimage continuous_subtype_val⟩
    let g : C(V, S) := ⟨fun x ↦ ⟨f ⟨x.val.val, x.property⟩, hfS _⟩, by fun_prop⟩
    ∃ hG : IsCompact (enrLocalFixedSet g),
      enrLocalFixedPointIndex e U f hK =
        enrLocalFixedPointIndex (openENRRepresentation e S) V g hG := by
  dsimp only
  let V : Opens S := ⟨Subtype.val ⁻¹' (U : Set X), U.isOpen.preimage continuous_subtype_val⟩
  let g : C(V, S) := ⟨fun x ↦ ⟨f ⟨x.val.val, x.property⟩, hfS _⟩, by fun_prop⟩
  let j : U ≃ₜ V :=
    { toFun := fun x ↦ ⟨⟨x.val, hUS x.property⟩, x.property⟩
      invFun := fun x ↦ ⟨x.val.val, x.property⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  have hset : enrLocalFixedSet g = j '' enrLocalFixedSet f := by
    ext x
    constructor
    · intro hx
      refine ⟨j.symm x, ?_, j.apply_symm_apply x⟩
      exact congrArg Subtype.val hx
    · rintro ⟨y, hy, rfl⟩
      exact Subtype.ext hy
  have hG : IsCompact (enrLocalFixedSet g) := hset ▸ hK.image j.continuous
  refine ⟨hG, ?_⟩
  let eS := openENRRepresentation e S
  have hdomain : enrRetractedOpenDomain e U = enrRetractedOpenDomain eS V := by
    ext z
    constructor
    · rintro ⟨hz, hu⟩
      refine ⟨⟨hz, hUS hu⟩, ?_⟩
      exact hu
    · rintro ⟨hz, hu⟩
      exact ⟨hz.choose, hu⟩
  unfold enrLocalFixedPointIndex enrRetractionIndex
  apply euclidean_index_congr_domain _ _ hdomain
  intro z
  rfl
/-- A map on an open part of an open Euclidean subspace has the same index as
its ambient Euclidean formula. The restricted identity retraction is still identity. -/
theorem open_euclidean_index {n : ℕ} (S : Opens (Euclidean n)) (V : Opens S)
    (g : C(V, S)) (hG : IsCompact (enrLocalFixedSet g)) :
    ∃ W : Opens (Euclidean n), (W : Set _) = Subtype.val '' (V : Set S) ∧
      ∃ F : C(W, Euclidean n),
        (∀ y : V, ∀ hy : y.val.val ∈ W, F ⟨y.val.val, hy⟩ = (g y).val) ∧
        ∃ hF : IsCompact (euclideanFixedSet F),
          enrLocalFixedPointIndex (openENRRepresentation (euclideanENRRepresentation n) S)
            V g hG = euclideanFixedPointIndex F hF := by
  let W : Opens (Euclidean n) :=
    ⟨Subtype.val '' (V : Set S), S.isOpen.isOpenMap_subtype_val _ V.isOpen⟩
  let j : V ≃ₜ W :=
    { toFun := fun x ↦ ⟨x.val.val, ⟨x.val, x.property, rfl⟩⟩
      invFun := fun x ↦ ⟨⟨x.val, by obtain ⟨y, _, hy⟩ := x.property; exact hy ▸ y.property⟩,
        by
          obtain ⟨y, hy, heq⟩ := x.property
          have hy' : (⟨x.val, by obtain ⟨y, _, hy⟩ := x.property; exact hy ▸ y.property⟩ : S) = y :=
            Subtype.ext heq.symm
          exact hy' ▸ hy⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  let F : C(W, Euclidean n) :=
    ⟨fun x ↦ (g (j.symm x)).val, by fun_prop⟩
  have heq : euclideanFixedSet F = j '' enrLocalFixedSet g := by
    ext x
    constructor
    · intro hx
      refine ⟨j.symm x, Subtype.ext hx, j.apply_symm_apply x⟩
    · rintro ⟨y, hy, rfl⟩
      change (g (j.symm (j y))).val = y.val.val
      rw [j.symm_apply_apply]
      exact congrArg Subtype.val hy
  have hF : IsCompact (euclideanFixedSet F) := heq ▸ hG.image j.continuous
  refine ⟨W, rfl, F, ?_, hF, ?_⟩
  · intro y hy
    change (g (j.symm ⟨y.val.val, hy⟩)).val = (g y).val
    rfl
  · have hdomain : enrRetractedOpenDomain
        (openENRRepresentation (euclideanENRRepresentation n) S) V = W := by
      ext z
      constructor
      · rintro ⟨hz, hv⟩
        exact ⟨⟨z, hz.choose_spec⟩, hv, rfl⟩
      · rintro ⟨y, hy, rfl⟩
        exact ⟨⟨Set.mem_univ _, y.property⟩, hy⟩
    unfold enrLocalFixedPointIndex enrRetractionIndex
    apply euclidean_index_congr_domain _ _ hdomain
    intro z
    rfl

/-- A local chart computes the original ENR index by the actual coordinate
conjugate. First restrict the ambient ENR to the chart source, apply global
homeomorphism conjugacy on source and target, and use the identity Euclidean
retraction on the target. All map domains and image guards remain explicit. -/
theorem chart_computes_enr_index {n : ℕ} {X : Type*} [TopologicalSpace X]
    [MetrizableSpace X] [LocallyCompactSpace X]
    (e : ENRRepresentation X) (c : OpenPartialHomeomorph X (Euclidean n))
    (U : Opens X) (hUc : (U : Set X) ⊆ c.source)
    (f : C(U, X)) (hfc : ∀ x, f x ∈ c.source)
    (hK : IsCompact (enrLocalFixedSet f)) :
    ∃ W : Opens (Euclidean n), (W : Set _) = c '' (U : Set X) ∧
      ∃ F : C(W, Euclidean n),
        (∀ x : U, ∀ hx : c x.val ∈ W, F ⟨c x.val, hx⟩ = c (f x)) ∧
        ∃ hF : IsCompact (euclideanFixedSet F),
          euclideanFixedPointIndex F hF = enrLocalFixedPointIndex e U f hK := by
  let S : Opens X := ⟨c.source, c.open_source⟩
  let T : Opens (Euclidean n) := ⟨c.target, c.open_target⟩
  let V : Opens S := ⟨Subtype.val ⁻¹' (U : Set X), U.isOpen.preimage continuous_subtype_val⟩
  let g : C(V, S) := ⟨fun x ↦ ⟨f ⟨x.val.val, x.property⟩, hfc _⟩, by fun_prop⟩
  obtain ⟨hG, hi⟩ := enr_open_codomain_index e S U hUc f hfc hK
  let eS := openENRRepresentation e S
  let eT := openENRRepresentation (euclideanENRRepresentation n) T
  let h : S ≃ₜ T := c.toHomeomorphSourceTarget
  let : MetrizableSpace S := MetrizableSpace.subtype (S : Set X)
  let : MetrizableSpace T := MetrizableSpace.subtype (T : Set (Euclidean n))
  let : LocallyCompactSpace S := S.isOpen.locallyCompactSpace
  let : LocallyCompactSpace T := T.isOpen.locallyCompactSpace
  have hb := enr_local_fixed_point_index_conjugacy S eS
  obtain ⟨hH, hconj⟩ := hb.2.2.2.2.2.2.1 T eT h V g hG
  obtain ⟨W, hW, F, hFval, hF, hindex⟩ := open_euclidean_index T
    (enrConjugateDomain h V) (enrConjugateLocalMap h V g) hH
  refine ⟨W, ?_, F, ?_, hF, hindex.symm.trans (hconj.trans hi.symm)⟩
  · rw [hW]
    ext y
    constructor
    · rintro ⟨z, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨x.val, hx, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      let z : S := ⟨x, hUc hx⟩
      exact ⟨h z, ⟨z, hx, rfl⟩, rfl⟩
  · intro x hx
    let z : S := ⟨x.val, hUc x.property⟩
    let y : enrConjugateDomain h V := ⟨h z, ⟨z, x.property, rfl⟩⟩
    have hy := hFval y hx
    change F ⟨c x.val, hx⟩ = _ at hy
    rw [hy]
    change c (f ⟨c.symm (c x.val), _⟩) = c (f x)
    congr 2
    exact Subtype.ext (c.left_inv (hUc x.property))

/-- Any open neighborhood containing exactly the marked fixed point computes
its canonical finite-set local index. Such a neighborhood lies in the canonical
complement of all other fixed points, so the ENR restriction law applies. -/
theorem finite_local_index_on_isolating_domain {X : Type u} [TopologicalSpace X]
    [MetrizableSpace X] [LocallyCompactSpace X] (e : ENRRepresentation X)
    (f : C(X, X)) (hfinite : {y : X | f y = y}.Finite)
    (x : X) (hx : f x = x) (U : Opens X) (hxU : x ∈ U)
    (hiso : ∀ y ∈ U, f y = y → y = x) :
    let g : C(U, X) := f.comp ⟨Subtype.val, continuous_subtype_val⟩
    ∃ hG : IsCompact (enrLocalFixedSet g),
      finiteFixedPointLocalIndex e f hfinite x = enrLocalFixedPointIndex e U g hG := by
  let V := finiteFixedPointOpenDomain f hfinite x
  let F := finiteFixedPointLocalMap f hfinite x
  have hUV : U ≤ V := by
    intro y hy hbad
    exact hbad.2 (by simpa using hiso y hy hbad.1)
  have hKF : IsCompact (enrLocalFixedSet F) := by
    change IsCompact ((Subtype.val : V → X) ⁻¹' {y : X | f y = y})
    exact (hfinite.preimage Subtype.val_injective.injOn).isCompact
  have hcover : ∀ y : V, F y = y.val → y.val ∈ U := by
    intro y hy
    have heq : y.val = x :=
      ((finiteFixedPointOpenDomain_isolating f hfinite x hx).2.2 y.val y.property).mp hy
    exact heq ▸ hxU
  obtain ⟨hG, hi⟩ :=
    (enr_local_fixed_point_index_conjugacy.{u,u} X e).2.2.1 V U hUV F hKF hcover
  exact ⟨hG, hi⟩

/-- At a fixed point, an invertible derivative of the coordinate displacement
computes the actual manifold local index. Shrink inside the canonical isolating
domain and the chart overlap, use nonlinear Euclidean linearization, and then
transport the resulting index through the chart. -/
theorem finite_local_index_of_chart_displacement {n : ℕ} {X : Type u}
    [TopologicalSpace X] [MetrizableSpace X] [LocallyCompactSpace X]
    (e : ENRRepresentation X) (f : C(X, X))
    (hfinite : {y : X | f y = y}.Finite) (x : X) (hx : f x = x)
    (c : OpenPartialHomeomorph X (Euclidean n)) (hxc : x ∈ c.source) (hc0 : c x = 0)
    (L : Euclidean n ≃L[ℝ] Euclidean n)
    (hd : HasFDerivAt (fun y ↦ y - c (f (c.symm y))) L.toContinuousLinearMap 0) :
    finiteFixedPointLocalIndex e f hfinite x =
      (SignType.sign (LinearMap.det L.toLinearMap) : ℤ) := by
  let V := finiteFixedPointOpenDomain f hfinite x
  let S := c.target ∩ c.symm ⁻¹' ((V : Set X) ∩ f ⁻¹' c.source)
  have hS : IsOpen S := c.isOpen_inter_preimage_symm
    (V.isOpen.inter (c.open_source.preimage f.continuous))
  have hsymm0 : c.symm 0 = x := hc0 ▸ c.left_inv hxc
  have h0S : (0 : Euclidean n) ∈ S := by
    refine ⟨hc0 ▸ c.map_source hxc, ?_⟩
    change c.symm 0 ∈ V ∧ f (c.symm 0) ∈ c.source
    rw [hsymm0, hx]
    exact ⟨(finiteFixedPointOpenDomain_isolating f hfinite x hx).2.1, hxc⟩
  let g : Euclidean n → Euclidean n := fun y ↦ c (f (c.symm y))
  have hg : ContinuousOn g S := c.continuousOn.comp
    (f.continuous.continuousOn.comp (c.continuousOn_symm.mono Set.inter_subset_left)
      (Set.mapsTo_univ _ _)) (fun y hy ↦ hy.2.2)
  have hg0 : g 0 = 0 := by dsimp [g]; rw [hsymm0, hx, hc0]
  obtain ⟨r, hr, hrS, F, hFval, hF, hindex⟩ :=
    FranksLocalIndex.local_index_of_invertible_displacement g S hS h0S hg hg0 L hd
  let B : Opens (Euclidean n) := ⟨Metric.ball 0 r, Metric.isOpen_ball⟩
  have hBt : (B : Set _) ⊆ c.target := fun y hy ↦ (hrS hy).1
  let U : Opens X := ⟨c.symm '' (B : Set _),
    c.isOpen_image_symm_of_subset_target B.isOpen hBt⟩
  have hUc : (U : Set X) ⊆ c.source := by
    rintro y ⟨z, hz, rfl⟩
    exact c.map_target (hBt hz)
  have hxU : x ∈ U := ⟨0, Metric.mem_ball_self hr, hsymm0⟩
  have hUV : (U : Set X) ⊆ V := by
    rintro y ⟨z, hz, rfl⟩
    exact (hrS hz).2.1
  have hiso : ∀ y ∈ U, f y = y → y = x := fun y hy hfy ↦
    ((finiteFixedPointOpenDomain_isolating f hfinite x hx).2.2 y (hUV hy)).mp hfy
  obtain ⟨hG, hi⟩ := finite_local_index_on_isolating_domain e f hfinite x hx U hxU hiso
  let G : C(U, X) := f.comp ⟨Subtype.val, continuous_subtype_val⟩
  have hGc : ∀ y : U, G y ∈ c.source := by
    rintro ⟨y, z, hz, rfl⟩
    exact (hrS hz).2.2
  obtain ⟨W, hW, H, hHval, hH, hchart⟩ := chart_computes_enr_index e c U hUc G hGc hG
  have hWB : W = B := by
    apply TopologicalSpace.Opens.ext
    rw [hW]
    ext y
    constructor
    · rintro ⟨z, ⟨w, hw, rfl⟩, rfl⟩
      simpa only [c.right_inv (hBt hw)] using hw
    · intro hy
      exact ⟨c.symm y, ⟨y, hy, rfl⟩, c.right_inv (hBt hy)⟩
  have hindices : euclideanFixedPointIndex H hH = euclideanFixedPointIndex F hF := by
    apply euclidean_index_congr_domain W B hWB
    intro y
    let z : U := ⟨c.symm y.val, ⟨y.val, hWB ▸ y.property, rfl⟩⟩
    have hz : c z.val = y.val := c.right_inv (hBt (hWB ▸ y.property))
    have hh := hHval z (hz.symm ▸ y.property)
    have hh' : H y = c (G z) := by simpa only [hz] using hh
    rw [hh', hFval]
    rfl
  exact hi.trans (hchart.symm.trans (hindices.trans hindex))

/-- The derivative in the preferred real chart is the actual manifold
 derivative with explicit source and target tangent-model identifications. -/
theorem preferred_chart_hasFDerivAt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
    (f : M → M) (x : M) (hx : f x = x)
    (hf : MDifferentiableAt (modelWithCornersSelf ℝ E) (modelWithCornersSelf ℝ E) f x) :
    HasFDerivAt (fun y ↦ chartAt E x (f ((chartAt E x).symm y)))
      ((tangentSpaceCastModel (modelWithCornersSelf ℝ E) (f x)).toContinuousLinearMap ∘L
        mfderiv (modelWithCornersSelf ℝ E) (modelWithCornersSelf ℝ E) f x ∘L
        (tangentSpaceCastModel (modelWithCornersSelf ℝ E) x).symm.toContinuousLinearMap)
      (chartAt E x x) := by
  have hh := hf.hasMFDerivAt.2
  simpa [writtenInExtChartAt, extChartAt, OpenPartialHomeomorph.extend, hx,
    Function.comp_def] using hh

/-- Translate the preferred chart to zero; its displacement derivative is the
identity minus the original tangent derivative in model coordinates. -/
theorem centered_chart_displacement {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (Euclidean n) X]
    (f : X → X) (x : X) (hx : f x = x)
    (hf : MDifferentiableAt (modelWithCornersSelf ℝ (Euclidean n))
      (modelWithCornersSelf ℝ (Euclidean n)) f x) :
    ∃ c : OpenPartialHomeomorph X (Euclidean n), x ∈ c.source ∧ c x = 0 ∧
      HasFDerivAt (fun y ↦ y - c (f (c.symm y)))
        (ContinuousLinearMap.id ℝ (Euclidean n) -
          ((tangentSpaceCastModel (modelWithCornersSelf ℝ (Euclidean n)) (f x)).toContinuousLinearMap ∘L
            mfderiv (modelWithCornersSelf ℝ (Euclidean n))
              (modelWithCornersSelf ℝ (Euclidean n)) f x ∘L
            (tangentSpaceCastModel (modelWithCornersSelf ℝ (Euclidean n)) x).symm.toContinuousLinearMap)) 0 := by
  let a := chartAt (Euclidean n) x x
  let c := (chartAt (Euclidean n) x).trans (Homeomorph.subRight a).toOpenPartialHomeomorph
  refine ⟨c, ⟨mem_chart_source _ _, Set.mem_univ _⟩, sub_self _, ?_⟩
  have hd := preferred_chart_hasFDerivAt f x hx hf
  have hi := (hasFDerivAt_id (𝕜 := ℝ) (0 : Euclidean n)).add_const a
  rw [← zero_add (chartAt (Euclidean n) x x)] at hd
  have hd' := hd.comp 0 (show HasFDerivAt (fun y : Euclidean n ↦ y+a)
    (ContinuousLinearMap.id ℝ (Euclidean n)) 0 from hi)
  have hsub := hd'.sub_const a
  have htotal := (hasFDerivAt_id (𝕜 := ℝ) (0 : Euclidean n)).sub hsub
  convert htotal using 1 <;> simp [c, a, Homeomorph.subRight,
    OpenPartialHomeomorph.trans, ContinuousLinearMap.comp_id]
  funext y
  rfl

/-- The canonical local index of a differentiable self-map at a nondegenerate
fixed point is the determinant sign of identity minus its actual manifold
 derivative, expressed through the tangent-model identifications. -/
theorem finite_local_index_of_mfderiv {n : ℕ} {X : Type u}
    [TopologicalSpace X] [MetrizableSpace X] [LocallyCompactSpace X]
    [ChartedSpace (Euclidean n) X]
    (e : ENRRepresentation X) (f : C(X, X))
    (hfinite : {y : X | f y = y}.Finite) (x : X) (hx : f x = x)
    (hf : MDifferentiableAt (modelWithCornersSelf ℝ (Euclidean n))
      (modelWithCornersSelf ℝ (Euclidean n)) f x)
    (L : Euclidean n ≃L[ℝ] Euclidean n)
    (hL : L.toContinuousLinearMap = ContinuousLinearMap.id ℝ (Euclidean n) -
      ((tangentSpaceCastModel (modelWithCornersSelf ℝ (Euclidean n)) (f x)).toContinuousLinearMap ∘L
        mfderiv (modelWithCornersSelf ℝ (Euclidean n))
          (modelWithCornersSelf ℝ (Euclidean n)) f x ∘L
        (tangentSpaceCastModel (modelWithCornersSelf ℝ (Euclidean n)) x).symm.toContinuousLinearMap)) :
    finiteFixedPointLocalIndex e f hfinite x =
      (SignType.sign (LinearMap.det L.toLinearMap) : ℤ) := by
  obtain ⟨c, hxc, hc0, hd⟩ := centered_chart_displacement f x hx hf
  exact finite_local_index_of_chart_displacement e f hfinite x hx c hxc hc0 L (by rw [hL]; exact hd)

/-- The preferred chart computation is the determinant of the original tangent
endomorphism itself, by determinant invariance under tangent-model conjugacy. -/
theorem finite_local_index_of_tangent_displacement {n : ℕ} {X : Type u}
    [TopologicalSpace X] [MetrizableSpace X] [LocallyCompactSpace X]
    [ChartedSpace (Euclidean n) X]
    (e : ENRRepresentation X) (f : C(X, X))
    (hfinite : {y : X | f y = y}.Finite) (x : X) (hx : f x = x)
    (hf : MDifferentiableAt (modelWithCornersSelf ℝ (Euclidean n))
      (modelWithCornersSelf ℝ (Euclidean n)) f x)
    (D : TangentSpace (modelWithCornersSelf ℝ (Euclidean n)) x →L[ℝ]
      TangentSpace (modelWithCornersSelf ℝ (Euclidean n)) x)
    (hD : D = 1 - (show TangentSpace (modelWithCornersSelf ℝ (Euclidean n)) x →L[ℝ]
      TangentSpace (modelWithCornersSelf ℝ (Euclidean n)) x from
        mfderiv (modelWithCornersSelf ℝ (Euclidean n))
          (modelWithCornersSelf ℝ (Euclidean n)) f x))
    (hInv : D.IsInvertible) :
    finiteFixedPointLocalIndex e f hfinite x = (SignType.sign (LinearMap.det D.toLinearMap) : ℤ) := by
  obtain ⟨A,hA⟩ := hInv
  let c := tangentSpaceCastModel (modelWithCornersSelf ℝ (Euclidean n)) x
  let L := c.symm.trans (A.trans c)
  have hL : L.toContinuousLinearMap = ContinuousLinearMap.id ℝ (Euclidean n) -
      ((tangentSpaceCastModel (modelWithCornersSelf ℝ (Euclidean n)) (f x)).toContinuousLinearMap ∘L
        mfderiv (modelWithCornersSelf ℝ (Euclidean n))
          (modelWithCornersSelf ℝ (Euclidean n)) f x ∘L c.symm.toContinuousLinearMap) := by
    apply ContinuousLinearMap.ext
    intro v
    change c (A (c.symm v)) = v - _
    have he := congrArg (fun T ↦ T (c.symm v)) (hA.trans hD)
    change A (c.symm v) = c.symm v - _ at he
    rw [he, map_sub, c.apply_symm_apply]
    congr 1
  have hi := finite_local_index_of_mfderiv e f hfinite x hx hf L hL
  have hd : LinearMap.det L.toLinearMap = LinearMap.det D.toLinearMap := by
    have he : L.toLinearMap = c.toLinearEquiv.toLinearMap.comp
        (A.toLinearMap.comp c.symm.toLinearEquiv.toLinearMap) := rfl
    exact (LinearMap.det_conj A.toLinearMap c.toLinearEquiv).trans
      (congrArg (fun T ↦ LinearMap.det T.toLinearMap) hA)
  exact hi.trans (congrArg (fun t : ℝ ↦ (SignType.sign t : ℤ)) hd)


/-- A local conjugacy transports the chart displacement formula to its original
fixed-point index. This applies to a covering sheet without any metric on the cover. -/
theorem finite_local_index_of_local_conjugate_chart {n : ℕ} {X : Type v} {Y : Type u}
    [TopologicalSpace X] [TopologicalSpace Y] [MetrizableSpace Y] [LocallyCompactSpace Y]
    (eY : ENRRepresentation Y) (f : C(Y, Y)) (g : C(X, X))
    (hfinite : {y : Y | f y = y}.Finite) (x : Y) (hx : f x = x)
    (e : OpenPartialHomeomorph Y X) (hxe : x ∈ e.source)
    (hconj : ∀ z ∈ e.source, f z ∈ e.source → e (f z) = g (e z))
    (c : OpenPartialHomeomorph X (Euclidean n)) (hxc : e x ∈ c.source) (hc0 : c (e x) = 0)
    (L : Euclidean n ≃L[ℝ] Euclidean n)
    (hd : HasFDerivAt (fun y ↦ y - c (g (c.symm y))) L.toContinuousLinearMap 0) :
    finiteFixedPointLocalIndex eY f hfinite x = (SignType.sign (LinearMap.det L.toLinearMap) : ℤ) := by
  let C := e.trans c
  have hxC : x ∈ C.source := ⟨hxe, hxc⟩
  have hC0 : C x = 0 := hc0
  have h0C : (0 : Euclidean n) ∈ C.target := hC0 ▸ C.map_source hxC
  have hCx : C.symm 0 = x := hC0 ▸ C.left_inv hxC
  have hcs := C.continuousAt_symm h0C
  have hnear : ∀ᶠ y in 𝓝 (0 : Euclidean n), f (C.symm y) ∈ e.source := by
    have h := (f.continuous.continuousAt.comp hcs).eventually
      (e.open_source.mem_nhds (show f (C.symm 0) ∈ e.source by rw [hCx, hx]; exact hxe))
    exact h
  have heq : (fun y ↦ y - C (f (C.symm y))) =ᶠ[𝓝 0] (fun y ↦ y - c (g (c.symm y))) := by
    filter_upwards [C.open_target.mem_nhds h0C, hnear] with y hy hfy
    have hyS : C.symm y ∈ C.source := C.map_target hy
    have hyT : c.symm y ∈ e.target := hy.2
    change y - c (e (f (C.symm y))) = y - c (g (c.symm y))
    rw [hconj _ hyS.1 hfy]
    congr 3
    exact e.right_inv hyT
  apply finite_local_index_of_chart_displacement eY f hfinite x hx C hxC hC0 L
  exact hd.congr_of_eventuallyEq heq

/-- A covering sheet transfers an invertible original tangent displacement to
the upstairs local fixed-point index. No smooth or Riemannian structure upstairs is needed. -/
theorem finite_local_index_of_local_conjugate_tangent {n : ℕ} {X : Type v} {Y : Type u}
    [TopologicalSpace X] [TopologicalSpace Y] [MetrizableSpace Y] [LocallyCompactSpace Y]
    [ChartedSpace (Euclidean n) X]
    (eY : ENRRepresentation Y) (f : C(Y, Y)) (g : C(X, X))
    (hfinite : {y : Y | f y = y}.Finite) (x : Y) (hx : f x = x)
    (e : OpenPartialHomeomorph Y X) (hxe : x ∈ e.source)
    (hconj : ∀ z ∈ e.source, f z ∈ e.source → e (f z) = g (e z))
    (hg : MDifferentiableAt (modelWithCornersSelf ℝ (Euclidean n))
      (modelWithCornersSelf ℝ (Euclidean n)) g (e x))
    (D : TangentSpace (modelWithCornersSelf ℝ (Euclidean n)) (e x) →L[ℝ]
      TangentSpace (modelWithCornersSelf ℝ (Euclidean n)) (e x))
    (hD : D = 1 - (show TangentSpace (modelWithCornersSelf ℝ (Euclidean n)) (e x) →L[ℝ]
      TangentSpace (modelWithCornersSelf ℝ (Euclidean n)) (e x) from
        mfderiv (modelWithCornersSelf ℝ (Euclidean n))
          (modelWithCornersSelf ℝ (Euclidean n)) g (e x)))
    (hInv : D.IsInvertible) :
    finiteFixedPointLocalIndex eY f hfinite x = (SignType.sign (LinearMap.det D.toLinearMap) : ℤ) := by
  have hxg : g (e x) = e x := (hconj x hxe (by simpa only [hx] using hxe)).symm.trans (congrArg e hx)
  obtain ⟨A,hA⟩ := hInv
  let c := tangentSpaceCastModel (modelWithCornersSelf ℝ (Euclidean n)) (e x)
  let L := c.symm.trans (A.trans c)
  have hL : L.toContinuousLinearMap = ContinuousLinearMap.id ℝ (Euclidean n) -
      ((tangentSpaceCastModel (modelWithCornersSelf ℝ (Euclidean n)) (g (e x))).toContinuousLinearMap ∘L
        mfderiv (modelWithCornersSelf ℝ (Euclidean n))
          (modelWithCornersSelf ℝ (Euclidean n)) g (e x) ∘L c.symm.toContinuousLinearMap) := by
    apply ContinuousLinearMap.ext
    intro v
    change c (A (c.symm v)) = v - _
    have he := congrArg (fun T ↦ T (c.symm v)) (hA.trans hD)
    change A (c.symm v) = c.symm v - _ at he
    rw [he, map_sub, c.apply_symm_apply]
    congr 1
  obtain ⟨C, hxC, hC0, hd⟩ := centered_chart_displacement g (e x) hxg hg
  have hi := finite_local_index_of_local_conjugate_chart eY f g hfinite x hx e hxe
    hconj C hxC hC0 L (by rw [hL]; exact hd)
  have hdet : LinearMap.det L.toLinearMap = LinearMap.det D.toLinearMap :=
    (LinearMap.det_conj A.toLinearMap c.toLinearEquiv).trans (congrArg (fun T : TangentSpace (modelWithCornersSelf ℝ (Euclidean n)) (e x) →L[ℝ] TangentSpace (modelWithCornersSelf ℝ (Euclidean n)) (e x) ↦ LinearMap.det T.toLinearMap) hA)
  exact hi.trans (congrArg (fun t : ℝ ↦ (SignType.sign t : ℤ)) hdet)

/-- A lift through a local homeomorphism has the original tangent displacement
index at each fixed point. The preferred sheet has forward function exactly p. -/
theorem finite_local_index_of_cover_tangent {n : ℕ} {X : Type v} {Y : Type u}
    [TopologicalSpace X] [TopologicalSpace Y] [MetrizableSpace Y] [LocallyCompactSpace Y]
    [ChartedSpace (Euclidean n) X]
    (eY : ENRRepresentation Y) (f : C(Y, Y)) (g : C(X, X))
    (hfinite : {y : Y | f y = y}.Finite) (x : Y) (hx : f x = x)
    (p : Y → X) (hp : IsLocalHomeomorph p) (hconj : ∀ y, p (f y) = g (p y))
    (hg : MDifferentiableAt (modelWithCornersSelf ℝ (Euclidean n))
      (modelWithCornersSelf ℝ (Euclidean n)) g (p x))
    (D : TangentSpace (modelWithCornersSelf ℝ (Euclidean n)) (p x) →L[ℝ]
      TangentSpace (modelWithCornersSelf ℝ (Euclidean n)) (p x))
    (hD : D = 1 - (show TangentSpace (modelWithCornersSelf ℝ (Euclidean n)) (p x) →L[ℝ]
      TangentSpace (modelWithCornersSelf ℝ (Euclidean n)) (p x) from
        mfderiv (modelWithCornersSelf ℝ (Euclidean n))
          (modelWithCornersSelf ℝ (Euclidean n)) g (p x)))
    (hInv : D.IsInvertible) :
    finiteFixedPointLocalIndex eY f hfinite x = (SignType.sign (LinearMap.det D.toLinearMap) : ℤ) := by
  let e := (hp.localInverseAt x).symm
  have he : (e : Y → X) = p := hp.localInverseAt_symm x
  have hg' : MDifferentiableAt (modelWithCornersSelf ℝ (Euclidean n))
      (modelWithCornersSelf ℝ (Euclidean n)) g (e x) := by simpa only [he] using hg
  exact finite_local_index_of_local_conjugate_tangent eY f g hfinite x hx e
    hp.self_mem_localInverseAt_target (by intro z _ _; simpa only [he] using hconj z)
    hg' D (by
      exact hD.trans (congrArg (fun z : X ↦
        (1 : Euclidean n →L[ℝ] Euclidean n) - (show Euclidean n →L[ℝ] Euclidean n from
          mfderiv (modelWithCornersSelf ℝ (Euclidean n))
            (modelWithCornersSelf ℝ (Euclidean n)) g z)) (congrFun he x).symm)) hInv

end
end HolomorphicAnosov.FixedPointIndexInterface


