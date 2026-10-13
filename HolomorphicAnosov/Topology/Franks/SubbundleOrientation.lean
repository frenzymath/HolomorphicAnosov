import HolomorphicAnosov.Topology.Franks.CharacteristicTorusCover
import HolomorphicAnosov.Geometry.Manifold.VectorBundle.ContinuousRealTangentSubbundleFinrank
import HolomorphicAnosov.Geometry.Manifold.VectorBundle.RealTangentSubbundleSpace
import HolomorphicAnosov.Topology.RealVectorBundleOrientationMonodromy
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.VectorBundle.Constructions
import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

noncomputable section
namespace HolomorphicAnosov.FranksSubbundleOrientation
open Bundle
open scoped ContDiff _root_.Topology
set_option backward.isDefEq.respectTransparency false

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H} {X : Type*}
variable [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ∞ X]

/-- Constant rank identifies the local model dimension with the chosen fibre rank. -/
theorem fixed_rank_chart [PreconnectedSpace X]
    (P : ContinuousRealTangentSubbundle I X) (x₀ x : X) :
    let d := Module.finrank ℝ (P.toDistribution x₀)
    letI := realSubbundleTotalSpaceTopology I P.toDistribution d
    ∃ e : Trivialization (Fin d → ℝ)
      (TotalSpace.proj (F := Fin d → ℝ) (E := fun y ↦ ↥(P.toDistribution y))),
      x ∈ e.baseSet ∧ e.IsLinear ℝ := by
  obtain ⟨r, e, hx, he⟩ := P.locally_trivial x
  let := realSubbundleTotalSpaceTopology I P.toDistribution r
  have := he
  have hr : r = Module.finrank ℝ (P.toDistribution x₀) := by
    have h := (e.linearEquivAt ℝ x hx).finrank_eq
    simpa using h.symm.trans (P.finrank_eq x x₀)
  subst r
  exact ⟨e, hx, he⟩

/-- The original tangent inclusion induces the expected topology on each fibre. -/
theorem fibre_inclusion_isInducing (P : ContinuousRealTangentSubbundle I X) (d : ℕ) (x : X) :
    letI := realSubbundleTotalSpaceTopology I P.toDistribution d
    Topology.IsInducing (@TotalSpace.mk X (Fin d → ℝ) (fun y ↦ ↥(P.toDistribution y)) x) := by
  let := realSubbundleTotalSpaceTopology I P.toDistribution d
  refine ⟨?_⟩
  change (inferInstance : TopologicalSpace ↥(P.toDistribution x)) =
    TopologicalSpace.induced _ (TopologicalSpace.induced _ _)
  rw [induced_compose]
  exact ((FiberBundle.totalSpaceMk_isInducing E (TangentSpace I) x).comp
    Topology.IsInducing.subtypeVal).eq_induced

/-- The full atlas of linear charts registers the actual constant-rank subbundle. -/
@[instance_reducible]
def fibreBundle [PreconnectedSpace X]
    (P : ContinuousRealTangentSubbundle I X) (x₀ : X) :
    let d := Module.finrank ℝ (P.toDistribution x₀)
    letI := realSubbundleTotalSpaceTopology I P.toDistribution d
    FiberBundle (Fin d → ℝ) (fun y ↦ ↥(P.toDistribution y)) := by
  classical
  let d := Module.finrank ℝ (P.toDistribution x₀)
  letI := realSubbundleTotalSpaceTopology I P.toDistribution d
  exact {
    totalSpaceMk_isInducing' := fibre_inclusion_isInducing P d
    trivializationAtlas' := {e | e.IsLinear ℝ}
    trivializationAt' := fun x ↦ (fixed_rank_chart P x₀ x).choose
    mem_baseSet_trivializationAt' := fun x ↦ (fixed_rank_chart P x₀ x).choose_spec.1
    trivialization_mem_atlas' := fun x ↦ (fixed_rank_chart P x₀ x).choose_spec.2 }

/-- In finite dimension, joint continuity of chart changes implies operator continuity. -/
theorem vectorBundle [PreconnectedSpace X]
    (P : ContinuousRealTangentSubbundle I X) (x₀ : X) :
    let d := Module.finrank ℝ (P.toDistribution x₀)
    letI := realSubbundleTotalSpaceTopology I P.toDistribution d
    letI := fibreBundle P x₀
    VectorBundle ℝ (Fin d → ℝ) (fun y ↦ ↥(P.toDistribution y)) := by
  let d := Module.finrank ℝ (P.toDistribution x₀)
  let := realSubbundleTotalSpaceTopology I P.toDistribution d
  let := fibreBundle P x₀
  have hlin (e : Trivialization (Fin d → ℝ)
      (TotalSpace.proj (F := Fin d → ℝ) (E := fun y ↦ ↥(P.toDistribution y))))
      [MemTrivializationAtlas e] : e.IsLinear ℝ := MemTrivializationAtlas.out (e := e)
  refine ⟨hlin, ?_⟩
  intro e e' he he'
  have := hlin e
  have := hlin e'
  apply continuousOn_clm_apply.mpr
  intro v
  apply continuousOn_iff_continuous_domRestrict.mpr
  have hi : Continuous (fun x : ↥(e.baseSet ∩ e'.baseSet) ↦
      e.toOpenPartialHomeomorph.symm (x.val, v)) :=
    e.toOpenPartialHomeomorph.continuousOn_symm.comp_continuous
      (continuous_subtype_val.prodMk continuous_const)
      (fun x ↦ by rw [e.target_eq]; exact ⟨x.property.1, Set.mem_univ _⟩)
  have hj := e'.continuousOn.comp_continuous hi (fun x ↦ by
    rw [e'.source_eq]
    simpa only [Set.mem_preimage, e.symm_coe_proj x.property.1] using x.property.2)
  apply (continuous_snd.comp hj).congr
  intro x
  exact congrArg Prod.snd (e.apply_symm_apply_eq_coordChangeL e' x.property v)

/-- At a fixed fibre, orientation comparison is exactly the determinant sign.
The assertion includes rank zero, where the determinant and comparison are both one. -/
theorem comparison_eq_det_sign {V : Type*} [AddCommGroup V] [Module ℝ V]
    [Module.Free ℝ V] [Module.Finite ℝ V] (d : ℕ) (L : V ≃ₗ[ℝ] V)
    (o : RealBasisOrientation d V) :
    (realOrientationComparison d L o o : ℤ) = (SignType.sign (LinearMap.det L.toLinearMap) : ℤ) := by
  classical
  induction o using Quotient.inductionOn with
  | h b =>
    have heq : realOrientationMap L (Quotient.mk _ b) = Quotient.mk _ b ↔
        0 < LinearMap.det L.toLinearMap := by
      change Quotient.mk _ (b.map L) = Quotient.mk _ b ↔ _
      rw [Quotient.eq]
      exact b.orientation_comp_linearEquiv_eq_iff_det_pos L
    have hn : LinearMap.det L.toLinearMap ≠ 0 := L.isUnit_det'.ne_zero
    by_cases hp : 0 < LinearMap.det L.toLinearMap
    · simp [realOrientationComparison, heq.mpr hp, sign_eq_one_iff.mpr hp]
    · have hneg : LinearMap.det L.toLinearMap < 0 := lt_of_le_of_ne (le_of_not_gt hp) hn
      simp [realOrientationComparison, mt heq.mp hp, sign_eq_neg_one_iff.mpr hneg]

local instance pullbackAddCommGroup {A B : Type*} (p : A → B) (V : B → Type*)
    [∀ b, AddCommGroup (V b)] (a : A) : AddCommGroup ((p *ᵖ V) a) :=
  inferInstanceAs (AddCommGroup (V (p a)))

/-- A continuous orientation along a map is a continuous section of its actual
pullback vector bundle. This is checked in the original linear charts. -/
theorem section_pullback_continuous
    {A B : Type*} [TopologicalSpace A] [TopologicalSpace B] (d : ℕ)
    (V : B → Type*) [∀ b, AddCommGroup (V b)] [∀ b, Module ℝ (V b)]
    [∀ b, TopologicalSpace (V b)] [TopologicalSpace (TotalSpace (Fin d → ℝ) V)]
    [FiberBundle (Fin d → ℝ) V] [VectorBundle ℝ (Fin d → ℝ) V]
    (p : C(A, B)) (o : ∀ a, RealBasisOrientation d (V (p a)))
    (ho : letI := realOrientationTopology d V
      Continuous (fun a ↦ (⟨p a, o a⟩ : RealOrientationTotal d V))) :
    letI := realOrientationTopology d ((p : A → B) *ᵖ V)
    Continuous (fun a ↦ (⟨a, o a⟩ : RealOrientationTotal d ((p : A → B) *ᵖ V))) := by
  classical
  let := realOrientationTopology d V
  let := realOrientationTopology d ((p : A → B) *ᵖ V)
  apply continuous_iff_continuousAt.mpr
  intro a
  let e := trivializationAt (Fin d → ℝ) V (p a)
  let ep := e.pullback p
  let U := ep.baseSet
  have ha : a ∈ U := mem_baseSet_trivializationAt (Fin d → ℝ) V (p a)
  let c (x : U) := realOrientationMap (e.linearEquivAt ℝ (p x.val) x.property) (o x.val)
  have hc : Continuous c :=
    continuous_snd.comp ((OrientationMonodromyProof.chartHomeomorph d V e).continuous.comp
      ((ho.comp continuous_subtype_val).subtype_mk (fun x ↦ x.property)))
  have hi := (OrientationMonodromyProof.chartInverse_continuous d ((p : A → B) *ᵖ V) ep).comp
    (continuous_id.prodMk hc)
  have hs : Continuous (fun x : U ↦
      (⟨x.val, o x.val⟩ : RealOrientationTotal d ((p : A → B) *ᵖ V))) := by
    apply hi.congr
    intro x
    change (⟨x.val, realOrientationMap (ep.linearEquivAt ℝ x.val x.property).symm (c x)⟩ :
      RealOrientationTotal d ((p : A → B) *ᵖ V)) = _
    congr 1
    have he : ep.linearEquivAt ℝ x.val x.property = e.linearEquivAt ℝ (p x.val) x.property := by
      ext v
      rfl
    rw [he]
    exact (OrientationMonodromyProof.orientationEquiv
      (e.linearEquivAt ℝ (p x.val) x.property)).left_inv (o x.val)
  exact (continuousOn_iff_continuous_domRestrict.mpr hs).continuousAt (ep.open_baseSet.mem_nhds ha)

/-- A continuous orientation section on a connected pullback gives one comparison
sign for every continuous bundle automorphism covering a continuous base map. -/
theorem comparison_along_constant
    {A B : Type*} [TopologicalSpace A] [PreconnectedSpace A] [TopologicalSpace B] (d : ℕ)
    (V : B → Type*) [∀ b, AddCommGroup (V b)] [∀ b, Module ℝ (V b)]
    [∀ b, TopologicalSpace (V b)] [TopologicalSpace (TotalSpace (Fin d → ℝ) V)]
    [FiberBundle (Fin d → ℝ) V] [VectorBundle ℝ (Fin d → ℝ) V]
    (p : C(A, B)) (o : ∀ a, RealBasisOrientation d (V (p a)))
    (ho : letI := realOrientationTopology d V
      Continuous (fun a ↦ (⟨p a, o a⟩ : RealOrientationTotal d V)))
    (T : C(A, A)) (L : ∀ a, V (p a) ≃ₗ[ℝ] V (p (T a)))
    (hL : Continuous (fun z : TotalSpace (Fin d → ℝ) ((p : A → B) *ᵖ V) ↦
      (⟨T z.proj, L z.proj z.snd⟩ : TotalSpace (Fin d → ℝ) ((p : A → B) *ᵖ V)))) :
    ∀ a b, realOrientationComparison d (L a) (o a) (o (T a)) =
      realOrientationComparison d (L b) (o b) (o (T b)) := by
  intro a b
  exact (inferInstance : PreconnectedSpace A).constant
    (OrientationMonodromyProof.comparison_continuous d ((p : A → B) *ᵖ V) o
      (section_pullback_continuous d V p o ho) T T.continuous L hL)

/-- The original derivative restricts to a continuous bundle isomorphism on
an invariant subbundle pulled back along a semiconjugacy. -/
theorem derivative_lift_bundle_map
    {A : Type*} [TopologicalSpace A] (P : ContinuousRealTangentSubbundle I X)
    (d : ℕ) (f : Diffeomorph I I X X ∞)
    (hP : ∀ x, (P.toDistribution x).map (mfderiv I I f x).toLinearMap = P.toDistribution (f x))
    (p : C(A, X)) (T : C(A, A)) (hp : ∀ a, p (T a) = f (p a)) :
    letI := realSubbundleTotalSpaceTopology I P.toDistribution d
    ∃ L : ∀ a, P.toDistribution (p a) ≃L[ℝ] P.toDistribution (p (T a)),
      (∀ a v, (L a v : TangentSpace I (p (T a))) = mfderiv I I f (p a) v) ∧
      Continuous (fun z : TotalSpace (Fin d → ℝ) ((p : A → X) *ᵖ (fun y ↦ ↥(P.toDistribution y))) ↦
        (⟨T z.proj, L z.proj z.snd⟩ :
          TotalSpace (Fin d → ℝ) ((p : A → X) *ᵖ (fun y ↦ ↥(P.toDistribution y))))) := by
  let := realSubbundleTotalSpaceTopology I P.toDistribution d
  let V := fun y ↦ ↥(P.toDistribution y)
  have hInv (a : A) : (P.toDistribution (p a)).map
      (f.mfderivToContinuousLinearEquiv (by simp) (p a)).toLinearMap = P.toDistribution (p (T a)) := by
    rw [hp]
    exact hP (p a)
  let L (a : A) := (f.mfderivToContinuousLinearEquiv (by simp) (p a)).ofSubmodules _ _ (hInv a)
  refine ⟨L, fun _ _ ↦ rfl, ?_⟩
  apply (inducing_pullbackTotalSpaceEmbedding (Fin d → ℝ) V (p : A → X)).continuous_iff.mpr
  have hbase : Continuous (fun z : TotalSpace (Fin d → ℝ) ((p : A → X) *ᵖ V) ↦ T z.proj) :=
    T.continuous.comp (Pullback.continuous_proj _ _ _)
  have hinc : Continuous (realSubbundleInclusion I P.toDistribution d) := continuous_induced_dom
  have hraw := f.contMDiff.continuous_tangentMap (show (1 : WithTop ℕ∞) ≤ ∞ by simp)
  have hv : Continuous (fun z : TotalSpace (Fin d → ℝ) ((p : A → X) *ᵖ V) ↦
      (⟨p (T z.proj), L z.proj z.snd⟩ : TotalSpace (Fin d → ℝ) V)) := by
    apply (show Topology.IsInducing (realSubbundleInclusion I P.toDistribution d) from ⟨rfl⟩).continuous_iff.mpr
    apply (hraw.comp (hinc.comp (Pullback.continuous_lift _ _ _))).congr
    intro z
    change (⟨f (p z.proj), mfderiv I I f (p z.proj) z.snd.val⟩ : TangentBundle I X) =
      ⟨p (T z.proj), (L z.proj z.snd).val⟩
    apply TotalSpace.ext
    · exact (hp z.proj).symm
    · rfl
  exact hbase.prodMk hv

/-- At a fixed base point, comparison equals the determinant sign of the return
endomorphism, independently of which orientation was chosen. -/
theorem comparison_fixed_eq_det_sign
    {A : Type*} (V : A → Type*) [∀ a, AddCommGroup (V a)] [∀ a, Module ℝ (V a)]
    [∀ a, Module.Free ℝ (V a)] [∀ a, Module.Finite ℝ (V a)]
    (d : ℕ) (o : ∀ a, RealBasisOrientation d (V a)) (a b : A) (h : b = a)
    (L : V a ≃ₗ[ℝ] V b) :
    (realOrientationComparison d L (o a) (o b) : ℤ) =
      (SignType.sign (LinearMap.det (show V a ≃ₗ[ℝ] V a from h ▸ L).toLinearMap) : ℤ) := by
  subst b
  exact comparison_eq_det_sign d L (o a)

/-- Every lift to the doubled torus cover has a constant comparison sign on the
original invariant subbundle. The orientation and derivative are genuine pullbacks. -/
theorem doubled_derivative_comparison_constant [PreconnectedSpace X]
    {n : ℕ} (q : X ≃ₜ UnitAddTorus (Fin n))
    (P : ContinuousRealTangentSubbundle I X) (f : Diffeomorph I I X X ∞)
    (hP : ∀ x, (P.toDistribution x).map (mfderiv I I f x).toLinearMap = P.toDistribution (f x))
    (T : C(UnitAddTorus (Fin n), UnitAddTorus (Fin n)))
    (hp : ∀ a, q.symm (2 • T a) = f (q.symm (2 • a))) :
    let d := Module.finrank ℝ (P.toDistribution (q.symm 0))
    ∃ (o : ∀ a : UnitAddTorus (Fin n), RealBasisOrientation d (P.toDistribution (q.symm (2 • a))))
      (L : ∀ a, P.toDistribution (q.symm (2 • a)) ≃L[ℝ] P.toDistribution (q.symm (2 • T a))),
      (∀ a v, (L a v : TangentSpace I (q.symm (2 • T a))) = mfderiv I I f (q.symm (2 • a)) v) ∧
      ∀ a b, realOrientationComparison d (L a).toLinearEquiv (o a) (o (T a)) =
        realOrientationComparison d (L b).toLinearEquiv (o b) (o (T b)) := by
  let d := Module.finrank ℝ (P.toDistribution (q.symm 0))
  let := realSubbundleTotalSpaceTopology I P.toDistribution d
  let := fibreBundle P (q.symm 0)
  have := vectorBundle P (q.symm 0)
  let p : C(UnitAddTorus (Fin n), X) := ⟨fun a ↦ q.symm (2 • a),
    q.symm.continuous.comp (continuous_id.const_smul 2)⟩
  obtain ⟨o, ho⟩ := Topology.FranksCover.doubled_orientation_section q d (fun y ↦ ↥(P.toDistribution y))
  obtain ⟨L, hL, hc⟩ := derivative_lift_bundle_map P d f hP p T hp
  exact ⟨o, L, hL, comparison_along_constant d (fun y ↦ ↥(P.toDistribution y))
    p o ho T (fun a ↦ (L a).toLinearEquiv) hc⟩

/-- An endomorphism with the same underlying subspace action computes the
comparison at a fixed base point, regardless of dependent fibre transport. -/
theorem comparison_of_submodule_action {A W : Type*}
    [AddCommGroup W] [Module ℝ W] [Module.Free ℝ W] [Module.Finite ℝ W]
    (V : A → Submodule ℝ W) (d : ℕ) (o : ∀ a, RealBasisOrientation d (V a))
    (a b : A) (h : b = a) (L : V a ≃ₗ[ℝ] V b) (K : V a ≃ₗ[ℝ] V a)
    (hLK : ∀ v, (L v : W) = K v) :
    (realOrientationComparison d L (o a) (o b) : ℤ) =
      (SignType.sign (LinearMap.det K.toLinearMap) : ℤ) := by
  subst b
  have he : L = K := by ext v; exact hLK v
  subst L
  exact comparison_eq_det_sign d K (o a)

omit [IsManifold I ∞ X] in
/-- The same comparison criterion for actual tangent subspaces, keeping their
point-dependent algebraic instances explicit through the model identifications. -/
theorem comparison_of_tangent_action {A : Type*} [FiniteDimensional ℝ E]
    (P : RealTangentDistribution I X) (p : A → X) (d : ℕ)
    (o : ∀ a, RealBasisOrientation d (P (p a))) (a b : A) (h : b = a)
    (L : P (p a) ≃ₗ[ℝ] P (p b)) (K : P (p a) ≃ₗ[ℝ] P (p a))
    (hLK : ∀ v, tangentSpaceCastModel I (p b) (L v) = tangentSpaceCastModel I (p a) (K v)) :
    (realOrientationComparison d L (o a) (o b) : ℤ) =
      (SignType.sign (LinearMap.det K.toLinearMap) : ℤ) := by
  subst b
  have he : L = K := by
    ext v
    exact (tangentSpaceCastModel I (p a)).injective (hLK v)
  subst L
  exact comparison_eq_det_sign d K (o a)

end HolomorphicAnosov.FranksSubbundleOrientation


