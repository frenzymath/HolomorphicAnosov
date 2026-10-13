import HolomorphicAnosov.Geometry.SmoothAffineConnection.OpenRestrictionField
import HolomorphicAnosov.Geometry.SmoothAffineConnection.CoordinateFrameExpansion
import HolomorphicAnosov.Geometry.SmoothAffineConnection.CoordinateCoefficientSmooth
import HolomorphicAnosov.Geometry.SmoothAffineConnection.FiniteFrameExpansion
import HolomorphicAnosov.Geometry.Riemannian.Gauss.CoordinateFrameGerm
import HolomorphicAnosov.Geometry.SmoothAffineConnection.ChristoffelLaws
import Mathlib.Geometry.Manifold.VectorField.LieBracket
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.Geometry.Manifold.BumpFunction

/-!
# Smooth affine connections on the real tangent bundle


-/ 

open Bundle IsManifold Module TopologicalSpace
open scoped Manifold ContDiff Topology _root_.Topology
namespace HolomorphicAnosov
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

/-- Repeated multiplication by smooth scalar functions is associative up to the commutative order of real scalars. This is the concrete product law behind the local scalar action in Andrews Definition 8.2.1(3), p.72. -/
theorem LocalSmoothVectorField.mulFunction_mulFunction
    {U : Opens M} (X : LocalSmoothVectorField E M U)
    (f g : U → ℝ) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ f)
    (hg : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ g) :
    (X.mulFunction f hf).mulFunction g hg =
      X.mulFunction (fun p ↦ f p * g p) (hf.smul hg) := by
  ext p
  simp [LocalSmoothVectorField.mulFunction, smul_smul, mul_comm]

/-- Scalar multiplication preserves the genuine tangent-bundle restriction relation. If local scalar functions agree under the open inclusion, the corresponding multiplied local fields agree after the canonical derivative of that inclusion. -/
theorem LocalSmoothVectorField.IsRestriction.mulFunction
    {U V : Opens M} (hVU : V ≤ U)
    {XU : LocalSmoothVectorField E M U} {XV : LocalSmoothVectorField E M V}
    {fU : U → ℝ} {fV : V → ℝ}
    (hX : LocalSmoothVectorField.IsRestriction hVU XU XV)
    (hfv : ∀ p : V, fV p = fU (Opens.inclusion hVU p))
    (hfU : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ fU)
    (hfV : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ fV) :
    LocalSmoothVectorField.IsRestriction hVU
      (XU.mulFunction fU hfU) (XV.mulFunction fV hfV) := by
  intro p
  change mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (Opens.inclusion hVU) p (fV p • XV p) =
    fU (Opens.inclusion hVU p) • XU (Opens.inclusion hVU p)
  rw [map_smul, hfv p, hX p]

/-- If a Christoffel coordinate formula is available, a pair of local fields whose coordinate germs are constant at a point evaluates the corresponding Christoffel coefficient. This is the finite-sum extraction used in the coordinate reconstruction in Andrews, Lecture 8, Proposition 8.3.1. -/
theorem christoffel_coefficient_of_coordinate_germs
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M]
    (cov : LocalBilinearCovariantDerivative E M) (U : Opens M) {n : ℕ}
    (b : Basis (Fin n) ℝ E) (c : OpenPartialHomeomorph U E)
    (Γ : Fin n → Fin n → Fin n → U → ℝ)
    (hΓ : ∀ (X Y : LocalSmoothVectorField E M U) (p : U), p ∈ c.source → ∀ k,
      (cov U X Y).tangentCoefficient b c p k =
        (∑ i, X.tangentCoefficient b c p i *
          fderiv ℝ (Y.coordinateCoefficient b c k) (c p) (b i)) +
        ∑ i, ∑ j, X.tangentCoefficient b c p i *
          Y.tangentCoefficient b c p j * Γ i j k p)
    (p : U) (hp : p ∈ c.source) (i j k : Fin n)
    (X Y : LocalSmoothVectorField E M U)
    (hX : ∀ᶠ q in 𝓝 p, mvfderiv 𝓘(ℝ, E) c q (X q) = b i)
    (hY : ∀ᶠ q in 𝓝 p, mvfderiv 𝓘(ℝ, E) c q (Y q) = b j) :
    (cov U X Y).tangentCoefficient b c p k = Γ i j k p := by
  classical
  have hc : ContinuousAt c.symm (c p) := c.continuousAt_symm (c.map_source hp)
  have hy := hc.eventually (by simpa only [c.left_inv hp] using hY)
  have hyc : Y.coordinateCoefficient b c k =ᶠ[𝓝 (c p)]
      fun _ ↦ b.repr (b j) k := by
    filter_upwards [hy] with z hz
    exact congrArg (fun v ↦ b.repr v k) hz
  have hd : fderiv ℝ (Y.coordinateCoefficient b c k) (c p) = 0 := by
    rw [hyc.fderiv_eq]
    exact fderiv_const_apply _
  rw [hΓ X Y p hp k, hd]
  simp only [LocalSmoothVectorField.tangentCoefficient, hX.self_of_nhds,
    hY.self_of_nhds, b.repr_self_apply, ite_mul, mul_ite, one_mul,
    zero_mul, mul_one, Finset.sum_ite_eq, Finset.mem_univ, ite_true,
    zero_apply, mul_zero, Finset.sum_const_zero, zero_add]

/-!
The extracted Christoffel coefficients are unique. This is the converse-facing part of Andrews Proposition 8.3.1: once the coordinate formula is fixed, the coefficient functions cannot depend on the auxiliary frame germs used to read them off.
-/ 

/-- Two Christoffel coordinate formulas for the same local operator have the same coefficients on the chart source. The coordinate-frame germs are supplied by the preceding bump-function construction, so no extension of arbitrary local fields or global frame is assumed. -/
theorem christoffel_symbols_unique
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M]
    (cov : LocalBilinearCovariantDerivative E M) (U : Opens M) {n : ℕ}
    (b : Basis (Fin n) ℝ E) (c : OpenPartialHomeomorph U E)
    (hc : c ∈ maximalAtlas 𝓘(ℝ, E) ∞ U)
    (Γ Δ : Fin n → Fin n → Fin n → U → ℝ)
    (hΓ : ∀ (X Y : LocalSmoothVectorField E M U) (p : U), p ∈ c.source → ∀ k,
      (cov U X Y).tangentCoefficient b c p k =
        (∑ i, X.tangentCoefficient b c p i *
          fderiv ℝ (Y.coordinateCoefficient b c k) (c p) (b i)) +
        ∑ i, ∑ j, X.tangentCoefficient b c p i *
          Y.tangentCoefficient b c p j * Γ i j k p)
    (hΔ : ∀ (X Y : LocalSmoothVectorField E M U) (p : U), p ∈ c.source → ∀ k,
      (cov U X Y).tangentCoefficient b c p k =
        (∑ i, X.tangentCoefficient b c p i *
          fderiv ℝ (Y.coordinateCoefficient b c k) (c p) (b i)) +
        ∑ i, ∑ j, X.tangentCoefficient b c p i *
          Y.tangentCoefficient b c p j * Δ i j k p) :
    ∀ i j k p, p ∈ c.source → Γ i j k p = Δ i j k p := by
  intro i j k p hp
  obtain ⟨X, hX⟩ := exists_coordinate_frame_germ c hc p hp (b i)
  obtain ⟨Y, hY⟩ := exists_coordinate_frame_germ c hc p hp (b j)
  have hΓijk := christoffel_coefficient_of_coordinate_germs
    cov U b c Γ hΓ p hp i j k X Y hX hY
  have hΔijk := christoffel_coefficient_of_coordinate_germs
    cov U b c Δ hΔ p hp i j k X Y hX hY
  exact hΓijk.symm.trans hΔijk

/-- Coordinate coefficients are additive in the local field argument. This is the finite-dimensional coordinate identity used when expanding a field in a local frame. -/
theorem LocalSmoothVectorField.coordinateCoefficient_add
    {U : Opens M} {n : ℕ} (b : Basis (Fin n) ℝ E)
    (c : OpenPartialHomeomorph U E)
    (X Y : LocalSmoothVectorField E M U) (k : Fin n) (z : E) :
    (X + Y).coordinateCoefficient b c k z =
      X.coordinateCoefficient b c k z + Y.coordinateCoefficient b c k z := by
  simp [LocalSmoothVectorField.coordinateCoefficient,
    LocalSmoothVectorField.tangentCoefficient, map_add]

/-- Chart coefficients distribute over finite sums of local fields. This is the finite-frame linearity used when expanding a field in the coordinate frame of Andrews, Proposition 8.3.1. -/
theorem LocalSmoothVectorField.coordinateCoefficient_finset_sum
    {U : Opens M} {n : ℕ} {ι : Type*} (b : Basis (Fin n) ℝ E)
    (c : OpenPartialHomeomorph U E)
    (s : Finset ι) (X : ι → LocalSmoothVectorField E M U)
    (k : Fin n) (z : E) :
    (s.sum X).coordinateCoefficient b c k z =
      s.sum (fun i => (X i).coordinateCoefficient b c k z) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp [LocalSmoothVectorField.coordinateCoefficient,
        LocalSmoothVectorField.tangentCoefficient]
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, LocalSmoothVectorField.coordinateCoefficient_add, ih]
      simp [Finset.sum_insert, ha]

/-- A finite smooth frame expansion distributes through chart coefficients. This is the finite-sum algebraic bridge used in the coordinate expansion in Andrews, Proposition 8.3.1: for smooth coefficients `f i`, the chart coefficient of `∑ i, f i • X i` is the corresponding finite sum of scalar coefficient products. -/
theorem LocalSmoothVectorField.coordinateCoefficient_finset_sum_mul
    {U : Opens M} {n r : ℕ} (b : Basis (Fin n) ℝ E)
    (c : OpenPartialHomeomorph U E)
    (X : Fin r → LocalSmoothVectorField E M U)
    (f : Fin r → U → ℝ)
    (hf : ∀ i, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ (f i))
    (k : Fin n) (z : E) :
    ((Finset.univ.sum (fun i => (X i).mulFunction (f i) (hf i))).coordinateCoefficient b c k z) =
      Finset.univ.sum (fun i => f i (c.symm z) * (X i).coordinateCoefficient b c k z) := by
  rw [LocalSmoothVectorField.coordinateCoefficient_finset_sum (s := Finset.univ)]
  simp_rw [LocalSmoothVectorField.coordinateCoefficient,
    LocalSmoothVectorField.tangentCoefficient_mulFunction]
/-- The local affine-connection laws are equivalent to the smooth Christoffel coordinate formula. Source: Andrews, Lecture 8, Definition 8.2.1, p.72, and Proposition 8.3.1, p.74. -/
 private def ambientOpenOfSubtypeX {M : Type*} [TopologicalSpace M]
    (U : Opens M) (V : Opens U) : Opens M :=
  ⟨Subtype.val '' (V : Set U), U.2.isOpenMap_subtype_val _ V.2⟩

omit [FiniteDimensional ℝ E] in
 private theorem test_transport_chart (U : Opens M) (S : Opens U) (hS : Nonempty S)
    (c : OpenPartialHomeomorph U E) (hcsrc : c.source = (S : Set U))
    (hc : c ∈ maximalAtlas 𝓘(ℝ, E) ∞ U) :
    ∃ O : Opens M, ∃ hOU : O ≤ U,
      ∃ e : OpenPartialHomeomorph O E, e.source = Set.univ ∧
      e ∈ maximalAtlas 𝓘(ℝ, E) ∞ O ∧
      (∀ x : O, Opens.inclusion hOU x ∈ c.source ∧ e x = c (Opens.inclusion hOU x)) ∧
      (∀ p : U, p ∈ c.source → ∃ x : O, Opens.inclusion hOU x = p) := by
  let O : Opens M := ambientOpenOfSubtypeX U S
  have hOU : O ≤ U := by
    intro x hx
    rcases hx with ⟨q, hq, rfl⟩
    exact q.property
  have hO : Nonempty O := by
    rcases hS with ⟨q⟩
    exact ⟨⟨q.val, ⟨q.val, q.property, rfl⟩⟩⟩
  let i : O → U := Opens.inclusion hOU
  let q : O → S := fun x => ⟨i x, by
    rcases x.property with ⟨r, hr, hrx⟩
    change i x ∈ (S : Set U)
    have hri : i x = r := Subtype.ext hrx.symm
    rw [hri]
    exact hr⟩
  have hi : Topology.IsOpenEmbedding i := TopologicalSpace.Opens.isOpenEmbedding_of_le hOU
  have hvalS : Topology.IsOpenEmbedding ((↑) : S → U) := S.2.isOpenEmbedding_subtypeVal
  have hqi : ((↑) : S → U) ∘ q = i := by
    funext x; rfl
  have hq : Topology.IsOpenEmbedding q := Topology.IsOpenEmbedding.of_comp q hvalS (by simpa [hqi] using hi)
  let d : OpenPartialHomeomorph S E := c.subtypeRestr hS
  have hdsource : d.source = Set.univ := by
    rw [OpenPartialHomeomorph.subtypeRestr_source, hcsrc]
    ext x
    simp
  have hdemb : Topology.IsOpenEmbedding d := d.isOpenEmbedding hdsource
  let φ : O → E := d ∘ q
  have hφ : Topology.IsOpenEmbedding φ := by
    simpa [φ] using hdemb.comp hq
  let e : OpenPartialHomeomorph O E := hφ.toOpenPartialHomeomorph φ
  have hisrc (x : O) : i x ∈ c.source := by
    rw [hcsrc]
    exact (q x).property
  have hef (x : O) : e x = c (i x) := rfl
  have heinv (z : E) (hz : z ∈ e.target) : i (e.symm z) = c.symm z := by
    have hczt : z ∈ c.target := by
      rw [← e.right_inv hz, hef]
      exact c.map_source (hisrc _)
    apply c.injOn (hisrc _) (c.map_target hczt)
    rw [← hef, e.right_inv hz, c.right_inv hczt]
  have he : e ∈ maximalAtlas 𝓘(ℝ, E) ∞ O := by
    apply e.mem_maximalAtlas_of_contMDiffOn
    · intro x hx
      exact ((contMDiffAt_of_mem_maximalAtlas hc (hisrc x)).comp x
        ((contMDiff_inclusion hOU).contMDiffAt)).contMDiffWithinAt
    · intro z hz
      have hczt : z ∈ c.target := by
        rw [← e.right_inv hz, hef]
        exact c.map_source (hisrc _)
      apply ((ContMDiffAt.subtypeVal_comp_iff O e.symm z).mp ?_).contMDiffWithinAt
      have hcs := (contMDiff_subtype_val (I := 𝓘(ℝ, E)) (U := U)).contMDiffAt.comp z
        (contMDiffAt_symm_of_mem_maximalAtlas hc hczt)
      apply hcs.congr_of_eventuallyEq
      filter_upwards [e.open_target.mem_nhds hz] with w hw
      exact congrArg Subtype.val (heinv w hw)
  refine ⟨O, hOU, e, by simp [e], he, fun x ↦ ⟨hisrc x, hef x⟩, ?_⟩
  intro p hp
  exact ⟨⟨p, ⟨p, hcsrc ▸ hp, rfl⟩⟩, rfl⟩

private theorem invertible_composition {E F G : Type*}
    [AddCommGroup E] [TopologicalSpace E] [Module ℝ E]
    [AddCommGroup F] [TopologicalSpace F] [Module ℝ F]
    [AddCommGroup G] [TopologicalSpace G] [Module ℝ G]
    {A : E →L[ℝ] F} {B : F →L[ℝ] G} {C : E →L[ℝ] G}
    (hB : B.IsInvertible) (hC : C.IsInvertible) (h : B ∘L A = C) : A.IsInvertible := by
  rcases hB with ⟨eB, rfl⟩
  rcases hC with ⟨eC, hC⟩
  have heq : (eB : F →L[ℝ] G) ∘L A = eC := h.trans hC.symm
  have hA : A = (eB.symm : G →L[ℝ] F) ∘L eC := by
    apply ContinuousLinearMap.ext
    intro v
    have hv := congrArg (fun L : E →L[ℝ] G ↦ (eB.symm : G →L[ℝ] F) (L v)) heq
    simpa using hv
  refine ⟨eC.trans eB.symm, ?_⟩
  rw [hA]
  rfl

theorem nested_open_inclusion_mfderiv_invertible
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] {U V : Opens M} (hVU : V ≤ U) (p : V) :
    (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (Opens.inclusion hVU) p).IsInvertible := by
  let incU : U → M := fun q ↦ q.1
  let incV : V → M := fun q ↦ q.1
  have hB := smooth_open_inclusion_mfderiv_invertible (E := E) (M := M) U
    (Opens.inclusion hVU p)
  have hC := smooth_open_inclusion_mfderiv_invertible (E := E) (M := M) V p
  have hg : MDiffAt (fun q : U ↦ (q : M)) (Opens.inclusion hVU p) :=
    (ContMDiff.contMDiffAt (x := Opens.inclusion hVU p)
      (contMDiff_subtype_val (I := 𝓘(ℝ, E)) (U := U) (n := ∞))).mdifferentiableAt
      (by simp : (∞ : ℕ∞ω) ≠ 0)
  have hf : MDiffAt (Opens.inclusion hVU) p :=
    (ContMDiff.contMDiffAt (x := p) (contMDiff_inclusion hVU)).mdifferentiableAt
      (by simp : (∞ : ℕ∞ω) ≠ 0)
  have hh := mfderiv_comp p hg hf
  refine invertible_composition hB hC ?_
  simpa [incU, incV, Function.comp_def] using hh.symm


private theorem isSmoothAffineConnectionOperator_forward (cov : LocalBilinearCovariantDerivative E M)
    (h : IsSmoothAffineConnectionOperator cov) : cov.HasSmoothChristoffelSymbols := by
  classical
  intro U n b c hc
  by_cases hs : c.source.Nonempty
  · let S : Opens U := ⟨c.source, c.open_source⟩
    have hS : Nonempty S := ⟨⟨hs.choose, hs.choose_spec⟩⟩
    obtain ⟨O, hOU, d, hdsrc, hd, hdc, hcover⟩ := test_transport_chart U S hS c rfl hc
    let inc : O → U := Opens.inclusion hOU
    have hOne : Nonempty O := by
      obtain ⟨q⟩ := hS
      obtain ⟨x, _⟩ := hcover q.1 q.2
      exact ⟨x⟩
    let : Nonempty O := hOne
    have hds (q : O) : q ∈ d.source := hdsrc ▸ Set.mem_univ q
    have hisrc (q : O) : inc q ∈ c.source := (hdc q).1
    have heq : (d : O → E) = c ∘ inc := funext fun q ↦ (hdc q).2
    have hdD : d.MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ, E) :=
      ⟨(contMDiffOn_of_mem_maximalAtlas hd).mdifferentiableOn (by simp),
        (contMDiffOn_symm_of_mem_maximalAtlas hd).mdifferentiableOn (by simp)⟩
    let W (i : Fin n) : LocalSmoothVectorField E M O :=
      ⟨VectorField.mpullback 𝓘(ℝ, E) 𝓘(ℝ, E) d (fun _ ↦ b i), by
        intro q
        have hcst : ContMDiffAt 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞
            (fun z : E ↦ (⟨z, b i⟩ : TangentBundle 𝓘(ℝ, E) E)) (d q) :=
          contMDiffAt_vectorSpace_iff_contDiffAt.mpr contDiffAt_const
        exact hcst.mpullback_vectorField_preimage
          (contMDiffAt_of_mem_maximalAtlas hd (hds q))
          ⟨hdD.mfderiv (hds q), rfl⟩ (by simp)⟩
    have hWcoord (i : Fin n) (q : O) : mvfderiv 𝓘(ℝ, E) d q (W i q) = b i :=
      (show (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) d q).IsInvertible from
        ⟨hdD.mfderiv (hds q), rfl⟩).self_apply_inverse (b i)
    have hExpansion (X : LocalSmoothVectorField E M O) :
        X = ∑ i, (W i).mulFunction (fun q ↦ X.tangentCoefficient b d q i)
          (fun q ↦ (X.contMDiffOn_tangentCoefficient b d hd i).contMDiffAt
            (d.open_source.mem_nhds (hds q))) := by
      ext q
      have hx := X.coordinate_frame_expansion b d hdD q (hds q) (fun i ↦ W i q)
        (fun i ↦ hWcoord i q)
      have hsumEval (s : Finset (Fin n)) (Z : Fin n → LocalSmoothVectorField E M O) :
          (∑ i ∈ s, Z i) q = ∑ i ∈ s, Z i q := by
        induction s using Finset.induction_on with
        | empty => rfl
        | @insert a s ha ih => simp only [Finset.sum_insert ha,
            ContMDiffSection.coe_add, Pi.add_apply, ih]
      rw [hsumEval]
      exact hx
    have hCoefficient (X : LocalSmoothVectorField E M O) (k : Fin n) :
        ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ (fun q ↦ X.tangentCoefficient b d q k) :=
      fun q ↦ (X.contMDiffOn_tangentCoefficient b d hd k).contMDiffAt
        (d.open_source.mem_nhds (hds q))
    have hRestrict (X : LocalSmoothVectorField E M U) :
        ∃ XO : LocalSmoothVectorField E M O, LocalSmoothVectorField.IsRestriction hOU X XO :=
      X.openRestriction hOU (nested_open_inclusion_mfderiv_invertible hOU)
    have hcoeffRestrict (X : LocalSmoothVectorField E M U)
        (XO : LocalSmoothVectorField E M O) (hX : LocalSmoothVectorField.IsRestriction hOU X XO)
        (q : O) (k : Fin n) : XO.tangentCoefficient b d q k = X.tangentCoefficient b c (inc q) k := by
      have hcD := (contMDiffAt_of_mem_maximalAtlas hc (hisrc q)).mdifferentiableAt (by simp)
      have hiD : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E) inc q :=
        ((contMDiff_inclusion (I := 𝓘(ℝ, E)) (n := ∞) hOU).contMDiffAt).mdifferentiableAt (by simp)
      have hh := mfderiv_comp q hcD hiD
      change b.repr (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) d q (XO q)) k =
        b.repr (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c (inc q) (X (inc q))) k
      rw [heq, hh]
      change b.repr (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c (inc q)
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) inc q (XO q))) k = _
      rw [hX q]
    have hi : Topology.IsOpenEmbedding inc :=
      TopologicalSpace.Opens.isOpenEmbedding_of_le hOU
    let ei : OpenPartialHomeomorph O U := hi.toOpenPartialHomeomorph inc
    let F (i j k : Fin n) : O → ℝ :=
      fun q ↦ (cov O (W i) (W j)).tangentCoefficient b d q k
    let Γ (i j k : Fin n) : U → ℝ := F i j k ∘ ei.symm
    have hF (i j k : Fin n) :
        ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ (F i j k) := by
      intro q
      have hq := (cov O (W i) (W j)).contMDiffOn_tangentCoefficient b d hd k q (hds q)
      exact hq.contMDiffAt (by rw [hdsrc]; exact Filter.univ_mem)
    have hΓsmooth (i j k : Fin n) :
        ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ) ∞ (Γ i j k) c.source := by
      intro p hp
      obtain ⟨q, hq⟩ := hcover p hp
      have hqrange : p ∈ Set.range inc := ⟨q, hq⟩
      have hvalAt : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) ∞
          (Subtype.val ∘ ei.symm) p := by
        apply (contMDiff_subtype_val (I := 𝓘(ℝ, E)) (U := U)).contMDiffAt.congr_of_eventuallyEq
        filter_upwards [hi.isOpen_range.mem_nhds hqrange] with r hr
        have hr' : r ∈ ei.target := by simpa [ei] using hr
        exact congrArg Subtype.val (ei.right_inv hr')
      have hiAt : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ (ei.symm) p :=
        (ContMDiffAt.subtypeVal_comp_iff O ei.symm p).mp hvalAt
      have hcomp := (hF i j k).contMDiffAt.comp p hiAt
      simpa [Γ] using hcomp.contMDiffWithinAt
    refine ⟨Γ, ?_, ?_⟩
    · intro i j k
      exact hΓsmooth i j k
    intro X Y p hp k
    obtain ⟨x, hx⟩ := hcover p hp
    obtain ⟨XO, hXO⟩ := hRestrict X
    obtain ⟨YO, hYO⟩ := hRestrict Y
    have hcoeffX (i : Fin n) :
        XO.tangentCoefficient b d x i = X.tangentCoefficient b c p i := by
      have hh := hcoeffRestrict X XO hXO x i
      have hincx : inc x = p := hx
      rw [hincx] at hh
      exact hh
    have hcoeffY (j : Fin n) :
        YO.tangentCoefficient b d x j = Y.tangentCoefficient b c p j := by
      have hh := hcoeffRestrict Y YO hYO x j
      have hincx : inc x = p := hx
      rw [hincx] at hh
      exact hh
    have hcovres := h.restriction hOU X Y XO YO hXO hYO
    have hcD := (contMDiffAt_of_mem_maximalAtlas hc (hisrc x)).mdifferentiableAt (by simp)
    have hiD : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E) inc x :=
      ((contMDiff_inclusion (I := 𝓘(ℝ, E)) (n := ∞) hOU).contMDiffAt).mdifferentiableAt
        (by simp)
    have hcomp := mfderiv_comp x hcD hiD
    have hΓeval (i j : Fin n) : Γ i j k p = F i j k x := by
      dsimp [Γ]
      have hincx : inc x = p := hx
      rw [← hincx]
      have hxs : x ∈ ei.source := by
        change x ∈ (Set.univ : Set O)
        exact Set.mem_univ x
      exact congrArg (F i j k) (ei.left_inv hxs)
    have hcovcoef :
        (cov O XO YO).tangentCoefficient b d x k =
          (cov U X Y).tangentCoefficient b c p k := by
      change b.repr (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) d x (cov O XO YO x)) k =
        b.repr (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c p (cov U X Y p)) k
      have hincx : inc x = p := hx
      rw [← hincx]
      have hdeq : (d : O → E) = c ∘ inc := heq
      rw [hdeq, hcomp]
      change b.repr (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c (inc x)
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) inc x (cov O XO YO x))) k = _
      rw [hcovres x]
    have hfin := covariantDerivative_finite_frame_expansion cov h
      (Finset.univ : Finset (Fin n)) (Finset.univ : Finset (Fin n)) W W
      (fun i q ↦ XO.tangentCoefficient b d q i)
      (fun j q ↦ YO.tangentCoefficient b d q j)
      (fun i ↦ hCoefficient XO i) (fun j ↦ hCoefficient YO j) x
    rw [← hExpansion XO, ← hExpansion YO] at hfin
    have hfincoef := congrArg
      (fun z : TangentSpace 𝓘(ℝ, E) x ↦ b.repr (mvfderiv 𝓘(ℝ, E) d x z) k) hfin
    dsimp only [F] at hΓeval hfincoef ⊢
    rw [← hcovcoef]
    change b.repr (mvfderiv 𝓘(ℝ, E) d x (cov O XO YO x)) k = _
    rw [hfincoef]
    simp [map_add, map_sum, map_smul, smul_eq_mul, Finset.sum_apply, Pi.smul_apply, LocalSmoothVectorField.tangentCoefficient]
    have hcoeffX' (i : Fin n) :
        b.repr (mvfderiv 𝓘(ℝ, E) d x (XO x)) i =
          b.repr (mvfderiv 𝓘(ℝ, E) c p (X p)) i := hcoeffX i
    have hcoeffY' (j : Fin n) :
        b.repr (mvfderiv 𝓘(ℝ, E) d x (YO x)) j =
          b.repr (mvfderiv 𝓘(ℝ, E) c p (Y p)) j := hcoeffY j
    have hW' (i j : Fin n) :
        b.repr (mvfderiv 𝓘(ℝ, E) d x (W i x)) j = b.repr (b i) j := by
      rw [hWcoord i x]
    have hcs : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ c.symm (c p) :=
      (contMDiffOn_symm_of_mem_maximalAtlas hc).contMDiffAt
        (c.open_target.mem_nhds (c.map_source hp))
    have hYc (j : Fin n) : DifferentiableAt ℝ (Y.coordinateCoefficient b c j) (c p) := by
      have hYcoeffAt := (Y.contMDiffOn_tangentCoefficient b c hc j).contMDiffAt
        (c.open_source.mem_nhds hp)
      have hcompY := hYcoeffAt.comp_of_eq hcs (c.left_inv hp)
      have heqY : Y.coordinateCoefficient b c j =ᶠ[𝓝 (c p)]
          (fun z ↦ Y.tangentCoefficient b c (c.symm z) j) := by
        filter_upwards [c.open_target.mem_nhds (c.map_source hp)] with z hz
        rfl
      have hcoord := hcompY.congr_of_eventuallyEq heqY.symm
      exact (contMDiffAt_iff_contDiffAt.mp hcoord).differentiableAt (by simp)
    have hcoeffEq (j : Fin n) :
        (fun q : O ↦ YO.tangentCoefficient b d q j) =
          (Y.coordinateCoefficient b c j) ∘ d := by
      funext q
      change b.repr (mvfderiv 𝓘(ℝ, E) d q (YO q)) j =
        b.repr (mvfderiv 𝓘(ℝ, E) c (c.symm (d q)) (Y (c.symm (d q)))) j
      have hdq : d q = c (inc q) := hdc q |>.2
      rw [hdq, c.left_inv (hisrc q)]
      exact hcoeffRestrict Y YO hYO q j
    have hderivY (i j : Fin n) :
        (mvfderiv 𝓘(ℝ, E) (fun q : O ↦ YO.tangentCoefficient b d q j) x) (W i x) =
          (fderiv ℝ (Y.coordinateCoefficient b c j) (c p)) (b i) := by
      have hdx : d x = c p := by
        rw [hdc x |>.2, hx]
      have hcompY := mvfderiv_comp_apply x
        (hdx ▸ (hYc j).mdifferentiableAt) (hdD.mdifferentiableAt (hds x)) (W i x)
      rw [← hcoeffEq j] at hcompY
      have hw := hWcoord i x
      change (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (d : O → E) x) (W i x) = b i at hw
      rw [hw] at hcompY
      convert hcompY using 1 ; simp only [mvfderiv_eq_fderiv, hdx] ; rfl
    have hderivY' (i j : Fin n) :
        ((mvfderiv 𝓘(ℝ, E) (fun q : O ↦
          (b.repr (mvfderiv 𝓘(ℝ, E) d q (YO q))) j) x) (W i x)) =
          (fderiv ℝ (Y.coordinateCoefficient b c j) (c p)) (b i) := hderivY i j
    have hΓeval' (i j : Fin n) :
        b.repr (mvfderiv 𝓘(ℝ, E) d x ((cov O (W i) (W j)) x)) k =
          Γ i j k p := (hΓeval i j).symm
    simp_rw [hcoeffX', hcoeffY', hW']
    simp_rw [hderivY']
    simp_rw [hΓeval']
    simp [Finsupp.single_apply]
    ac_rfl
  · refine ⟨fun _ _ _ _ ↦ 0, fun _ _ _ ↦ contMDiffOn_const, ?_⟩
    intro X Y p hp
    exact (hs ⟨p, hp⟩).elim

theorem isSmoothAffineConnectionOperator_iff_christoffel
    (cov : LocalBilinearCovariantDerivative E M) :
    IsSmoothAffineConnectionOperator cov ↔
      cov.RespectsRestriction ∧ cov.HasSmoothChristoffelSymbols := by
  classical
  constructor
  · intro h
    exact ⟨h.restriction, isSmoothAffineConnectionOperator_forward cov h⟩
  · rintro ⟨hr, hc⟩
    exact isSmoothAffineConnectionOperator_of_christoffel cov hr hc

/-- The coordinate formula in Andrews, Lecture 8, Proposition 8.3.1, p.74, depends only on the first field's value and the second field's germ. -/
theorem LocalBilinearCovariantDerivative.HasSmoothChristoffelSymbols.eval_eq_of_germ
    {cov : LocalBilinearCovariantDerivative E M} (hc : cov.HasSmoothChristoffelSymbols)
    {U : Opens M} (X X' Y Y' : LocalSmoothVectorField E M U) (p : U)
    (hX : X p = X' p) (hY : ∀ᶠ q in 𝓝 p, Y q = Y' q) :
    cov U X Y p = cov U X' Y' p := by
  let b := Module.finBasis ℝ E
  let c := chartAt E p
  have hp : p ∈ c.source := mem_chart_source E p
  obtain ⟨Γ, _, hΓ⟩ := hc U (Module.finrank ℝ E) b c
    (chart_mem_maximalAtlas p)
  have htend : Filter.Tendsto c.symm (𝓝 (c p)) (𝓝 p) := by
    simpa only [c.left_inv hp] using (c.continuousAt_symm (c.map_source hp)).tendsto
  have hYp : Y p = Y' p := hY.self_of_nhds (p := fun q : U ↦ Y q = Y' q)
  have hderiv : ∀ k, fderiv ℝ (Y.coordinateCoefficient b c k) (c p) =
      fderiv ℝ (Y'.coordinateCoefficient b c k) (c p) := by
    intro k
    apply Filter.EventuallyEq.fderiv_eq
    filter_upwards [htend.eventually hY] with z hz
    simp only [LocalSmoothVectorField.coordinateCoefficient,
      LocalSmoothVectorField.tangentCoefficient, hz]
  apply (mdifferentiable_chart (I := 𝓘(ℝ, E)) p).mfderiv_injective hp
  apply (NormedSpace.fromTangentSpace (c p)).injective
  apply b.repr.injective
  ext k
  change (cov U X Y).tangentCoefficient b c p k =
    (cov U X' Y').tangentCoefficient b c p k
  rw [hΓ X Y p hp k, hΓ X' Y' p hp k]
  simp only [hderiv, LocalSmoothVectorField.tangentCoefficient, hX, hYp]

/-- Evaluation depends only on the first field's value and the second field's germ at the point. Source: Andrews, Lecture 8, Proposition 8.3.1, p.74, and the local-germ clause of `geometry.andrews_smooth_affine_connection`. -/
theorem SmoothAffineConnection.eval_eq_of_value_eq_of_germ_eq
    (nabla : SmoothAffineConnection E M) {U : Opens M}
    (X X' Y Y' : LocalSmoothVectorField E M U) (p : U)
    (hX : X p = X' p) (hY : ∀ᶠ q in 𝓝 p, Y q = Y' q) :
    nabla.cov U X Y p = nabla.cov U X' Y' p := by
  have hc := ((isSmoothAffineConnectionOperator_iff_christoffel nabla.cov).mp nabla.laws).2
  exact hc.eval_eq_of_germ X X' Y Y' p hX hY


end

end HolomorphicAnosov

