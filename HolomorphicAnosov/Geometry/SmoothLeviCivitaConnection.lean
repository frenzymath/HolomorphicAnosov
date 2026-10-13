import HolomorphicAnosov.Geometry.SmoothAffineConnection
import HolomorphicAnosov.Geometry.SmoothAffineConnectionKoszul
import HolomorphicAnosov.Geometry.SmoothAffineConnectionUniqueness
import HolomorphicAnosov.Geometry.SmoothVectorFieldExtensionGerm
import HolomorphicAnosov.Geometry.CovariantDerivativeExtensionIndependence
import HolomorphicAnosov.Geometry.VectorFieldBracketGermNaturality
import HolomorphicAnosov.Geometry.SmoothMatrixInverseAt
import HolomorphicAnosov.Geometry.SmoothScalarExtensionGerm
import HolomorphicAnosov.Geometry.DirectionalDerivativeGermNaturality
import HolomorphicAnosov.Geometry.SmoothMetricKoszulCoefficient
import HolomorphicAnosov.Geometry.MetricFrameReconstruction
import HolomorphicAnosov.Geometry.SmoothOpenInclusionDifferentialInjective
import HolomorphicAnosov.Geometry.SmoothOpenInclusionDifferentialInvertible
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita
import Mathlib.Tactic.LinearCombination
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.Geometry.Manifold.BumpFunction
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Geometry.Manifold.Algebra.Structures

/-! This file develops the smooth Levi-Civita connection, its local coordinate coefficients, and the associated uniqueness and regularity statements (Andrews, Lectures 8 and 10). -/

open Bundle IsManifold Module TopologicalSpace
open scoped Manifold ContDiff Topology _root_.Topology Matrix

namespace HolomorphicAnosov

noncomputable section

/-- The metric pulled back along a smooth map has smooth scalar coefficients in local coordinates (Andrews, Lecture 10, p. 98). -/
private lemma smooth_metric_pullback_entry
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    (g : ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E (TangentSpace 𝓘(ℝ, E) : M → Type _))
    {s : Set E} (hs : IsOpen s) (ψ : E → M)
    (hψ : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ ψ s) (v w : E) :
    ContDiffOn ℝ ∞ (fun z ↦ g.inner (ψ z)
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) ψ z v)
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) ψ z w)) s := by
  have hv (a : E) : ContMDiffOn 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞
      (fun z ↦ (⟨ψ z, mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) ψ z a⟩ :
        TangentBundle 𝓘(ℝ, E) M)) s := by
    have ha : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞
        (fun z : E ↦ (⟨z, a⟩ : TangentBundle 𝓘(ℝ, E) E)) := by
      intro z
      exact contMDiffAt_vectorSpace_iff_contDiffAt.mpr contDiffAt_const
    have ht := hψ.contMDiffOn_tangentMapWithin (m := ∞) (by simp)
      hs.uniqueMDiffOn
    have hc := ht.comp ha.contMDiffOn (fun z hz ↦ hz)
    apply hc.congr
    intro z hz
    simp only [tangentMapWithin, Function.comp_apply]
    rw [mfderivWithin_of_mem_nhds (hs.mem_nhds hz)]
  rw [← contMDiffOn_iff_contDiffOn]
  have h := (g.contMDiff.comp_contMDiffOn hψ).clm_bundle_apply₂
    (F₃ := ℝ) (E₃ := Bundle.Trivial M ℝ) (hv v) (hv w)
  intro z hz
  simpa using (contMDiffWithinAt_totalSpace.mp (h z hz)).2

set_option backward.isDefEq.respectTransparency false in
/-- The metric matrix induced by an injective differential has nonzero determinant. -/
private lemma smooth_metric_pullback_det_ne_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    (g : ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E (TangentSpace 𝓘(ℝ, E) : M → Type _))
    (ψ : E → M) (z : E) (hd : Function.Injective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) ψ z))
    {n : ℕ} (b : Basis (Fin n) ℝ E) :
    Matrix.det (fun i j ↦ g.inner (ψ z) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) ψ z (b i))
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) ψ z (b j))) ≠ 0 := by
  let d : E →L[ℝ] TangentSpace 𝓘(ℝ, E) (ψ z) := mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) ψ z
  let B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ := LinearMap.mk₂ ℝ
    (fun v w ↦ g.inner (ψ z) (d v) (d w))
    (by intros; simp) (by intros; simp) (by intros; simp) (by intros; simp)
  have hB : B.SeparatingLeft := by
    intro v hv
    by_contra hv0
    have hpos := g.pos (ψ z) (d v) (fun h ↦ hv0 (hd (h.trans (map_zero d).symm)))
    exact (ne_of_gt hpos) (hv v)
  have hmatrix : LinearMap.toMatrix₂ b b B =
      fun i j ↦ g.inner (ψ z) (d (b i)) (d (b j)) := by
    ext i j
    rw [LinearMap.toMatrix₂_apply]
    rfl
  have hnonzero := (LinearMap.separatingLeft_iff_det_ne_zero b).mp hB
  rw [hmatrix] at hnonzero
  convert hnonzero using 1

/-- The inverse-chart metric coefficients satisfy the smooth Christoffel formula on the chart source and target (Andrews, Lecture 10, p. 98). -/
private lemma smooth_metric_chart_coefficients
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    (g : ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E (TangentSpace 𝓘(ℝ, E) : M → Type _))
    (U : Opens M) (n : ℕ) (b : Basis (Fin n) ℝ E) (c : OpenPartialHomeomorph U E)
    (hc : c ∈ maximalAtlas 𝓘(ℝ, E) ∞ U) :
    let ψ : E → M := fun z ↦ (c.symm z : M)
    let G : E → Matrix (Fin n) (Fin n) ℝ := fun z i j ↦ g.inner (ψ z)
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) ψ z (b i))
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) ψ z (b j))
    ∃ Γ : Fin n → Fin n → Fin n → U → ℝ,
      (∀ i j k, ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ) ∞ (Γ i j k) c.source) ∧
      (∀ i j k, ContDiffOn ℝ ∞ (fun z ↦ Γ i j k (c.symm z)) c.target) ∧
      ∀ (p : U), p ∈ c.source → ∀ i j k,
        Γ i j k p = (1 / 2 : ℝ) * ∑ l : Fin n, ((G (c p))⁻¹) k l *
          (fderiv ℝ (fun z ↦ G z j l) (c p) (b i) +
            fderiv ℝ (fun z ↦ G z i l) (c p) (b j) -
            fderiv ℝ (fun z ↦ G z i j) (c p) (b l)) := by
  let ψ : E → M := fun z ↦ (c.symm z : M)
  let G : E → Matrix (Fin n) (Fin n) ℝ := fun z i j ↦ g.inner (ψ z)
    (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) ψ z (b i))
    (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) ψ z (b j))
  have hs := contMDiffOn_symm_of_mem_maximalAtlas hc
  have hψ : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ ψ c.target :=
    contMDiff_subtype_val.comp_contMDiffOn hs
  have hG (i j : Fin n) : ContDiffOn ℝ ∞ (fun z ↦ G z i j) c.target :=
    smooth_metric_pullback_entry g c.open_target ψ hψ (b i) (b j)
  have hdet (z : E) (hz : z ∈ c.target) : (G z).det ≠ 0 := by
    apply smooth_metric_pullback_det_ne_zero g ψ z _ b
    have hcs := contMDiffAt_symm_of_mem_maximalAtlas hc hz
    have hi := contMDiff_subtype_val (I := 𝓘(ℝ, E)) (U := U) (n := ∞) (c.symm z)
    have hcDiff : c.MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ, E) :=
      ⟨(contMDiffOn_of_mem_maximalAtlas hc).mdifferentiableOn (by simp),
        hs.mdifferentiableOn (by simp)⟩
    change Function.Injective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (Subtype.val ∘ c.symm) z)
    rw [mfderiv_comp z (hi.mdifferentiableAt (by simp))
      (hcs.mdifferentiableAt (by simp))]
    exact (smooth_open_inclusion_mfderiv_injective U (c.symm z)).comp
      (hcDiff.symm.mfderiv_injective hz)
  let F (i j k : Fin n) (z : E) := (1 / 2 : ℝ) * ∑ l : Fin n,
    ((G z)⁻¹) k l * (fderiv ℝ (fun z ↦ G z j l) z (b i) +
      fderiv ℝ (fun z ↦ G z i l) z (b j) - fderiv ℝ (fun z ↦ G z i j) z (b l))
  have hF (i j k : Fin n) : ContDiffOn ℝ ∞ (F i j k) c.target :=
    smooth_metric_koszul_coefficient c.open_target G hG hdet b i j k
  refine ⟨fun i j k p ↦ F i j k (c p), ?_, ?_, fun _ _ _ _ _ ↦ rfl⟩
  · intro i j k
    exact (hF i j k).contMDiffOn.comp (contMDiffOn_of_mem_maximalAtlas hc) c.mapsTo
  · intro i j k
    apply (hF i j k).congr
    intro z hz
    exact congrArg (F i j k) (c.right_inv hz)

/-- Differentiating a smooth scalar function along a smooth tangent section is smooth (Andrews, Lecture 8, §8.3). -/
private lemma smooth_directional_derivative
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    (f : M → ℝ) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ f)
    (X : ∀ p : M, TangentSpace 𝓘(ℝ, E) p)
    (hX : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞
      (fun p ↦ (⟨p, X p⟩ : TangentBundle 𝓘(ℝ, E) M))) :
    ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ (fun p ↦ mvfderiv 𝓘(ℝ, E) f p (X p)) := by
  have h := (hf.contMDiff_tangentMap (m := ∞) (by simp)).comp hX
  exact (contMDiff_snd_tangentBundle_modelSpace ℝ 𝓘(ℝ)).comp h

/-- The scalar pairings in the Koszul formula for the native Levi-Civita connection are smooth (Andrews, Lecture 10, p. 97). -/
private lemma native_leviCivita_inner_smooth
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    [RiemannianBundle (TangentSpace 𝓘(ℝ, E) : M → Type _)]
    [IsContMDiffRiemannianBundle 𝓘(ℝ, E) ∞ E (TangentSpace 𝓘(ℝ, E) : M → Type _)]
    (X Y Z : ∀ p : M, TangentSpace 𝓘(ℝ, E) p)
    (hX : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞
      (fun p ↦ (⟨p, X p⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (hY : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞
      (fun p ↦ (⟨p, Y p⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (hZ : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞
      (fun p ↦ (⟨p, Z p⟩ : TangentBundle 𝓘(ℝ, E) M))) :
    ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ (fun p ↦ inner ℝ
      (CovariantDerivative.leviCivitaConnection 𝓘(ℝ, E) M Y p (X p)) (Z p)) := by
  let : IsManifold 𝓘(ℝ, E) (minSmoothness ℝ 2) M :=
    IsManifold.of_le (n := ∞) (by simp)
  let : IsManifold 𝓘(ℝ, E) ((⊤ : ℕ∞) + 1) M :=
    IsManifold.of_le (n := ∞) (by simp)
  have hb (V W : ∀ p : M, TangentSpace 𝓘(ℝ, E) p)
      (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞ (fun p ↦
        (⟨p, V p⟩ : TangentBundle 𝓘(ℝ, E) M)))
      (hW : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞ (fun p ↦
        (⟨p, W p⟩ : TangentBundle 𝓘(ℝ, E) M))) :
      ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞ (fun p ↦
        (⟨p, VectorField.mlieBracket 𝓘(ℝ, E) V W p⟩ : TangentBundle 𝓘(ℝ, E) M)) := by
    intro p
    exact (hV p).mlieBracket_vectorField (hW p) (by simp)
  have hp (V W : ∀ p : M, TangentSpace 𝓘(ℝ, E) p)
      (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞
        (fun p ↦ (⟨p, V p⟩ : TangentBundle 𝓘(ℝ, E) M)))
      (hW : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞
        (fun p ↦ (⟨p, W p⟩ : TangentBundle 𝓘(ℝ, E) M))) :
      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ (fun p ↦ inner ℝ (V p) (W p)) :=
    ContMDiff.inner_bundle (F := E) (E := TangentSpace 𝓘(ℝ, E)) hV hW
  have hd₁ := smooth_directional_derivative _ (hp Y Z hY hZ) X hX
  have hd₂ := smooth_directional_derivative _ (hp Z X hZ hX) Y hY
  have hd₃ := smooth_directional_derivative _ (hp X Y hX hY) Z hZ
  have hk := (((((hd₁.add hd₂).sub hd₃).sub (hp Y _ hY (hb X Z hX hZ))).sub
    (hp Z _ hZ (hb Y X hY hX))).add (hp X _ hX (hb Z Y hZ hY)))
  have hscale := (((1 / 2 : ℝ) • ContinuousLinearMap.id ℝ ℝ).contDiff
    (n := ∞)).contMDiff.comp hk
  apply hscale.congr
  intro p
  simpa only [Function.comp_apply, Pi.smul_apply, Pi.add_apply, Pi.sub_apply,
    smul_eq_mul, div_eq_mul_inv, smul_apply, ContinuousLinearMap.id_apply, one_mul,
    one_div, mul_comm] using
    (CovariantDerivative.leviCivitaConnection_apply_inner 𝓘(ℝ, E)
    ((hX p).mdifferentiableAt (by simp)) ((hY p).mdifferentiableAt (by simp))
    ((hZ p).mdifferentiableAt (by simp)))

/-- Pairings with a finite smooth frame determine a tangent section uniquely. -/
private lemma smooth_tangent_section_of_pairings
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M]
    [RiemannianBundle (TangentSpace 𝓘(ℝ, E) : M → Type _)]
    [IsContMDiffRiemannianBundle 𝓘(ℝ, E) ∞ E (TangentSpace 𝓘(ℝ, E) : M → Type _)]
    {n : ℕ} (V : ∀ p : M, TangentSpace 𝓘(ℝ, E) p)
    (hV : ∀ Z : ContMDiffSection 𝓘(ℝ, E) E ∞ (TangentSpace 𝓘(ℝ, E) : M → Type _),
      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ (fun p ↦ inner ℝ (Z p) (V p)))
    (p : M) (b : Basis (Fin n) ℝ (TangentSpace 𝓘(ℝ, E) p))
    (hcard : ∀ q : M, Module.finrank ℝ (TangentSpace 𝓘(ℝ, E) q) = n)
    (Z : Fin n → ContMDiffSection 𝓘(ℝ, E) E ∞ (TangentSpace 𝓘(ℝ, E) : M → Type _))
    (hZ : ∀ i, Z i p = b i) :
    ContMDiffAt 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞
      (fun q ↦ (⟨q, V q⟩ : TangentBundle 𝓘(ℝ, E) M)) p := by
  classical
  let G : M → Matrix (Fin n) (Fin n) ℝ :=
    fun q ↦ Matrix.gram ℝ (fun i ↦ Z i q)
  have hG (i j) : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ) ∞ (fun q ↦ G q i j) p := by
    have hi : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞
        (fun q ↦ (⟨q, Z i q⟩ : TangentBundle 𝓘(ℝ, E) M)) := (Z i).contMDiff
    have hj : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞
        (fun q ↦ (⟨q, Z j q⟩ : TangentBundle 𝓘(ℝ, E) M)) := (Z j).contMDiff
    have hp (V W : ∀ q : M, TangentSpace 𝓘(ℝ, E) q)
        (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞
          (fun q ↦ (⟨q, V q⟩ : TangentBundle 𝓘(ℝ, E) M)))
        (hW : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞
          (fun q ↦ (⟨q, W q⟩ : TangentBundle 𝓘(ℝ, E) M))) :
        ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ (fun q ↦ inner ℝ (V q) (W q)) :=
      ContMDiff.inner_bundle (F := E) (E := TangentSpace 𝓘(ℝ, E)) hV hW
    exact (hp (fun q ↦ Z i q) (fun q ↦ Z j q) hi hj) p
  have hGp : G p = Matrix.gram ℝ b := by
    ext i j
    simp only [G, Matrix.gram_apply]
    rw [hZ i, hZ j]
  have hdet : (G p).det ≠ 0 := by
    rw [hGp]
    exact (Matrix.det_gram_ne_zero_iff_linearIndependent (𝕜 := ℝ)).mpr b.linearIndependent
  have hdSmooth : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ) ∞ (fun q ↦ (G q).det) p := by
    simp only [Matrix.det_apply']
    refine ContMDiffAt.sum fun σ _ ↦ contMDiffAt_const.mul ?_
    exact ContMDiffAt.prod fun i _ ↦ hG (σ i) i
  have hdNear : ∀ᶠ q in 𝓝 p, (G q).det ≠ 0 := hdSmooth.continuousAt.eventually_ne hdet
  let a : Fin n → M → ℝ := fun i q ↦
    ((G q)⁻¹ *ᵥ (fun j ↦ inner ℝ (Z j q) (V q))) i
  have ha (i) : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ) ∞ (a i) p := by
    change ContMDiffAt _ _ _ (fun q ↦ ∑ j, ((G q)⁻¹) i j *
      inner ℝ (Z j q) (V q)) p
    exact ContMDiffAt.sum fun j _ ↦
      (manifold_matrix_inverse_entry_smoothAt G p hG hdet i j).mul ((hV (Z j)) p)
  have hs : ContMDiffAt 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞
      (fun q ↦ (⟨q, ∑ i, a i q • Z i q⟩ : TangentBundle 𝓘(ℝ, E) M)) p :=
    ContMDiffAt.sum_section fun i _ ↦ (ha i).smul_section ((Z i).contMDiff p)
  apply hs.congr_of_eventuallyEq
  filter_upwards [hdNear] with q hq
  have hlin : LinearIndependent ℝ (fun i ↦ Z i q) :=
    Matrix.linearIndependent_of_det_gram_ne_zero hq
  let bq := basisOfLinearIndependentOfCardEqFinrank' (fun i ↦ Z i q) hlin
    (by simp [hcard q])
  have hbq : ⇑bq = fun i ↦ Z i q := coe_basisOfLinearIndependentOfCardEqFinrank' _ _ _
  have heq := metric_frame_reconstruction bq (V q)
  simp only [hbq] at heq
  exact congrArg (fun v ↦ (⟨q, v⟩ : TangentBundle 𝓘(ℝ, E) M)) heq.symm

/-- The native Levi-Civita operator sends smooth tangent sections to a smooth tangent section (Andrews, Prop. 10.3.1). -/
private lemma native_leviCivita_section_smooth
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M]
    [RiemannianBundle (TangentSpace 𝓘(ℝ, E) : M → Type _)]
    [IsContMDiffRiemannianBundle 𝓘(ℝ, E) ∞ E (TangentSpace 𝓘(ℝ, E) : M → Type _)]
    (X Y : ContMDiffSection 𝓘(ℝ, E) E ∞ (TangentSpace 𝓘(ℝ, E) : M → Type _)) :
    ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞
      (fun p ↦ (⟨p, CovariantDerivative.leviCivitaConnection 𝓘(ℝ, E) M
        (fun q ↦ Y q) p (X p)⟩ : TangentBundle 𝓘(ℝ, E) M)) := by
  classical
  intro p
  let b := Module.finBasis ℝ (TangentSpace 𝓘(ℝ, E) p)
  choose Z hZ using fun i ↦ exists_smooth_vectorField_value p (b i)
  apply smooth_tangent_section_of_pairings _ _ p b (fun q ↦ rfl) Z hZ
  intro W
  have h := native_leviCivita_inner_smooth (fun q ↦ X q) (fun q ↦ Y q)
    (fun q ↦ W q) X.contMDiff Y.contMDiff W.contMDiff
  apply h.congr
  intro q
  exact real_inner_comm _ _

/-- Native Levi-Civita differentiation of local fields is a smooth local section and agrees with ambient differentiation of germ extensions (Andrews, Lectures 8 and 10). -/
private lemma native_leviCivita_local_section
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M]
    [RiemannianBundle (TangentSpace 𝓘(ℝ, E) : M → Type _)]
    [IsContMDiffRiemannianBundle 𝓘(ℝ, E) ∞ E (TangentSpace 𝓘(ℝ, E) : M → Type _)]
    (U : Opens M) (X Y : LocalSmoothVectorField E M U) :
    ∃ V : LocalSmoothVectorField E M U,
      ∀ (p : U) (AX AY : ContMDiffSection 𝓘(ℝ, E) E ∞
        (TangentSpace 𝓘(ℝ, E) : M → Type _)),
      (∀ᶠ q in 𝓝 p, AX q.1 = mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E)
        (fun r : U ↦ (r : M)) q (X q)) →
      (∀ᶠ q in 𝓝 p, AY q.1 = mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E)
        (fun r : U ↦ (r : M)) q (Y q)) →
      mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (fun r : U ↦ (r : M)) p (V p) =
        CovariantDerivative.leviCivitaConnection 𝓘(ℝ, E) M
          (fun q ↦ AY q) p.1 (AX p.1) := by
  classical
  let cov := CovariantDerivative.leviCivitaConnection 𝓘(ℝ, E) M
  let incl : U → M := Subtype.val
  let d := mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) incl
  choose ZX hZX using fun p : U ↦ exists_smooth_vectorField_extension_germ U p X
  choose ZY hZY using fun p : U ↦ exists_smooth_vectorField_extension_germ U p Y
  let V := fun p : U ↦ (d p).inverse (cov (fun q ↦ ZY p q) p.1 (ZX p p.1))
  have hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞
      (fun p ↦ (⟨p, V p⟩ : TangentBundle 𝓘(ℝ, E) U)) := by
    intro p
    have hglob := native_leviCivita_section_smooth (ZX p) (ZY p)
    have hs := (hglob p.1).mpullback_vectorField_preimage
      (contMDiff_subtype_val (I := 𝓘(ℝ, E)) (U := U) (n := ∞) p)
        (smooth_open_inclusion_mfderiv_invertible U p) (by simp)
    apply hs.congr_of_eventuallyEq
    filter_upwards [(hZX p).eventually_nhds, (hZY p).eventually_nhds] with q hx hy
    have hc := covariantDerivative_extension_independent cov U q
      (ZX q) (ZX p) (ZY q) (ZY p)
      (by filter_upwards [hZX q, hx] with r hr hr'; exact hr.trans hr'.symm)
      (by filter_upwards [hZY q, hy] with r hr hr'; exact hr.trans hr'.symm)
    exact congrArg (fun v ↦ (⟨q, (d q).inverse v⟩ : TangentBundle 𝓘(ℝ, E) U)) hc
  refine ⟨⟨V, hV⟩, ?_⟩
  intro p AX AY hAX hAY
  change d p ((d p).inverse _) = _
  rw [(smooth_open_inclusion_mfderiv_invertible U p).self_apply_inverse]
  exact covariantDerivative_extension_independent cov U p
    (ZX p) AX (ZY p) AY
    (by filter_upwards [hZX p, hAX] with q hq hq'; exact hq.trans hq'.symm)
    (by filter_upwards [hZY p, hAY] with q hq hq'; exact hq.trans hq'.symm)

/-- The native connection induces bilinear smooth local operators satisfying the inclusion transport law (Andrews, Definition 8.2.1). -/
private lemma native_leviCivita_all_open_operator
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M]
    [RiemannianBundle (TangentSpace 𝓘(ℝ, E) : M → Type _)]
    [IsContMDiffRiemannianBundle 𝓘(ℝ, E) ∞ E (TangentSpace 𝓘(ℝ, E) : M → Type _)] :
    ∃ B : LocalBilinearCovariantDerivative E M,
      ∀ (U : Opens M) (X Y : LocalSmoothVectorField E M U)
      (p : U) (AX AY : ContMDiffSection 𝓘(ℝ, E) E ∞
        (TangentSpace 𝓘(ℝ, E) : M → Type _)),
      (∀ᶠ q in 𝓝 p, AX q.1 = mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E)
        (fun r : U ↦ (r : M)) q (X q)) →
      (∀ᶠ q in 𝓝 p, AY q.1 = mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E)
        (fun r : U ↦ (r : M)) q (Y q)) →
      mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (fun r : U ↦ (r : M)) p (B U X Y p) =
        CovariantDerivative.leviCivitaConnection 𝓘(ℝ, E) M
          (fun q ↦ AY q) p.1 (AX p.1) := by
  classical
  choose V hV using fun (U : Opens M) (X Y : LocalSmoothVectorField E M U) ↦
    native_leviCivita_local_section U X Y
  let cov := CovariantDerivative.leviCivitaConnection 𝓘(ℝ, E) M
  have ha (U : Opens M) (X X' Y : LocalSmoothVectorField E M U) :
      V U (X + X') Y = V U X Y + V U X' Y := by
    apply ContMDiffSection.ext
    intro p
    obtain ⟨AX, hAX⟩ := exists_smooth_vectorField_extension_germ U p X
    obtain ⟨AX', hAX'⟩ := exists_smooth_vectorField_extension_germ U p X'
    obtain ⟨AY, hAY⟩ := exists_smooth_vectorField_extension_germ U p Y
    have hsum : ∀ᶠ q in 𝓝 p, (AX + AX') q.1 =
        mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (fun r : U ↦ (r : M)) q ((X + X') q) := by
      filter_upwards [hAX, hAX'] with q hq hq'
      change AX q.1 + AX' q.1 = _
      rw [hq, hq']
      exact (map_add _ _ _).symm
    apply smooth_open_inclusion_mfderiv_injective U p
    change _ = mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (fun r : U ↦ (r : M)) p
      (V U X Y p + V U X' Y p)
    rw [map_add, hV U (X + X') Y p (AX + AX') AY hsum hAY,
      hV U X Y p AX AY hAX hAY, hV U X' Y p AX' AY hAX' hAY]
    exact map_add _ _ _
  have hs (U : Opens M) (a : ℝ) (X Y : LocalSmoothVectorField E M U) :
      V U (a • X) Y = a • V U X Y := by
    apply ContMDiffSection.ext
    intro p
    obtain ⟨AX, hAX⟩ := exists_smooth_vectorField_extension_germ U p X
    obtain ⟨AY, hAY⟩ := exists_smooth_vectorField_extension_germ U p Y
    have hsmul : ∀ᶠ q in 𝓝 p, (a • AX) q.1 =
        mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (fun r : U ↦ (r : M)) q ((a • X) q) := by
      filter_upwards [hAX] with q hq
      change a • AX q.1 = _
      rw [hq]
      exact (map_smul _ _ _).symm
    apply smooth_open_inclusion_mfderiv_injective U p
    change _ = mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (fun r : U ↦ (r : M)) p
      (a • V U X Y p)
    rw [map_smul, hV U (a • X) Y p (a • AX) AY hsmul hAY,
      hV U X Y p AX AY hAX hAY]
    exact map_smul _ _ _
  have ha' (U : Opens M) (X Y Y' : LocalSmoothVectorField E M U) :
      V U X (Y + Y') = V U X Y + V U X Y' := by
    apply ContMDiffSection.ext
    intro p
    obtain ⟨AX, hAX⟩ := exists_smooth_vectorField_extension_germ U p X
    obtain ⟨AY, hAY⟩ := exists_smooth_vectorField_extension_germ U p Y
    obtain ⟨AY', hAY'⟩ := exists_smooth_vectorField_extension_germ U p Y'
    have hsum : ∀ᶠ q in 𝓝 p, (AY + AY') q.1 =
        mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (fun r : U ↦ (r : M)) q ((Y + Y') q) := by
      filter_upwards [hAY, hAY'] with q hq hq'
      change AY q.1 + AY' q.1 = _
      rw [hq, hq']
      exact (map_add _ _ _).symm
    apply smooth_open_inclusion_mfderiv_injective U p
    change _ = mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (fun r : U ↦ (r : M)) p
      (V U X Y p + V U X Y' p)
    rw [map_add, hV U X (Y + Y') p AX (AY + AY') hAX hsum,
      hV U X Y p AX AY hAX hAY, hV U X Y' p AX AY' hAX hAY']
    exact congrArg (fun d ↦ d (AX p.1)) (cov.isCovariantDerivativeOnUniv.add
      ((AY.contMDiff p.1).mdifferentiableAt (by simp))
      ((AY'.contMDiff p.1).mdifferentiableAt (by simp)))
  have hs' (U : Opens M) (a : ℝ) (X Y : LocalSmoothVectorField E M U) :
      V U X (a • Y) = a • V U X Y := by
    apply ContMDiffSection.ext
    intro p
    obtain ⟨AX, hAX⟩ := exists_smooth_vectorField_extension_germ U p X
    obtain ⟨AY, hAY⟩ := exists_smooth_vectorField_extension_germ U p Y
    have hsmul : ∀ᶠ q in 𝓝 p, (a • AY) q.1 =
        mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (fun r : U ↦ (r : M)) q ((a • Y) q) := by
      filter_upwards [hAY] with q hq
      change a • AY q.1 = _
      rw [hq]
      exact (map_smul _ _ _).symm
    apply smooth_open_inclusion_mfderiv_injective U p
    change _ = mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (fun r : U ↦ (r : M)) p
      (a • V U X Y p)
    rw [map_smul, hV U X (a • Y) p AX (a • AY) hAX hsmul,
      hV U X Y p AX AY hAX hAY]
    exact congrArg (fun d ↦ d (AX p.1)) (cov.isCovariantDerivativeOnUniv.smul_const a
      ((AY.contMDiff p.1).mdifferentiableAt (by simp)))
  exact ⟨fun U ↦ LinearMap.mk₂ ℝ (V U) (ha U) (hs U) (ha' U) (hs' U), hV⟩

/-- The induced local operator commutes with restriction to smaller open subsets (Andrews, Definition 8.2.1). -/
private lemma native_leviCivita_operator_restriction
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M]
    [RiemannianBundle (TangentSpace 𝓘(ℝ, E) : M → Type _)]
    [IsContMDiffRiemannianBundle 𝓘(ℝ, E) ∞ E (TangentSpace 𝓘(ℝ, E) : M → Type _)]
    (B : LocalBilinearCovariantDerivative E M)
    (hB : ∀ (U : Opens M) (X Y : LocalSmoothVectorField E M U)
      (p : U) (AX AY : ContMDiffSection 𝓘(ℝ, E) E ∞
        (TangentSpace 𝓘(ℝ, E) : M → Type _)),
      (∀ᶠ q in 𝓝 p, AX q.1 = mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E)
        (fun r : U ↦ (r : M)) q (X q)) →
      (∀ᶠ q in 𝓝 p, AY q.1 = mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E)
        (fun r : U ↦ (r : M)) q (Y q)) →
      mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (fun r : U ↦ (r : M)) p (B U X Y p) =
        CovariantDerivative.leviCivitaConnection 𝓘(ℝ, E) M
          (fun q ↦ AY q) p.1 (AX p.1)) : B.RespectsRestriction := by
  intro U V hVU XU YU XV YV hX hY p
  let inc := Opens.inclusion hVU
  have hc (q : V) : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (fun r : V ↦ (r : M)) q =
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (fun r : U ↦ (r : M)) (inc q)).comp
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) inc q) := by
    exact mfderiv_comp q
      ((contMDiff_subtype_val (I := 𝓘(ℝ, E)) (U := U) (n := ∞) (inc q)).mdifferentiableAt
        (by simp))
      ((contMDiff_inclusion (I := 𝓘(ℝ, E)) (n := ∞) hVU q).mdifferentiableAt
        (by simp))
  obtain ⟨AX, hAX⟩ := exists_smooth_vectorField_extension_germ U (inc p) XU
  obtain ⟨AY, hAY⟩ := exists_smooth_vectorField_extension_germ U (inc p) YU
  have hAXV : ∀ᶠ q in 𝓝 p, AX q.1 =
      mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (fun r : V ↦ (r : M)) q (XV q) := by
    have hx := (contMDiff_inclusion (I := 𝓘(ℝ, E)) (n := ∞) hVU p).continuousAt
      |>.eventually hAX
    filter_upwards [hx] with q hq
    rw [hc, ContinuousLinearMap.comp_apply, hX q]
    exact hq
  have hAYV : ∀ᶠ q in 𝓝 p, AY q.1 =
      mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (fun r : V ↦ (r : M)) q (YV q) := by
    have hy := (contMDiff_inclusion (I := 𝓘(ℝ, E)) (n := ∞) hVU p).continuousAt
      |>.eventually hAY
    filter_upwards [hy] with q hq
    rw [hc, ContinuousLinearMap.comp_apply, hY q]
    exact hq
  apply smooth_open_inclusion_mfderiv_injective U (inc p)
  rw [← ContinuousLinearMap.comp_apply, ← hc,
    hB V XV YV p AX AY hAXV hAYV, hB U XU YU (inc p) AX AY hAX hAY]

/-- The induced local Levi-Civita operator is torsion-free (Andrews, Prop. 10.3.1). -/
private lemma native_leviCivita_operator_torsion
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M]
    [RiemannianBundle (TangentSpace 𝓘(ℝ, E) : M → Type _)]
    [IsContMDiffRiemannianBundle 𝓘(ℝ, E) ∞ E (TangentSpace 𝓘(ℝ, E) : M → Type _)]
    (B : LocalBilinearCovariantDerivative E M)
    (hB : ∀ (U : Opens M) (X Y : LocalSmoothVectorField E M U)
      (p : U) (AX AY : ContMDiffSection 𝓘(ℝ, E) E ∞
        (TangentSpace 𝓘(ℝ, E) : M → Type _)),
      (∀ᶠ q in 𝓝 p, AX q.1 = mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E)
        (fun r : U ↦ (r : M)) q (X q)) →
      (∀ᶠ q in 𝓝 p, AY q.1 = mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E)
        (fun r : U ↦ (r : M)) q (Y q)) →
      mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (fun r : U ↦ (r : M)) p (B U X Y p) =
        CovariantDerivative.leviCivitaConnection 𝓘(ℝ, E) M
          (fun q ↦ AY q) p.1 (AX p.1)) :
    ∀ (U : Opens M) (X Y : LocalSmoothVectorField E M U) (p : U),
      B U X Y p - B U Y X p =
        VectorField.mlieBracket 𝓘(ℝ, E) (fun q ↦ X q) (fun q ↦ Y q) p := by
  intro U X Y p
  obtain ⟨AX, hAX⟩ := exists_smooth_vectorField_extension_germ U p X
  obtain ⟨AY, hAY⟩ := exists_smooth_vectorField_extension_germ U p Y
  apply smooth_open_inclusion_mfderiv_injective U p
  rw [map_sub, hB U X Y p AX AY hAX hAY, hB U Y X p AY AX hAY hAX,
    bracket_germ_naturality U p X Y AX AY hAX hAY]
  exact (CovariantDerivative.torsion_eq_zero_iff _).mp
    (CovariantDerivative.torsion_leviCivitaConnection_eq_zero 𝓘(ℝ, E))
    ((AX.contMDiff p.1).mdifferentiableAt (by simp))
    ((AY.contMDiff p.1).mdifferentiableAt (by simp))

/-- The induced local operator is compatible with the induced metric (Andrews, Lecture 10, p. 97). -/
private lemma native_leviCivita_operator_metric
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M]
    [RiemannianBundle (TangentSpace 𝓘(ℝ, E) : M → Type _)]
    [IsContMDiffRiemannianBundle 𝓘(ℝ, E) ∞ E (TangentSpace 𝓘(ℝ, E) : M → Type _)]
    (B : LocalBilinearCovariantDerivative E M)
    (hB : ∀ (U : Opens M) (X Y : LocalSmoothVectorField E M U)
      (p : U) (AX AY : ContMDiffSection 𝓘(ℝ, E) E ∞
        (TangentSpace 𝓘(ℝ, E) : M → Type _)),
      (∀ᶠ q in 𝓝 p, AX q.1 = mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E)
        (fun r : U ↦ (r : M)) q (X q)) →
      (∀ᶠ q in 𝓝 p, AY q.1 = mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E)
        (fun r : U ↦ (r : M)) q (Y q)) →
      mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (fun r : U ↦ (r : M)) p (B U X Y p) =
        CovariantDerivative.leviCivitaConnection 𝓘(ℝ, E) M
          (fun q ↦ AY q) p.1 (AX p.1)) :
    ∀ (U : Opens M) (X Y Z : LocalSmoothVectorField E M U) (p : U),
      let d := mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (fun r : U ↦ (r : M))
      mvfderiv 𝓘(ℝ, E) (fun q ↦ inner ℝ (d q (Y q)) (d q (Z q))) p (X p) =
        inner ℝ (d p (B U X Y p)) (d p (Z p)) +
          inner ℝ (d p (Y p)) (d p (B U X Z p)) := by
  intro U X Y Z p
  dsimp only
  obtain ⟨AX, hAX⟩ := exists_smooth_vectorField_extension_germ U p X
  obtain ⟨AY, hAY⟩ := exists_smooth_vectorField_extension_germ U p Y
  obtain ⟨AZ, hAZ⟩ := exists_smooth_vectorField_extension_germ U p Z
  have hp (V W : ∀ q : M, TangentSpace 𝓘(ℝ, E) q)
      (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞
        (fun q ↦ (⟨q, V q⟩ : TangentBundle 𝓘(ℝ, E) M)))
      (hW : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞
        (fun q ↦ (⟨q, W q⟩ : TangentBundle 𝓘(ℝ, E) M))) :
      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ (fun q ↦ inner ℝ (V q) (W q)) :=
    ContMDiff.inner_bundle (F := E) (E := TangentSpace 𝓘(ℝ, E)) hV hW
  have hpair := hp (fun q ↦ AY q) (fun q ↦ AZ q) AY.contMDiff AZ.contMDiff
  have hgerm : (fun q : U ↦ inner ℝ
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (fun r : U ↦ (r : M)) q (Y q))
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (fun r : U ↦ (r : M)) q (Z q)))
      =ᶠ[𝓝 p] (fun q : U ↦ inner ℝ (AY q.1) (AZ q.1)) := by
    filter_upwards [hAY, hAZ] with q hq hq'
    rw [← hq, ← hq']
  have hdir : mvfderiv 𝓘(ℝ, E) (fun q : U ↦ inner ℝ
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (fun r : U ↦ (r : M)) q (Y q))
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (fun r : U ↦ (r : M)) q (Z q))) p (X p) =
      mvfderiv 𝓘(ℝ, E) (fun q : M ↦ inner ℝ (AY q) (AZ q)) p.1 (AX p.1) := by
    change mfderiv 𝓘(ℝ, E) 𝓘(ℝ) _ p (X p) = _
    rw [hgerm.mfderiv_eq]
    change mfderiv 𝓘(ℝ, E) 𝓘(ℝ)
      ((fun q : M ↦ inner ℝ (AY q) (AZ q)) ∘ (fun q : U ↦ (q : M))) p (X p) = _
    rw [mfderiv_comp p ((hpair p.1).mdifferentiableAt (by simp))
      ((contMDiff_subtype_val (I := 𝓘(ℝ, E)) (U := U) (n := ∞) p).mdifferentiableAt
        (by simp)), ContinuousLinearMap.comp_apply,
      ← Filter.EventuallyEq.eq_of_nhds hAX]
    rfl
  rw [hdir, hB U X Y p AX AY hAX hAY, hB U X Z p AX AZ hAX hAZ,
    ← Filter.EventuallyEq.eq_of_nhds hAY, ← Filter.EventuallyEq.eq_of_nhds hAZ]
  exact (CovariantDerivative.isMetricCompatible_leviCivitaConnection 𝓘(ℝ, E)
    (M := M)).mvfderiv_inner_eq (fun q ↦ AX q)
      ((AY.contMDiff p.1).mdifferentiableAt (by simp))
      ((AZ.contMDiff p.1).mdifferentiableAt (by simp))

/-- The induced local operator satisfies the affine connection laws (Andrews, Definition 8.2.1). -/
private lemma native_leviCivita_operator_laws
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M]
    [RiemannianBundle (TangentSpace 𝓘(ℝ, E) : M → Type _)]
    [IsContMDiffRiemannianBundle 𝓘(ℝ, E) ∞ E (TangentSpace 𝓘(ℝ, E) : M → Type _)]
    (B : LocalBilinearCovariantDerivative E M)
    (hB : ∀ (U : Opens M) (X Y : LocalSmoothVectorField E M U)
      (p : U) (AX AY : ContMDiffSection 𝓘(ℝ, E) E ∞
        (TangentSpace 𝓘(ℝ, E) : M → Type _)),
      (∀ᶠ q in 𝓝 p, AX q.1 = mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E)
        (fun r : U ↦ (r : M)) q (X q)) →
      (∀ᶠ q in 𝓝 p, AY q.1 = mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E)
        (fun r : U ↦ (r : M)) q (Y q)) →
      mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (fun r : U ↦ (r : M)) p (B U X Y p) =
        CovariantDerivative.leviCivitaConnection 𝓘(ℝ, E) M
          (fun q ↦ AY q) p.1 (AX p.1)) : IsSmoothAffineConnectionOperator B := by
  refine ⟨native_leviCivita_operator_restriction B hB, ?_, ?_⟩
  · intro U X Y f hf
    apply ContMDiffSection.ext
    intro p
    obtain ⟨AX, hAX⟩ := exists_smooth_vectorField_extension_germ U p X
    obtain ⟨AY, hAY⟩ := exists_smooth_vectorField_extension_germ U p Y
    obtain ⟨F, hF, hFp⟩ := exists_smooth_scalar_extension_germ U p f hf
    let AFX : ContMDiffSection 𝓘(ℝ, E) E ∞
        (TangentSpace 𝓘(ℝ, E) : M → Type _) :=
      ⟨fun q ↦ F q • AX q, hF.smul_section AX.contMDiff⟩
    have hAFX : ∀ᶠ q in 𝓝 p, AFX q.1 =
        mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (fun r : U ↦ (r : M)) q
          (X.mulFunction f hf q) := by
      filter_upwards [hAX, hFp] with q hq hq'
      change F q.1 • AX q.1 = _
      rw [hq, hq']
      exact (map_smul _ _ _).symm
    apply smooth_open_inclusion_mfderiv_injective U p
    change _ = mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (fun r : U ↦ (r : M)) p
      (f p • B U X Y p)
    rw [map_smul, hB U (X.mulFunction f hf) Y p AFX AY hAFX hAY,
      hB U X Y p AX AY hAX hAY]
    change CovariantDerivative.leviCivitaConnection 𝓘(ℝ, E) M (fun q ↦ AY q)
      p.1 (F p.1 • AX p.1) = _
    rw [Filter.EventuallyEq.eq_of_nhds hFp]
    exact map_smul _ _ _
  · intro U X Y f hf p
    obtain ⟨AX, hAX⟩ := exists_smooth_vectorField_extension_germ U p X
    obtain ⟨AY, hAY⟩ := exists_smooth_vectorField_extension_germ U p Y
    obtain ⟨F, hF, hFp⟩ := exists_smooth_scalar_extension_germ U p f hf
    let AFY : ContMDiffSection 𝓘(ℝ, E) E ∞
        (TangentSpace 𝓘(ℝ, E) : M → Type _) :=
      ⟨fun q ↦ F q • AY q, hF.smul_section AY.contMDiff⟩
    have hAFY : ∀ᶠ q in 𝓝 p, AFY q.1 =
        mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (fun r : U ↦ (r : M)) q
          (Y.mulFunction f hf q) := by
      filter_upwards [hAY, hFp] with q hq hq'
      change F q.1 • AY q.1 = _
      rw [hq, hq']
      exact (map_smul _ _ _).symm
    apply smooth_open_inclusion_mfderiv_injective U p
    rw [map_add, map_smul, map_smul,
      hB U X (Y.mulFunction f hf) p AX AFY hAX hAFY,
      hB U X Y p AX AY hAX hAY,
      ← Filter.EventuallyEq.eq_of_nhds hAY,
      directional_derivative_germ_naturality U p f F hF X AX hFp hAX,
      ← Filter.EventuallyEq.eq_of_nhds hFp]
    have hc := (CovariantDerivative.leviCivitaConnection 𝓘(ℝ, E) M).isCovariantDerivativeOnUniv.leibniz
        ((AY.contMDiff p.1).mdifferentiableAt (by simp))
        ((hF p.1).mdifferentiableAt (by simp))
    exact congrArg (fun d ↦ d (AX p.1)) hc

/-- There is a unique smooth torsion-free metric-compatible affine connection (Andrews, Prop. 10.3.1). -/
private lemma native_smooth_leviCivita_exists_unique
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M]
    (g : ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E
      (TangentSpace 𝓘(ℝ, E) : M → Type _)) :
    ∃ nabla : SmoothAffineConnection E M,
      nabla.IsTorsionFree ∧ nabla.IsMetricCompatible g ∧
      ∀ other : SmoothAffineConnection E M,
        other.IsTorsionFree → other.IsMetricCompatible g → other = nabla := by
  let : RiemannianBundle (TangentSpace 𝓘(ℝ, E) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  obtain ⟨B, hB⟩ := native_leviCivita_all_open_operator (E := E) (M := M)
  let nabla : SmoothAffineConnection E M :=
    ⟨B, native_leviCivita_operator_laws B hB⟩
  have ht : nabla.IsTorsionFree := native_leviCivita_operator_torsion B hB
  have hg : nabla.IsMetricCompatible g := native_leviCivita_operator_metric B hB
  exact ⟨nabla, ht, hg, fun other ht' hg' ↦
    nabla.eq_of_torsionFree_metricCompatible g other ht hg ht' hg'⟩

/-- Coordinates of a vector in a genuine frame are recovered from its metric pairings and the inverse metric matrix (Andrews, Lecture 10, p. 98). -/
private lemma metric_inverse_frame_coordinate
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M]
    (g : ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E
      (TangentSpace 𝓘(ℝ, E) : M → Type _))
    (p : M) {n : ℕ} (e : Fin n → TangentSpace 𝓘(ℝ, E) p)
    (x : Fin n → ℝ) (v : TangentSpace 𝓘(ℝ, E) p)
    (hexp : ∑ i, x i • e i = v)
    (hdet : Matrix.det (fun i j ↦ g.inner p (e i) (e j)) ≠ 0) (k : Fin n) :
    x k = ∑ l, @Inv.inv (Matrix (Fin n) (Fin n) ℝ) Matrix.inv
      (fun i j ↦ g.inner p (e i) (e j))
      k l * g.inner p v (e l) := by
  classical
  let G : Matrix (Fin n) (Fin n) ℝ := fun i j ↦ g.inner p (e i) (e j)
  have hp : G *ᵥ x = fun l ↦ g.inner p v (e l) := by
    funext l
    have h := congrArg (fun w ↦ g.inner p (e l) w) hexp
    simpa only [G, Matrix.mulVec, dotProduct, map_sum, map_smul,
      smul_eq_mul, mul_comm, g.symm p (e l) v] using h
  have hi := congrArg (fun y ↦ (G⁻¹ *ᵥ y) k) hp
  rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul G
    (isUnit_iff_ne_zero.mpr hdet), Matrix.one_mulVec] at hi
  simpa only [G, Matrix.mulVec, dotProduct] using hi

/-- The three derivative terms in the Koszul formula combine into the inverse-metric coefficient sum (Andrews, Lecture 10, p. 98). -/
private lemma metric_inverse_koszul_coordinate
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    (g : ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E
      (TangentSpace 𝓘(ℝ, E) : M → Type _))
    (p : M) {n : ℕ} (e : Fin n → TangentSpace 𝓘(ℝ, E) p)
    (x : Fin n → ℝ) (v : TangentSpace 𝓘(ℝ, E) p)
    (hexp : ∑ i, x i • e i = v)
    (hdet : Matrix.det (fun i j ↦ g.inner p (e i) (e j)) ≠ 0)
    (H : Fin n → ℝ) (hH : ∀ l, 2 * g.inner p v (e l) = H l) (k : Fin n) :
    x k = (1 / 2 : ℝ) * ∑ l, @Inv.inv (Matrix (Fin n) (Fin n) ℝ) Matrix.inv
      (fun i j ↦ g.inner p (e i) (e j)) k l * H l := by
  classical
  rw [metric_inverse_frame_coordinate g p e x v hexp hdet k, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l _
  rw [← hH l]
  ring

/-- Coordinate-constant field germs commute at their center (Andrews, Lecture 10, p. 98). -/
private lemma bracket_coordinate_germs
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {N : Type*} [TopologicalSpace N] [ChartedSpace E N] [IsManifold 𝓘(ℝ, E) ∞ N]
    (c : OpenPartialHomeomorph N E) (hc : c ∈ maximalAtlas 𝓘(ℝ, E) ∞ N)
    (p : N) (hp : p ∈ c.source)
    (X Y : ContMDiffSection 𝓘(ℝ, E) E ∞ (TangentSpace 𝓘(ℝ, E) : N → Type _))
    (v w : E)
    (hX : ∀ᶠ q in 𝓝 p, mvfderiv 𝓘(ℝ, E) c q (X q) = v)
    (hY : ∀ᶠ q in 𝓝 p, mvfderiv 𝓘(ℝ, E) c q (Y q) = w) :
    VectorField.mlieBracket 𝓘(ℝ, E) (fun q ↦ X q) (fun q ↦ Y q) p = 0 := by
  let : IsManifold 𝓘(ℝ, E) (minSmoothness ℝ 2) N :=
    IsManifold.of_le (n := ∞) (by simp)
  have hcD : c.MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ, E) :=
    ⟨(contMDiffOn_of_mem_maximalAtlas hc).mdifferentiableOn (by simp),
      (contMDiffOn_symm_of_mem_maximalAtlas hc).mdifferentiableOn (by simp)⟩
  have hconst (a : E) (z : E) : ContMDiffAt 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞
      (fun z : E ↦ (⟨z, a⟩ : TangentBundle 𝓘(ℝ, E) E)) z :=
    contMDiffAt_vectorSpace_iff_contDiffAt.mpr contDiffAt_const
  have heq (Z : ContMDiffSection 𝓘(ℝ, E) E ∞ (TangentSpace 𝓘(ℝ, E) : N → Type _))
      (a : E) (hZ : ∀ᶠ q in 𝓝 p, mvfderiv 𝓘(ℝ, E) c q (Z q) = a) :
      VectorField.mpullback 𝓘(ℝ, E) 𝓘(ℝ, E) c (fun _ ↦ a) =ᶠ[𝓝 p] (fun q ↦ Z q) := by
    filter_upwards [hZ, c.open_source.mem_nhds hp] with q hq hqc
    change (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c q).inverse a = Z q
    rw [← hq]
    exact (show (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c q).IsInvertible from
      ⟨hcD.mfderiv hqc, rfl⟩).inverse_apply_self _
  have hn := VectorField.mpullback_mlieBracket
    ((hconst v (c p)).mdifferentiableAt (by simp))
    ((hconst w (c p)).mdifferentiableAt (by simp))
    (contMDiffAt_of_mem_maximalAtlas hc hp) (by simp)
  rw [(heq X v hX).mlieBracket_vectorField_eq (heq Y w hY)] at hn
  rw [← hn]
  change (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c p).inverse
    (VectorField.mlieBracketWithin 𝓘(ℝ, E) (fun _ ↦ v) (fun _ ↦ w) Set.univ (c p)) = 0
  rw [congrFun (VectorField.mlieBracketWithin_eq_lieBracketWithin
    (𝕜 := ℝ) (E := E) (V := fun _ ↦ v) (W := fun _ ↦ w) (s := Set.univ)) (c p)]
  simp [VectorField.lieBracketWithin]
  exact map_zero _

set_option backward.isDefEq.respectTransparency false in
/-- A field with prescribed chart coordinates is the inverse-chart frame transported by the open inclusion. -/
private lemma coordinate_frame_inclusion
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    (U : Opens M) (c : OpenPartialHomeomorph U E)
    (hc : c ∈ maximalAtlas 𝓘(ℝ, E) ∞ U) (p : U) (hp : p ∈ c.source)
    (v : TangentSpace 𝓘(ℝ, E) p) (a : E)
    (hv : mvfderiv 𝓘(ℝ, E) c p v = a) :
    mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (fun q : U ↦ (q : M)) p v =
      mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (fun z : E ↦ (c.symm z : M)) (c p) a := by
  have hcD : c.MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ, E) :=
    ⟨(contMDiffOn_of_mem_maximalAtlas hc).mdifferentiableOn (by simp),
      (contMDiffOn_symm_of_mem_maximalAtlas hc).mdifferentiableOn (by simp)⟩
  have hd := congrArg (fun d ↦ d v) (hcD.symm_comp_deriv hp)
  change mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c.symm (c p)
    (mvfderiv 𝓘(ℝ, E) c p v) = v at hd
  rw [hv] at hd
  change @Eq E _ (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (Subtype.val ∘ c.symm) (c p) a)
  erw [mfderiv_comp (c p)
    ((contMDiff_subtype_val (I := 𝓘(ℝ, E)) (U := U) (n := ∞)
      (c.symm (c p))).mdifferentiableAt (by simp))
    (hcD.symm.mdifferentiableAt (c.map_source hp)), ContinuousLinearMap.comp_apply,
    hd, c.left_inv hp]

/-- The derivative of a chart-composed germ is its ordinary coordinate derivative (Andrews, Lecture 8, p. 74). -/
private lemma scalar_coordinate_germ_derivative
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {N : Type*} [TopologicalSpace N] [ChartedSpace E N] [IsManifold 𝓘(ℝ, E) ∞ N]
    (c : OpenPartialHomeomorph N E) (hc : c ∈ maximalAtlas 𝓘(ℝ, E) ∞ N)
    (p : N) (hp : p ∈ c.source) (f : N → ℝ) (F : E → ℝ)
    (hF : DifferentiableAt ℝ F (c p)) (he : f =ᶠ[𝓝 p] F ∘ c)
    (v : TangentSpace 𝓘(ℝ, E) p) :
    mvfderiv 𝓘(ℝ, E) f p v = fderiv ℝ F (c p) (mvfderiv 𝓘(ℝ, E) c p v) := by
  change mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f p v = _
  rw [he.mfderiv_eq]
  have hh := mvfderiv_comp_apply p hF.mdifferentiableAt
    ((contMDiffAt_of_mem_maximalAtlas hc hp).mdifferentiableAt (by simp)) v
  rw [mvfderiv_eq_fderiv] at hh
  exact hh

/-- Pairings of coordinate-constant field germs are the corresponding entries of the inverse-chart metric. -/
private lemma metric_coordinate_pairing_germ
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    (g : ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E
      (TangentSpace 𝓘(ℝ, E) : M → Type _))
    (U : Opens M) (c : OpenPartialHomeomorph U E)
    (hc : c ∈ maximalAtlas 𝓘(ℝ, E) ∞ U) (p : U) (hp : p ∈ c.source)
    (X Y : LocalSmoothVectorField E M U) (v w : E)
    (hX : ∀ᶠ q in 𝓝 p, mvfderiv 𝓘(ℝ, E) c q (X q) = v)
    (hY : ∀ᶠ q in 𝓝 p, mvfderiv 𝓘(ℝ, E) c q (Y q) = w) :
    (fun q : U ↦ g.inner q.1
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (fun r : U ↦ (r : M)) q (X q))
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (fun r : U ↦ (r : M)) q (Y q))) =ᶠ[𝓝 p]
    (fun q : U ↦ g.inner (c.symm (c q)).1
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (fun z : E ↦ (c.symm z : M)) (c q) v)
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (fun z : E ↦ (c.symm z : M)) (c q) w)) := by
  filter_upwards [hX, hY, c.open_source.mem_nhds hp] with q hx hy hq
  have hx' := coordinate_frame_inclusion U c hc q hq (X q) v hx
  have hy' := coordinate_frame_inclusion U c hc q hq (Y q) w hy
  erw [← hx', ← hy', c.left_inv hq]

/-- Any torsion-free metric connection has Christoffel coefficients given by the inverse-metric Koszul formula (Andrews, Lecture 10, p. 98). -/
private lemma christoffel_eq_metric_formula
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M]
    (g : ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E
      (TangentSpace 𝓘(ℝ, E) : M → Type _))
    (nabla : SmoothAffineConnection E M) (ht : nabla.IsTorsionFree)
    (hg : nabla.IsMetricCompatible g) (U : Opens M) {n : ℕ}
    (b : Basis (Fin n) ℝ E) (c : OpenPartialHomeomorph U E)
    (hc : c ∈ maximalAtlas 𝓘(ℝ, E) ∞ U)
    (Γ : Fin n → Fin n → Fin n → U → ℝ)
    (hΓ : ∀ (X Y : LocalSmoothVectorField E M U) (p : U), p ∈ c.source → ∀ k,
      (nabla.cov U X Y).tangentCoefficient b c p k =
        (∑ i, X.tangentCoefficient b c p i *
          fderiv ℝ (Y.coordinateCoefficient b c k) (c p) (b i)) +
        ∑ i, ∑ j, X.tangentCoefficient b c p i * Y.tangentCoefficient b c p j * Γ i j k p)
    (p : U) (hp : p ∈ c.source) (i j k : Fin n) :
    let ψ : E → M := fun z ↦ (c.symm z : M)
    let G : E → Matrix (Fin n) (Fin n) ℝ := fun z r s ↦ g.inner (ψ z)
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) ψ z (b r))
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) ψ z (b s))
    Γ i j k p = (1 / 2 : ℝ) * ∑ l, ((G (c p))⁻¹) k l *
      (fderiv ℝ (fun z ↦ G z j l) (c p) (b i) +
        fderiv ℝ (fun z ↦ G z i l) (c p) (b j) -
        fderiv ℝ (fun z ↦ G z i j) (c p) (b l)) := by
  classical
  let ψ : E → M := fun z ↦ (c.symm z : M)
  let G : E → Matrix (Fin n) (Fin n) ℝ := fun z r s ↦ g.inner (ψ z)
    (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) ψ z (b r))
    (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) ψ z (b s))
  change Γ i j k p = (1 / 2 : ℝ) * ∑ l, ((G (c p))⁻¹) k l * _
  choose e he using fun r : Fin n ↦ exists_coordinate_frame_germ c hc p hp (b r)
  let d := mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (fun q : U ↦ (q : M))
  let P := fun (q : U) (v w : TangentSpace 𝓘(ℝ, E) q) ↦ g.inner q.1 (d q v) (d q w)
  have hψ : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ ψ c.target :=
    contMDiff_subtype_val.comp_contMDiffOn (contMDiffOn_symm_of_mem_maximalAtlas hc)
  have hG (r s : Fin n) : ContDiffOn ℝ ∞ (fun z ↦ G z r s) c.target :=
    smooth_metric_pullback_entry g c.open_target ψ hψ (b r) (b s)
  have hGP (r s : Fin n) : (fun q ↦ P q (e r q) (e s q)) =ᶠ[𝓝 p]
      (fun q ↦ G (c q) r s) :=
    metric_coordinate_pairing_germ g U c hc p hp (e r) (e s) (b r) (b s) (he r) (he s)
  have hder (r s t : Fin n) :
      mvfderiv 𝓘(ℝ, E) (fun q ↦ P q (e r q) (e s q)) p (e t p) =
        fderiv ℝ (fun z ↦ G z r s) (c p) (b t) := by
    rw [scalar_coordinate_germ_derivative c hc p hp _ _
      (((hG r s).contDiffAt (c.open_target.mem_nhds (c.map_source hp))).differentiableAt
        (by simp)) (hGP r s), (he t).self_of_nhds]
  have hsym (r s : Fin n) : (fun z ↦ G z r s) = fun z ↦ G z s r :=
    funext fun z ↦ g.symm _ _ _
  have hkos (l : Fin n) :
      2 * P p (nabla.cov U (e i) (e j) p) (e l p) =
        fderiv ℝ (fun z ↦ G z j l) (c p) (b i) +
          fderiv ℝ (fun z ↦ G z i l) (c p) (b j) -
          fderiv ℝ (fun z ↦ G z i j) (c p) (b l) := by
    have hk := nabla.koszul_of_torsionFree_metricCompatible g ht hg U (e i) (e j) (e l) p
    have hz (r s : Fin n) := bracket_coordinate_germs c hc p hp
      (e r) (e s) (b r) (b s) (he r) (he s)
    change 2 * P p (nabla.cov U (e i) (e j) p) (e l p) = _ at hk
    rw [hz i j, hz l i, hz l j] at hk
    simp only [map_zero, add_zero] at hk
    change 2 * P p (nabla.cov U (e i) (e j) p) (e l p) =
      mvfderiv 𝓘(ℝ, E) (fun q ↦ P q (e j q) (e l q)) p (e i p) +
      mvfderiv 𝓘(ℝ, E) (fun q ↦ P q (e l q) (e i q)) p (e j p) -
      mvfderiv 𝓘(ℝ, E) (fun q ↦ P q (e i q) (e j q)) p (e l p) at hk
    rw [hder, hder, hder, hsym l i] at hk
    exact hk
  let V := nabla.cov U (e i) (e j) p
  let x := fun r ↦ (nabla.cov U (e i) (e j)).tangentCoefficient b c p r
  have hexp : ∑ r, x r • e r p = V := by
    have hcD : c.MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ, E) :=
      ⟨(contMDiffOn_of_mem_maximalAtlas hc).mdifferentiableOn (by simp),
        (contMDiffOn_symm_of_mem_maximalAtlas hc).mdifferentiableOn (by simp)⟩
    apply hcD.mfderiv_injective hp
    change mvfderiv 𝓘(ℝ, E) c p (∑ r, x r • e r p) = mvfderiv 𝓘(ℝ, E) c p V
    simp only [map_sum, map_smul, fun r ↦ (he r).self_of_nhds]
    exact b.sum_repr _
  have hexpd : ∑ r, x r • d p (e r p) = d p V := by
    simpa only [map_sum, map_smul] using congrArg (d p) hexp
  have hmat : (fun r s ↦ g.inner p.1 (d p (e r p)) (d p (e s p))) = G (c p) := by
    funext r s
    exact (hGP r s).self_of_nhds
  have hdet : (G (c p)).det ≠ 0 := by
    apply smooth_metric_pullback_det_ne_zero g ψ (c p) _ b
    have hcD : c.MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ, E) :=
      ⟨(contMDiffOn_of_mem_maximalAtlas hc).mdifferentiableOn (by simp),
        (contMDiffOn_symm_of_mem_maximalAtlas hc).mdifferentiableOn (by simp)⟩
    change Function.Injective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (Subtype.val ∘ c.symm) (c p))
    rw [mfderiv_comp (c p)
      ((contMDiff_subtype_val (I := 𝓘(ℝ, E)) (U := U) (n := ∞)
        (c.symm (c p))).mdifferentiableAt (by simp))
      (hcD.symm.mdifferentiableAt (c.map_source hp))]
    exact (smooth_open_inclusion_mfderiv_injective U _).comp
      (hcD.symm.mfderiv_injective (c.map_source hp))
  have hxk := metric_inverse_koszul_coordinate g p.1 (fun r ↦ d p (e r p)) x (d p V)
    hexpd (by rw [hmat]; exact hdet) _ hkos k
  rw [hmat] at hxk
  rw [← christoffel_coefficient_of_coordinate_germs nabla.cov U b c Γ hΓ p hp i j k (e i) (e j) (he i) (he j)]
  exact hxk

/-- The smooth torsion-free metric-compatible affine connection exists uniquely, with the stated local coordinate formula (Andrews, Prop. 10.3.1). -/
theorem andrews_smooth_levi_civita_connection
    (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (M : Type*) [TopologicalSpace M] [T2Space M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M]
    (g : ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E
      (TangentSpace 𝓘(ℝ, E) : M → Type _)) :
    let gU := fun (U : Opens M) (p : U)
        (v w : TangentSpace 𝓘(ℝ, E) p) ↦
      let dι := mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (fun q : U ↦ (q : M)) p
      g.inner p.1 (dι v) (dι w)
    ∃ nabla : SmoothAffineConnection E M,
      nabla.IsTorsionFree ∧ nabla.IsMetricCompatible g ∧
      (∀ other : SmoothAffineConnection E M,
        other.IsTorsionFree → other.IsMetricCompatible g → other = nabla) ∧
      (∀ (U : Opens M) (X Y Z : LocalSmoothVectorField E M U) (p : U),
        2 * gU U p (nabla.cov U X Y p) (Z p) =
          mvfderiv 𝓘(ℝ, E) (fun q : U ↦ gU U q (Y q) (Z q)) p (X p) +
          mvfderiv 𝓘(ℝ, E) (fun q : U ↦ gU U q (Z q) (X q)) p (Y p) -
          mvfderiv 𝓘(ℝ, E) (fun q : U ↦ gU U q (X q) (Y q)) p (Z p) +
          gU U p (Z p)
            (VectorField.mlieBracket 𝓘(ℝ, E) (fun q ↦ X q) (fun q ↦ Y q) p) +
          gU U p (Y p)
            (VectorField.mlieBracket 𝓘(ℝ, E) (fun q ↦ Z q) (fun q ↦ X q) p) +
          gU U p (X p)
            (VectorField.mlieBracket 𝓘(ℝ, E) (fun q ↦ Z q) (fun q ↦ Y q) p)) ∧
      (∀ (U : Opens M) (n : ℕ) (b : Basis (Fin n) ℝ E)
          (c : OpenPartialHomeomorph U E), c ∈ maximalAtlas 𝓘(ℝ, E) ∞ U →
        let ψ : E → M := fun z ↦ (c.symm z : M)
        let e := fun (i : Fin n) (z : E) ↦ mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) ψ z (b i)
        let G : E → Matrix (Fin n) (Fin n) ℝ :=
          fun z i j ↦ g.inner (ψ z) (e i z) (e j z)
        ∃ Γ : Fin n → Fin n → Fin n → U → ℝ,
          (∀ i j k, ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ) ∞ (Γ i j k) c.source) ∧
          (∀ i j k, ContDiffOn ℝ ∞ (fun z ↦ Γ i j k (c.symm z)) c.target) ∧
          (∀ (p : U), p ∈ c.source → ∀ i j k : Fin n,
            Γ i j k p = (1 / 2 : ℝ) * ∑ l : Fin n,
              ((G (c p))⁻¹) k l *
                (fderiv ℝ (fun z ↦ G z j l) (c p) (b i) +
                  fderiv ℝ (fun z ↦ G z i l) (c p) (b j) -
                  fderiv ℝ (fun z ↦ G z i j) (c p) (b l))) ∧
          (∀ (X Y : LocalSmoothVectorField E M U) (p : U), p ∈ c.source →
            ∀ k : Fin n,
              (nabla.cov U X Y).tangentCoefficient b c p k =
                (∑ i, X.tangentCoefficient b c p i *
                  fderiv ℝ (Y.coordinateCoefficient b c k) (c p) (b i)) +
                ∑ i, ∑ j, X.tangentCoefficient b c p i *
                  Y.tangentCoefficient b c p j * Γ i j k p)) := by
  obtain ⟨nabla, ht, hg, hu⟩ := native_smooth_leviCivita_exists_unique g
  refine ⟨nabla, ht, hg, hu, ?_, ?_⟩
  · intro U X Y Z p
    exact nabla.koszul_of_torsionFree_metricCompatible g ht hg U X Y Z p
  · intro U n b c hc
    obtain ⟨Γ, hs, hsc, hformula⟩ := smooth_metric_chart_coefficients g U n b c hc
    refine ⟨Γ, hs, hsc, hformula, ?_⟩
    obtain ⟨Γ', _, hΓ'⟩ :=
      ((isSmoothAffineConnectionOperator_iff_christoffel nabla.cov).mp nabla.laws).2 U n b c hc
    intro X Y p hp k
    rw [hΓ' X Y p hp k]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [christoffel_eq_metric_formula g nabla ht hg U b c hc Γ' hΓ' p hp i j k,
      hformula p hp i j k]

end

end HolomorphicAnosov
