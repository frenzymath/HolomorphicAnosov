import Mathlib.Algebra.Algebra.RestrictScalars
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Geometry.Manifold.VectorBundle.Basic
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Smooth Hermitian metrics on finite-rank complex bundles


-/ 

open Bundle
open scoped ContDiff Manifold

namespace HolomorphicAnosov

universe u v w

variable {B : Type u} [NormedAddCommGroup B] [NormedSpace ℝ B]
  [FiniteDimensional ℝ B]
  {M : Type v} [TopologicalSpace M] [ChartedSpace B M]
  {E : M → Type w} [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]

/-- The real fibre action is the literal restriction of the given complex action. Source: Mathlib `Module.restrictScalars`, matching the underlying real vector spaces in Moroianu §4.2, printed pp.24–25, and Hatcher Proposition 1.3, printed pp.12–13. -/
noncomputable local instance hermitianMetricFiberRealModule (x : M) : Module ℝ (E x) :=
  Module.restrictScalars ℝ ℂ (E x)

/-- The positive weighted pullback construction used in Moroianu §4.2, p.25. No norm is installed on the source vector space. -/
private theorem hermitian_weighted_pullback_core
    {V H ι : Type*} [AddCommGroup V] [Module ℂ V]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [Fintype ι]
    (p : ι → V →ₗ[ℂ] H) (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i)
    (hp : ∃ i, 0 < a i ∧ Function.Injective (p i)) :
    ∃ g : InnerProductSpace.Core ℂ V,
      ∀ v w, g.inner v w = ∑ i, (a i : ℂ) * inner ℂ (p i v) (p i w) := by
  classical
  refine ⟨{ inner := fun v w ↦ ∑ i, (a i : ℂ) * inner ℂ (p i v) (p i w)
            conj_inner_symm := ?_
            re_inner_nonneg := ?_
            add_left := ?_
            smul_left := ?_
            definite := ?_ }, fun _ _ ↦ rfl⟩
  · intro v w
    simp only [map_sum, map_mul, Complex.conj_ofReal, inner_conj_symm]
  · intro v
    rw [map_sum]
    change 0 ≤ ∑ i, ((a i : ℂ) * inner ℂ (p i v) (p i v)).re
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    exact Finset.sum_nonneg fun i _ ↦ mul_nonneg (ha i) (inner_self_nonneg (𝕜 := ℂ))
  · intro v w z
    simp only [map_add, inner_add_left, mul_add, Finset.sum_add_distrib]
  · intro v w c
    simp only [map_smul, inner_smul_left, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  · intro v hv
    obtain ⟨i, hi, hpi⟩ := hp
    have hz : ∑ j, a j * (inner ℂ (p j v) (p j v)).re = 0 := by
      have h := congrArg RCLike.re hv
      rw [map_sum, map_zero] at h
      change (∑ j, ((a j : ℂ) * inner ℂ (p j v) (p j v)).re) = 0 at h
      simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
        using h
    have hterm : a i * (inner ℂ (p i v) (p i v)).re = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg
        (fun j _ ↦ mul_nonneg (ha j) (inner_self_nonneg (𝕜 := ℂ)))).mp hz i
          (Finset.mem_univ i)
    have hinner : (inner ℂ (p i v) (p i v)).re = 0 :=
      (mul_eq_zero.mp hterm).resolve_left hi.ne'
    have hnorm : ‖p i v‖ ^ 2 = 0 := by
      rw [InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ)]
      exact hinner
    have hpzero : p i v = 0 := norm_eq_zero.mp (sq_eq_zero_iff.mp hnorm)
    exact hpi (hpzero.trans (map_zero (p i)).symm)

/-- Any positive Hermitian core on a finite-rank original fibre has its original topology. This uses the native original coordinate homeomorphism and Mathlib's uniqueness of finite-dimensional Hausdorff vector-space topology. -/
private theorem hermitian_core_topology {V : Type*} [AddCommGroup V] [Module ℂ V]
    [TopologicalSpace V] (r : ℕ) (e : V ≃L[ℂ] (Fin r → ℂ))
    (g : InnerProductSpace.Core ℂ V) :
    (inferInstance : TopologicalSpace V) =
      g.toNormedAddCommGroup.toMetricSpace.toUniformSpace.toTopologicalSpace := by
  have hold := e.toHomeomorph.isEmbedding.isInducing.eq_induced
  let q : V ≃ₗ[ℂ] (Fin r → ℂ) := e.toLinearEquiv
  let : FiniteDimensional ℂ V := FiniteDimensional.of_injective e.toLinearMap e.injective
  let : InnerProductSpace.Core ℂ V := g
  let : NormedAddCommGroup V := g.toNormedAddCommGroup
  let : TopologicalSpace V :=
    g.toNormedAddCommGroup.toMetricSpace.toUniformSpace.toTopologicalSpace
  let : NormedSpace ℂ V := InnerProductSpace.Core.toNormedSpace
  have hnew := q.toContinuousLinearEquiv.toHomeomorph.isEmbedding.isInducing.eq_induced
  exact hold.trans hnew.symm

omit [FiniteDimensional ℝ B] in
/-- The zero extension of a supported weighted local Hermitian pairing is smooth. Inside the original trivialization this is a product of smooth coordinate pairings; outside its base set the weight vanishes on a neighbourhood. -/
private theorem hermitian_weighted_pairing_smooth (r : ℕ)
    [IsManifold 𝓘(ℝ, B) ∞ M]
    [TopologicalSpace (TotalSpace (Fin r → ℂ) E)] [∀ x, TopologicalSpace (E x)]
    [FiberBundle (Fin r → ℂ) E]
    [VectorBundle ℂ (Fin r → ℂ) E] [VectorBundle ℝ (Fin r → ℂ) E]
    [ContMDiffVectorBundle ∞ (Fin r → ℂ) E 𝓘(ℝ, B)]
    (e : Trivialization (Fin r → ℂ) (π (Fin r → ℂ) E)) [MemTrivializationAtlas e]
    (a : C^∞⟮𝓘(ℝ, B), M; 𝓘(ℝ), ℝ⟯) (ha : tsupport a ⊆ e.baseSet)
    (U : Set M) (s t : ∀ x, E x)
    (hs : ContMDiffOn 𝓘(ℝ, B) (𝓘(ℝ, B).prod 𝓘(ℝ, Fin r → ℂ)) ∞
      (fun x ↦ TotalSpace.mk' (Fin r → ℂ) x (s x)) U)
    (ht : ContMDiffOn 𝓘(ℝ, B) (𝓘(ℝ, B).prod 𝓘(ℝ, Fin r → ℂ)) ∞
      (fun x ↦ TotalSpace.mk' (Fin r → ℂ) x (t x)) U) :
    ContMDiffOn 𝓘(ℝ, B) 𝓘(ℝ, ℂ) ∞
      (fun x ↦ a x • inner ℂ
        ((EuclideanSpace.equiv (Fin r) ℂ).symm (e.linearMapAt ℂ x (s x)))
        ((EuclideanSpace.equiv (Fin r) ℂ).symm (e.linearMapAt ℂ x (t x)))) U := by
  intro x hx
  by_cases he : x ∈ e.baseSet
  · have hs' := (e.contMDiffWithinAt_section (IB := 𝓘(ℝ, B)) U he).mp (hs x hx)
    have ht' := (e.contMDiffWithinAt_section (IB := 𝓘(ℝ, B)) U he).mp (ht x hx)
    have hq := ((EuclideanSpace.equiv (Fin r) ℂ).symm.toContinuousLinearMap.restrictScalars ℝ).contDiff
      (n := ∞)
    have hp := (contDiff_inner (𝕜 := ℂ)).comp_contMDiffWithinAt
      ((hq.comp_contMDiffWithinAt hs').prodMk_space (hq.comp_contMDiffWithinAt ht'))
    have hprod := (a.contMDiff x).contMDiffWithinAt.smul hp
    apply hprod.congr_of_eventuallyEq
    · filter_upwards [Filter.Eventually.filter_mono nhdsWithin_le_nhds
        (e.open_baseSet.mem_nhds he)] with y hy
      simp only [e.coe_linearMapAt_of_mem hy, Function.comp_apply]
      rfl
    · simp only [e.coe_linearMapAt_of_mem he, Function.comp_apply]
      rfl
  · have hz : x ∉ tsupport a := fun h ↦ he (ha h)
    have hz' := notMem_tsupport_iff_eventuallyEq.mp hz
    have heq : (fun y ↦ a y • inner ℂ
        ((EuclideanSpace.equiv (Fin r) ℂ).symm (e.linearMapAt ℂ y (s y)))
        ((EuclideanSpace.equiv (Fin r) ℂ).symm (e.linearMapAt ℂ y (t y))))
        =ᶠ[nhds x] (fun _ ↦ (0 : ℂ)) := by
      filter_upwards [hz'] with y hy
      simp [hy]
    exact contMDiffWithinAt_const.congr_of_eventuallyEq
      (Filter.EventuallyEq.filter_mono heq nhdsWithin_le_nhds) heq.self_of_nhds

/-- A compact Hausdorff finite-dimensional smooth real manifold without boundary admits a smooth positive definite first-linear Hermitian metric on every smooth complex vector bundle of rank `r`, including `r = 0`. Source: Moroianu, author manuscript of March 16, 2004, §4.2 Definition 4.2 and the written Hermitian-structure construction, printed pp.24–25; Hatcher, *Vector Bundles and K-Theory*, Version 2.2, November 2017, Lemma 1.1, printed p.8, and Proposition 1.3 with its isometric-trivialization conclusion, printed pp.12–13. -/
theorem smooth_complex_bundle_hermitian_metric (r : ℕ)
    [CompactSpace M] [T2Space M] [IsManifold 𝓘(ℝ, B) ∞ M]
    [TopologicalSpace (TotalSpace (Fin r → ℂ) E)] [∀ x, TopologicalSpace (E x)]
    [FiberBundle (Fin r → ℂ) E]
    [VectorBundle ℂ (Fin r → ℂ) E] [VectorBundle ℝ (Fin r → ℂ) E]
    [ContMDiffVectorBundle ∞ (Fin r → ℂ) E 𝓘(ℝ, B)] :
    ∃ g : ∀ x, InnerProductSpace.Core ℂ (E x),
      let h : ∀ x, E x → E x → ℂ := fun x v w ↦ (g x).inner w v
      (∀ (U : Set M), IsOpen U → ∀ (s t : ∀ x, E x),
        ContMDiffOn 𝓘(ℝ, B) (𝓘(ℝ, B).prod 𝓘(ℝ, Fin r → ℂ)) ∞
          (fun x ↦ TotalSpace.mk' (Fin r → ℂ) x (s x)) U →
        ContMDiffOn 𝓘(ℝ, B) (𝓘(ℝ, B).prod 𝓘(ℝ, Fin r → ℂ)) ∞
          (fun x ↦ TotalSpace.mk' (Fin r → ℂ) x (t x)) U →
        ContMDiffOn 𝓘(ℝ, B) 𝓘(ℝ, ℂ) ∞ (fun x ↦ h x (s x) (t x)) U) ∧
      (∀ (U : Set M), IsOpen U → ∀ (s : Fin r → ∀ x, E x),
        (∀ x ∈ U, LinearIndependent ℂ (fun i ↦ s i x)) →
        (∀ x ∈ U, Submodule.span ℂ (Set.range (fun i ↦ s i x)) = ⊤) →
        (∀ i, ContMDiffOn 𝓘(ℝ, B) (𝓘(ℝ, B).prod 𝓘(ℝ, Fin r → ℂ)) ∞
          (fun x ↦ TotalSpace.mk' (Fin r → ℂ) x (s i x)) U) →
        ∀ i j, ContMDiffOn 𝓘(ℝ, B) 𝓘(ℝ, ℂ) ∞
          (fun x ↦ h x (s i x) (s j x)) U) ∧
      (∀ x, (inferInstance : TopologicalSpace (E x)) =
        (g x).toNormedAddCommGroup.toMetricSpace.toUniformSpace.toTopologicalSpace) := by
  classical
  let e (x : M) := trivializationAt (Fin r → ℂ) E x
  obtain ⟨J, hJ⟩ := isCompact_univ.elim_finite_subcover (fun x ↦ (e x).baseSet)
    (fun x ↦ (e x).open_baseSet) (by
      intro x _
      exact Set.mem_iUnion.mpr ⟨x, FiberBundle.mem_baseSet_trivializationAt (Fin r → ℂ) E x⟩)
  let ι := ↥J
  have hcover : Set.univ ⊆ ⋃ i : ι, (e i).baseSet := by
    intro x hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hJ hx)
    obtain ⟨hi, hxi⟩ := Set.mem_iUnion.mp hi
    exact Set.mem_iUnion.mpr ⟨⟨i, hi⟩, hxi⟩
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate 𝓘(ℝ, B)
    isClosed_univ (fun i : ι ↦ (e i).baseSet) (fun i ↦ (e i).open_baseSet) hcover
  let p (x : M) (i : ι) : E x →ₗ[ℂ] EuclideanSpace ℂ (Fin r) :=
    (EuclideanSpace.equiv (Fin r) ℂ).symm.toLinearEquiv.toLinearMap.comp
      ((e i).linearMapAt ℂ x)
  have hpos (x : M) : ∃ i : ι, 0 < ρ i x ∧ Function.Injective (p x i) := by
    obtain ⟨i, hi⟩ := ρ.exists_pos_of_mem (Set.mem_univ x)
    have hx : x ∈ (e i).baseSet := hρ i (subset_tsupport (ρ i) hi.ne')
    refine ⟨i, hi, ?_⟩
    have heinj := ((e i).linearEquivAt ℂ x hx).injective
    exact (EuclideanSpace.equiv (Fin r) ℂ).symm.injective.comp (by
      rw [(e i).coe_linearMapAt_of_mem hx]
      exact heinj)
  choose g hg using fun x ↦ hermitian_weighted_pullback_core (p x) (fun i ↦ ρ i x)
    (fun i ↦ ρ.nonneg i x) (hpos x)
  have hsmooth (U : Set M) (s t : ∀ x, E x)
      (hs : ContMDiffOn 𝓘(ℝ, B) (𝓘(ℝ, B).prod 𝓘(ℝ, Fin r → ℂ)) ∞
        (fun x ↦ TotalSpace.mk' (Fin r → ℂ) x (s x)) U)
      (ht : ContMDiffOn 𝓘(ℝ, B) (𝓘(ℝ, B).prod 𝓘(ℝ, Fin r → ℂ)) ∞
        (fun x ↦ TotalSpace.mk' (Fin r → ℂ) x (t x)) U) :
      ContMDiffOn 𝓘(ℝ, B) 𝓘(ℝ, ℂ) ∞ (fun x ↦ (g x).inner (t x) (s x)) U := by
    have hsum := contMDiffOn_finsetSum (t := (Finset.univ : Finset ι)) (fun i _ ↦
      hermitian_weighted_pairing_smooth r (e i) (ρ i) (hρ i) U t s ht hs)
    convert hsum using 1
    funext x
    rw [hg]
    apply Finset.sum_congr rfl
    intro i _
    rfl
  refine ⟨g, ?_, ?_, ?_⟩
  · intro U _ s t hs ht
    exact hsmooth U s t hs ht
  · intro U _ s _ _ hs i j
    exact hsmooth U (s i) (s j) (hs i) (hs j)
  · intro x
    exact hermitian_core_topology r
      ((e x).continuousLinearEquivAt ℂ x
        (FiberBundle.mem_baseSet_trivializationAt (Fin r → ℂ) E x)) (g x)


end HolomorphicAnosov
