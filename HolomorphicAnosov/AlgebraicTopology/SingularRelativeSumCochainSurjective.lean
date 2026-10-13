import HolomorphicAnosov.AlgebraicTopology.SingularCochainPairPullbackDefinition
import HolomorphicAnosov.AlgebraicTopology.SingularSumSubspaceSimplexFactorization
import HolomorphicAnosov.AlgebraicTopology.EvaluatedKernelElementLift
import HolomorphicAnosov.AlgebraicTopology.SingularSumCochainDegreewise
import Mathlib.Algebra.Homology.HomologicalComplexKernels
open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial
universe u
noncomputable section
namespace HolomorphicAnosov.SingularCochain
set_option backward.isDefEq.respectTransparency false
theorem relative_sum_cochain_restriction_surjective (R : Type u) [CommRing R] {ι : Type u} (X : ι → TopCat.{u})
    (A : ∀ j, Set (X j)) (n : ℕ) :
    Function.Surjective (fun c : (relativeComplex R (TopCat.of (Σ j, X j)) ((fun x : (Σ j, X j) => x.2 ∈ A x.1))).X n =>
      fun j => (relativePullback R (X := X j) (Y := TopCat.of (Σ k, X k)) (A := A j) (B := (fun x : (Σ j, X j) => x.2 ∈ A x.1))
        (TopCat.ofHom (ContinuousMap.sigmaMk (X := fun j => (X j : Type u)) j)) (fun _ hx => hx)).f n c) := by
  intro cs
  let p := pullback R (subspaceInclusion (TopCat.of (Σ j, X j)) ((fun x : (Σ j, X j) => x.2 ∈ A x.1)))
  let ks := fun j => (kernel.ι (pullback R (subspaceInclusion (X j) (A j)))).f n
  obtain ⟨c, hc⟩ := (singular_sum_cochain_restriction_bijective R X n).surjective
    (fun j => ks j (cs j))
  have hz : p.f n c = 0 := by
    apply SSet.chainComplex_hom_ext
    intro σ
    obtain ⟨j, τ, rfl⟩ := singular_sum_subspace_simplex_factorization X A n σ
    have hj := congrFun hc j
    have hcond := congrArg (fun f => f.f n)
      (kernel.condition (pullback R (subspaceInclusion (X j) (A j))))
    let f := pairSubspaceMap (X := X j) (Y := TopCat.of (Σ k, X k)) (A := A j) (B := (fun x : (Σ j, X j) => x.2 ∈ A x.1))
      (TopCat.ofHom (ContinuousMap.sigmaMk (X := fun j => (X j : Type u)) j)) (fun _ hx => hx)
    have hs := congrArg (fun m => m.f n)
      (pairRestrictionSquare R (X := X j) (Y := TopCat.of (Σ k, X k)) (A := A j) (B := (fun x : (Σ j, X j) => x.2 ∈ A x.1))
        (TopCat.ofHom (ContinuousMap.sigmaMk (X := fun j => (X j : Type u)) j)) (fun _ hx => hx))
    have hv := congrArg (fun m => m c) hs
    change (pullback R f).f n (p.f n c) =
      (pullback R (subspaceInclusion (X j) (A j))).f n
        ((pullback R (TopCat.ofHom (ContinuousMap.sigmaMk (X := fun j => (X j : Type u)) j))).f n c) at hv
    change (pullback R (TopCat.ofHom (ContinuousMap.sigmaMk (X := fun j => (X j : Type u)) j))).f n c = ks j (cs j) at hj
    rw [hj] at hv
    have hzj : (pullback R (subspaceInclusion (X j) (A j))).f n (ks j (cs j)) = 0 := by
      exact congrArg (fun m => m (cs j)) hcond
    rw [hzj] at hv
    change (SSet.chainComplexMap (TopCat.toSSet.map f) (ModuleCat.of R R)).f n ≫
      (p.f n c) = 0 at hv
    have hvgen := congrArg (fun m => (TopCat.toSSet.obj (TopCat.of (A j))).ιChainComplex τ ≫ m) hv
    simp only [SSet.ι_chainComplexMap_f_assoc, comp_zero] at hvgen
    simpa only [comp_zero] using hvgen
  obtain ⟨y, hy⟩ := evaluated_kernel_element_lift p n c hz
  refine ⟨y, ?_⟩
  funext j
  apply (ModuleCat.mono_iff_injective (ks j)).mp inferInstance
  have hmap : relativePullback R (X := X j) (Y := TopCat.of (Σ k, X k)) (A := A j) (B := (fun x : (Σ j, X j) => x.2 ∈ A x.1))
      (TopCat.ofHom (ContinuousMap.sigmaMk (X := fun j => (X j : Type u)) j)) (fun _ hx => hx) ≫
      kernel.ι (pullback R (subspaceInclusion (X j) (A j))) =
      kernel.ι p ≫ pullback R (TopCat.ofHom (ContinuousMap.sigmaMk (X := fun j => (X j : Type u)) j)) := kernel.lift_ι _ _ _
  have hn := congrArg (fun f => f.f n) hmap
  have hh := congrArg (fun f => f y) hn
  change _ = ks j (cs j)
  rw [show ks j ((relativePullback R (X := X j) (Y := TopCat.of (Σ k, X k)) (A := A j) (B := (fun x : (Σ j, X j) => x.2 ∈ A x.1))
      (TopCat.ofHom (ContinuousMap.sigmaMk (X := fun j => (X j : Type u)) j)) (fun _ hx => hx)).f n y) =
      (pullback R (TopCat.ofHom (ContinuousMap.sigmaMk (X := fun j => (X j : Type u)) j))).f n ((kernel.ι p).f n y) from hh]
  rw [hy]
  exact congrFun hc j
end HolomorphicAnosov.SingularCochain
