import HolomorphicAnosov.AlgebraicTopology.SingularCochainPairPullbackDefinition
import HolomorphicAnosov.AlgebraicTopology.SingularSumSimplexBijection
open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial
universe u
noncomputable section
namespace HolomorphicAnosov.SingularCochain
set_option backward.isDefEq.respectTransparency false
/-! Relative summand restriction is degreewise injective. -/
/-- The relative cochain restriction to all summands is injective.
Source: Hatcher, *Algebraic Topology*, p.202; DAG
`algebra.singular_relative_sum_cochain_injective_g13`.

The relative kernel inclusion is monic. If two relative cochains have equal
restrictions, postcompose that equality with the kernel inclusion of each
summand. The kernel map inclusion identity reduces this to equality after the
ambient summand chain map. Every ambient singular simplex factors through one
summand by `singular_sum_simplex_bijective`, and coproduct generator extensionality
then proves equality of the ambient cochains. -/
theorem relative_sum_cochain_restriction_injective (R : Type u) [CommRing R] {ι : Type u} (X : ι → TopCat.{u})
    (A : ∀ j, Set (X j)) (n : ℕ) :
    Function.Injective (fun c : (relativeComplex R (TopCat.of (Σ j, X j)) ((fun x : (Σ j, X j) => x.2 ∈ A x.1))).X n =>
      fun j => (relativePullback R (X := X j) (Y := TopCat.of (Σ k, X k)) (A := A j) (B := (fun x : (Σ j, X j) => x.2 ∈ A x.1)) (TopCat.ofHom (ContinuousMap.sigmaMk (X := fun j => (X j : Type u)) j)) (fun _ hx => hx) ).f n c) := by
  intro c d hcd
  let k := (kernel.ι (pullback R (subspaceInclusion (TopCat.of (Σ j, X j)) ((fun x : (Σ j, X j) => x.2 ∈ A x.1))))).f n
  apply (ModuleCat.mono_iff_injective k).mp inferInstance
  apply SSet.chainComplex_hom_ext
  intro σ
  obtain ⟨⟨j, τ⟩, hτ⟩ := (singular_sum_simplex_bijective X (op ⦋n⦌)).surjective σ
  subst σ
  have hj := congrFun hcd j
  have hh := congrArg (fun x =>
      (kernel.ι (pullback R (subspaceInclusion (X j) (A j)))).f n x) hj
  have hmap : relativePullback R (X := X j) (Y := TopCat.of (Σ k, X k)) (A := A j) (B := (fun x : (Σ j, X j) => x.2 ∈ A x.1)) (TopCat.ofHom (ContinuousMap.sigmaMk (X := fun j => (X j : Type u)) j)) (fun _ hx => hx) ≫
      kernel.ι (pullback R (subspaceInclusion (X j) (A j))) =
      kernel.ι (pullback R (subspaceInclusion (TopCat.of (Σ j, X j)) ((fun x : (Σ j, X j) => x.2 ∈ A x.1)))) ≫
        pullback R (TopCat.ofHom (ContinuousMap.sigmaMk (X := fun j => (X j : Type u)) j)) := by
    exact kernel.lift_ι _ _ _
  have hn := congrArg (fun z => z.f n) hmap
  change (((relativePullback R (X := X j) (Y := TopCat.of (Σ k, X k)) (A := A j) (B := (fun x : (Σ j, X j) => x.2 ∈ A x.1)) (TopCat.ofHom (ContinuousMap.sigmaMk (X := fun j => (X j : Type u)) j)) (fun _ hx => hx)).f n ≫
      (kernel.ι (pullback R (subspaceInclusion (X j) (A j)))).f n) c) =
    (((relativePullback R (X := X j) (Y := TopCat.of (Σ k, X k)) (A := A j) (B := (fun x : (Σ j, X j) => x.2 ∈ A x.1)) (TopCat.ofHom (ContinuousMap.sigmaMk (X := fun j => (X j : Type u)) j)) (fun _ hx => hx)).f n ≫
      (kernel.ι (pullback R (subspaceInclusion (X j) (A j)))).f n) d) at hh
  simp only [HomologicalComplex.comp_f] at hn
  rw [hn] at hh
  change (SSet.chainComplexMap (TopCat.toSSet.map (TopCat.ofHom (ContinuousMap.sigmaMk (X := fun j => (X j : Type u)) j)))
      (ModuleCat.of R R)).f n ≫ (k c) =
    (SSet.chainComplexMap (TopCat.toSSet.map (TopCat.ofHom (ContinuousMap.sigmaMk (X := fun j => (X j : Type u)) j)))
      (ModuleCat.of R R)).f n ≫ (k d) at hh
  have hgen := congrArg (fun f => (TopCat.toSSet.obj (X j)).ιChainComplex τ ≫ f) hh
  simp only [SSet.ι_chainComplexMap_f_assoc] at hgen
  exact hgen
end HolomorphicAnosov.SingularCochain
