import Mathlib

/-!
# Codimension-one holomorphic Anosov diffeomorphisms

The four main theorems of J. Zhang, *Codimension-one holomorphic Anosov diffeomorphisms*
(arXiv:2609.37695): Theorem A and Theorems 1.1, 1.2, 1.3, stated over Mathlib together with
every definition they use. Theorems A, 1.1 and 1.3 assume `HomotopyTorusRigidity`, the
homotopy-torus rigidity theorem in dimension at least five that Ghys invokes for his Theorem B.
-/

noncomputable section

universe u v

open scoped ContDiff

namespace HolomorphicAnosov

/-! ## Real tangent subbundles and invariant splittings -/

section RealTangentBundles

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H]

/-- A real distribution: a choice of a real linear subspace of every tangent space. -/
abbrev RealTangentDistribution (I : ModelWithCorners ℝ E H) (X : Type*)
    [TopologicalSpace X] [ChartedSpace H X] :=
  ∀ x : X, Submodule ℝ (TangentSpace I x)

/-- A continuous real subbundle of the tangent bundle: a distribution that is locally trivial
in the topology induced from the tangent bundle. -/
structure ContinuousRealTangentSubbundle (I : ModelWithCorners ℝ E H)
    (X : Type*) [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ∞ X] where
  /-- The fibres of the subbundle. -/
  toDistribution : RealTangentDistribution I X
  /-- Local triviality near every point. -/
  locally_trivial : ∀ x : X, ∃ r : ℕ,
    letI : TopologicalSpace
        (Bundle.TotalSpace (Fin r → ℝ) (fun y : X ↦ ↥(toDistribution y))) :=
      TopologicalSpace.induced
        (fun z ↦ (⟨z.proj, z.snd.val⟩ : TangentBundle I X)) inferInstance
    ∃ e : Bundle.Trivialization (Fin r → ℝ)
        (Bundle.TotalSpace.proj (F := Fin r → ℝ)
          (E := fun y : X ↦ ↥(toDistribution y))),
      x ∈ e.baseSet ∧ e.IsLinear ℝ

variable {I : ModelWithCorners ℝ E H}
variable {X : Type*} [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ∞ X]

/-- A splitting `TX = E^s ⊕ E^u` into two continuous subbundles, each invariant under the
derivative of the diffeomorphism `g`. -/
structure InvariantRealTangentSplitting (g : Diffeomorph I I X X ∞) where
  /-- The stable subbundle `E^s`. -/
  stable : ContinuousRealTangentSubbundle I X
  /-- The unstable subbundle `E^u`. -/
  unstable : ContinuousRealTangentSubbundle I X
  /-- `E^s_x ⊕ E^u_x = T_x X` at every point. -/
  isCompl : ∀ x, IsCompl (stable.toDistribution x) (unstable.toDistribution x)
  /-- `Dg_x (E^s_x) = E^s_{g x}`. -/
  stable_map : ∀ x,
    (stable.toDistribution x).map (mfderiv I I g x).toLinearMap =
      stable.toDistribution (g x)
  /-- `Dg_x (E^u_x) = E^u_{g x}`. -/
  unstable_map : ∀ x,
    (unstable.toDistribution x).map (mfderiv I I g x).toLinearMap =
      unstable.toDistribution (g x)

end RealTangentBundles

section Iterates

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type v} [TopologicalSpace H]
variable {X : Type*} [TopologicalSpace X] [ChartedSpace H X]

/-- The `n`-th iterate `g^n` of a diffeomorphism, as a diffeomorphism. -/
def realIterate (I : ModelWithCorners ℝ E H)
    (g : Diffeomorph I I X X ∞) (n : ℕ) : Diffeomorph I I X X ∞ :=
  { toEquiv :=
      { toFun := (g : X → X)^[n]
        invFun := (g.symm : X → X)^[n]
        left_inv := g.left_inv.iterate n
        right_inv := g.right_inv.iterate n }
    contMDiff_toFun := g.contMDiff_toFun.iterate n
    contMDiff_invFun := g.symm.contMDiff_toFun.iterate n }

end Iterates

section IterateDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H}
variable {X : Type*} [TopologicalSpace X] [ChartedSpace H X]

/-- A distribution invariant under `Dg` is invariant under `D(g^n)` for every `n`. -/
theorem real_distribution_iterate_invariant
    (g : Diffeomorph I I X X ∞) (P : RealTangentDistribution I X)
    (hP : ∀ x, (P x).map (mfderiv I I g x).toLinearMap = P (g x))
    (n : ℕ) (x : X) :
    (P x).map (mfderiv I I ((g : X → X)^[n]) x).toLinearMap =
      P (((g : X → X)^[n]) x) := by
  induction n generalizing x with
  | zero =>
    simp only [Function.iterate_zero, mfderiv_id, ContinuousLinearMap.coe_id]
    exact Submodule.map_id (P x)
  | succ n ih =>
    rw [Function.iterate_succ, mfderiv_comp x
      ((g.contMDiff.iterate n).mdifferentiableAt (by simp))
      (g.contMDiff.mdifferentiableAt (by simp)),
      ContinuousLinearMap.toLinearMap_comp, Submodule.map_comp, hP x]
    exact ih (g x)

/-- The restriction `D(g^n)_x : P_x → P_{g^n x}` of the derivative of `g^n` to an invariant
distribution `P`. -/
def restrictedIterateDerivative
    (g : Diffeomorph I I X X ∞) (P : RealTangentDistribution I X)
    (hP : ∀ x, (P x).map (mfderiv I I g x).toLinearMap = P (g x))
    (n : ℕ) (x : X) :
    ↥(P x) ≃L[ℝ] ↥(P (((g : X → X)^[n]) x)) :=
  ((realIterate I g n).mfderivToContinuousLinearEquiv (by simp) x).ofSubmodules
    (P x) (P (((g : X → X)^[n]) x))
    (real_distribution_iterate_invariant g P hP n x)

end IterateDerivative

section ComplexGeometry

/- In the library, `restrictedIterateDerivative` above and `complexTangentToReal` below live in
different files, and each gets its own copy of one auxiliary proof. Inside one file Lean would
reuse the first copy, so its cache of auxiliary proofs is cleared once here. -/
run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}

/- The definitions below were written in an environment without Mathlib's C*-algebra
instances on `ℂ` (and, for the most basic ones, without its inner-product instances on `ℂ`).
Those instances give a second, definitionally equal, route to the normed structure of `ℂ^d`;
they are switched off here so that every definition elaborates to the same term as in the
library that proves the theorems. -/
attribute [-instance] instCommCStarAlgebraComplex instNonUnitalCStarAlgebraForall

/-! ## Complex manifolds -/

section ComplexManifolds

section Models

attribute [-instance] RCLike.innerProductSpace RCLike.toInnerProductSpaceReal
  instInnerProductSpaceRealComplex

/-- The model space `ℂ^d`. -/
abbrev ComplexModel (d : ℕ) := Fin d → ℂ

/-- `ℂ^d` as the model of complex manifolds of dimension `d`. -/
abbrev complexModel (d : ℕ) :
    ModelWithCorners ℂ (ComplexModel d) (ComplexModel d) :=
  modelWithCornersSelf ℂ (ComplexModel d)

/-- `ℂ^d = ℝ^{2d}` as the model of the underlying real manifolds. -/
abbrev realModel (d : ℕ) :
    ModelWithCorners ℝ (ComplexModel d) (ComplexModel d) :=
  modelWithCornersSelf ℝ (ComplexModel d)

/-- A complex-linear endomorphism of `ℂ^d` is hyperbolic if no eigenvalue has modulus `1`. -/
def ComplexLinearHyperbolic {d : ℕ}
    (A : Module.End ℂ (ComplexModel d)) : Prop :=
  ∀ μ : ℂ, Module.End.HasEigenvalue A μ → ‖μ‖ ≠ 1

/-- A biholomorphism between complex manifolds of dimensions `d` and `e`. -/
abbrev Biholomorph (d e : ℕ) (X : Type u) (Y : Type v)
    [TopologicalSpace X] [ChartedSpace (ComplexModel d) X]
    [TopologicalSpace Y] [ChartedSpace (ComplexModel e) Y] :=
  Diffeomorph (complexModel d) (complexModel e) X Y ∞

/-- A complex manifold is a smooth real manifold on the same charts. -/
theorem complex_isManifold_real (d : ℕ) (X : Type u)
    [TopologicalSpace X] [ChartedSpace (ComplexModel d) X]
    [IsManifold (complexModel d) ∞ X] :
    IsManifold (realModel d) ∞ X := by
  apply isManifold_of_contDiffOn (realModel d) ∞ X
  intro e e' he he'
  have h := (contDiffGroupoid ∞ (complexModel d)).compatible he he'
  exact ContDiffOn.restrict_scalars ℝ (mem_groupoid_of_pregroupoid.mp h).1

/-- A holomorphic map is smooth as a map of the underlying real manifolds. -/
theorem contMDiff_complex_to_real {d e : ℕ} {X : Type u} {Y : Type v}
    [TopologicalSpace X] [ChartedSpace (ComplexModel d) X]
    [TopologicalSpace Y] [ChartedSpace (ComplexModel e) Y]
    {n : ℕ∞ω} {f : X → Y}
    (hf : ContMDiff (complexModel d) (complexModel e) n f) :
    ContMDiff (realModel d) (realModel e) n f := by
  intro x
  obtain ⟨hc, hd⟩ := contMDiffAt_iff.mp (hf x)
  exact contMDiffAt_iff.mpr ⟨hc, hd.restrict_scalars ℝ⟩

end Models

/-- The complex tangent space as a real vector space. -/
instance complexTangentRealModule (d : ℕ) {X : Type u}
    [TopologicalSpace X] [ChartedSpace (ComplexModel d) X] (x : X) :
    Module ℝ (TangentSpace (complexModel d) x) :=
  Module.restrictScalars ℝ ℂ (TangentSpace (complexModel d) x)

instance complexTangentScalarTower (d : ℕ) {X : Type u}
    [TopologicalSpace X] [ChartedSpace (ComplexModel d) X] (x : X) :
    IsScalarTower ℝ ℂ (TangentSpace (complexModel d) x) :=
  IsScalarTower.restrictScalars ℝ ℂ (TangentSpace (complexModel d) x)

/-- The identification of the complex tangent space `T_x X` with the real tangent space of
the underlying real manifold. -/
def complexTangentToReal (d : ℕ) {X : Type u}
    [TopologicalSpace X] [ChartedSpace (ComplexModel d) X] (x : X) :
    TangentSpace (complexModel d) x ≃L[ℝ] TangentSpace (realModel d) x :=
  let e := tangentSpaceCastModel (complexModel d) x
  let eReal : TangentSpace (complexModel d) x ≃L[ℝ] ComplexModel d :=
    { toLinearEquiv := e.toLinearEquiv.restrictScalars ℝ
      continuous_toFun := e.continuous
      continuous_invFun := e.symm.continuous }
  eReal.trans (tangentSpaceCastModel (realModel d) x).symm

/-- A biholomorphism as a diffeomorphism of the underlying real manifolds. -/
def Biholomorph.toReal {d e : ℕ} {X : Type u} {Y : Type v}
    [TopologicalSpace X] [ChartedSpace (ComplexModel d) X]
    [TopologicalSpace Y] [ChartedSpace (ComplexModel e) Y]
    (f : Biholomorph d e X Y) :
    Diffeomorph (realModel d) (realModel e) X Y ∞ :=
  { toEquiv := f.toEquiv
    contMDiff_toFun := contMDiff_complex_to_real f.contMDiff
    contMDiff_invFun := contMDiff_complex_to_real f.symm.contMDiff }

/-- A compact connected complex manifold of dimension `d` (Hausdorff, second countable). -/
class IsCompactComplexManifold (d : ℕ) (X : Type u)
    [TopologicalSpace X] [ChartedSpace (ComplexModel d) X] : Prop
    extends T2Space X, SecondCountableTopology X, CompactSpace X, ConnectedSpace X,
      IsManifold (complexModel d) ∞ X

end ComplexManifolds

/-! ## Complex tori -/

section ComplexTori

/- `import Mathlib` also brings in a charted-space instance for sheaves of manifolds, which
the library module defining the torus charts did not import; it is switched off so that the
charts below elaborate as in the library. -/
attribute [-instance] TopCat.of.chartedSpace

/-- A full lattice `Λ ⊂ ℂ^d`: a discrete subgroup spanning `ℂ^d` over `ℝ`. -/
structure FullComplexLattice (d : ℕ) where
  lattice : Submodule ℤ (ComplexModel d)
  discrete : DiscreteTopology lattice
  full : letI := discrete; IsZLattice ℝ lattice

/-- The complex torus `ℂ^d / Λ`. -/
abbrev ComplexTorus {d : ℕ} (L : FullComplexLattice d) :=
  ComplexModel d ⧸ L.lattice.toAddSubgroup

/-- The projection `ℂ^d → ℂ^d / Λ` is a covering map. -/
theorem torus_quotient_covering {d : ℕ} (L : FullComplexLattice d) :
    IsAddQuotientCoveringMap
      (QuotientAddGroup.mk : ComplexModel d → ComplexTorus L) L.lattice.toAddSubgroup := by
  have : DiscreteTopology L.lattice := L.discrete
  exact AddSubgroup.isAddQuotientCoveringMap_of_comm _ DiscreteTopology.isDiscrete

/-- The complex manifold structure on `ℂ^d / Λ`, with charts the local inverses of the
projection. -/
instance complexTorusChartedSpace {d : ℕ} (L : FullComplexLattice d) :
    ChartedSpace (ComplexModel d) (ComplexTorus L) :=
  (torus_quotient_covering L).isLocalHomeomorph.chartedSpace
    (H := ComplexModel d) (torus_quotient_covering L).surjective

/-- A complex-linear automorphism `A` of `ℂ^d` with `A(Λ) = Λ`. -/
structure LatticeLinearEquiv {d : ℕ} (L : FullComplexLattice d) where
  linear : ComplexModel d ≃ₗ[ℂ] ComplexModel d
  map_lattice : L.lattice.toAddSubgroup.map linear.toAddEquiv.toAddMonoidHom =
    L.lattice.toAddSubgroup

/-- The automorphism of `ℂ^d / Λ` induced by `A`. -/
def quotientLinearEquiv {d : ℕ} {L : FullComplexLattice d}
    (A : LatticeLinearEquiv L) : ComplexTorus L ≃+ ComplexTorus L :=
  QuotientAddGroup.congr L.lattice.toAddSubgroup L.lattice.toAddSubgroup
    A.linear.toAddEquiv A.map_lattice

end ComplexTori

/-! ## Holomorphic subbundles -/

section HolomorphicSubbundles

/-- Every fibre `S_x` is a complex line of `T_x X`, i.e. `S` has complex rank one. -/
def HasComplexRankOne {d : ℕ} {X : Type u}
    [TopologicalSpace X] [ChartedSpace (ComplexModel d) X]
    (S : RealTangentDistribution (realModel d) X) : Prop :=
  ∀ x : X, ∃ K : Submodule ℂ (TangentSpace (complexModel d) x),
    Module.finrank ℂ K = 1 ∧
      (K.restrictScalars ℝ).map
        (complexTangentToReal d x).toLinearEquiv.toLinearMap = S x

/-- `s₁, …, s_r` are holomorphic vector fields on the open set `U`, linearly independent over
`ℂ` at every point of `U`. -/
def IsHolomorphicTangentFrame {d r : ℕ} {X : Type u}
    [TopologicalSpace X] [ChartedSpace (ComplexModel d) X]
    [IsManifold (complexModel d) ∞ X]
    (U : Set X) (s : Fin r → (y : X) → TangentSpace (complexModel d) y) : Prop :=
  IsOpen U ∧
    (∀ i, ContMDiffOn (complexModel d) (complexModel d).tangent ∞
      (fun y ↦ (⟨y, s i y⟩ : TangentBundle (complexModel d) X)) U) ∧
    ∀ y ∈ U, LinearIndependent ℂ (fun i ↦ s i y)

/-- `P` is a holomorphic subbundle of rank `r` of the holomorphic tangent bundle: near every
point it is spanned by a holomorphic frame of `r` vector fields. -/
def IsHolomorphicTangentSubbundle {d : ℕ} {X : Type u}
    [TopologicalSpace X] [ChartedSpace (ComplexModel d) X]
    [IsManifold (complexModel d) ∞ X]
    (r : ℕ) (P : (x : X) → Submodule ℂ (TangentSpace (complexModel d) x)) : Prop :=
  ∀ x : X, ∃ (U : Set X) (s : Fin r → (y : X) → TangentSpace (complexModel d) y),
    x ∈ U ∧ IsHolomorphicTangentFrame U s ∧
      ∀ y ∈ U, Submodule.span ℂ (Set.range (fun i ↦ s i y)) = P y

end HolomorphicSubbundles

/-! ## Anosov diffeomorphisms and toral models -/

section Anosov

open scoped Bundle

attribute [local instance] complex_isManifold_real

/-- `f` is Anosov: there are a Riemannian metric, an invariant splitting `TX = E^s ⊕ E^u` and
an iterate `k ≥ 1` such that `Df^k` contracts `E^s` and `Df^{-k}` contracts `E^u`. -/
structure AnosovDatum {d : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (ComplexModel d) X]
    [IsManifold (complexModel d) ∞ X]
    (f : Biholomorph d d X X) where
  /-- A smooth Riemannian metric on `X`. -/
  metric : Bundle.ContMDiffRiemannianMetric (realModel d) ∞ (ComplexModel d)
    (fun x : X ↦ TangentSpace (realModel d) x)
  /-- The invariant splitting `TX = E^s ⊕ E^u`. -/
  splitting : InvariantRealTangentSplitting f.toReal
  /-- The iterate `k`. -/
  k : ℕ
  one_le_k : 1 ≤ k
  /-- `‖Df^k|E^s‖ < 1`. -/
  stable_contracting :
    letI : Bundle.RiemannianBundle (fun x : X ↦ TangentSpace (realModel d) x) :=
      ⟨metric.toRiemannianMetric⟩
    ∀ x, ‖(restrictedIterateDerivative f.toReal splitting.stable.toDistribution
      splitting.stable_map k x).toContinuousLinearMap‖ < 1
  /-- `‖Df^{-k}|E^u‖ < 1`. -/
  unstable_contracting :
    letI : Bundle.RiemannianBundle (fun x : X ↦ TangentSpace (realModel d) x) :=
      ⟨metric.toRiemannianMetric⟩
    ∀ x, ‖(restrictedIterateDerivative f.toReal splitting.unstable.toDistribution
      splitting.unstable_map k x).symm.toContinuousLinearMap‖ < 1

end Anosov

section ToralModels

/-- The automorphism of the real torus `ℝ^n / ℤ^n` induced by `A ∈ GL(n, ℤ)`. -/
def integralToralMap {n : ℕ}
    (A : Matrix.GeneralLinearGroup (Fin n) ℤ)
    (x : UnitAddTorus (Fin n)) : UnitAddTorus (Fin n) :=
  fun i ↦ ∑ j : Fin n, A i j • x j

/-- `f` is topologically conjugate to a hyperbolic automorphism of the real torus `ℝ^n / ℤ^n`. -/
def HyperbolicRealToralConjugacy (n : ℕ) (X : Type u) [TopologicalSpace X]
    (f : X → X) : Prop :=
  ∃ (A : Matrix.GeneralLinearGroup (Fin n) ℤ) (h : X ≃ₜ UnitAddTorus (Fin n)),
    (∀ μ : ℂ,
      Module.End.HasEigenvalue
        (Matrix.mulVecLin (fun i j : Fin n ↦ (A i j : ℂ))) μ → ‖μ‖ ≠ 1) ∧
    ∀ x : X, h (f x) = integralToralMap A (h x)

/-- `f` is biholomorphically conjugate to a hyperbolic linear automorphism of a complex torus. -/
def HasHyperbolicComplexTorusModel {d : ℕ} {X : Type u}
    [TopologicalSpace X] [ChartedSpace (ComplexModel d) X] (f : X → X) : Prop :=
  ∃ (L : FullComplexLattice d) (A : LatticeLinearEquiv L)
    (h : Biholomorph d d X (ComplexTorus L)),
    ComplexLinearHyperbolic A.linear.toLinearMap ∧
      Function.Semiconj (fun x ↦ h x) f (fun t ↦ quotientLinearEquiv A t)

end ToralModels

end ComplexGeometry

/-! ## Homotopy-torus rigidity -/

section Rigidity

/-- A closed (compact, boundaryless) smooth real manifold of dimension `n`. -/
class ClosedSmoothRealManifold (n : outParam ℕ) (M : Type u)
    [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] : Prop where
  [compactSpace : CompactSpace M]
  [t2Space : T2Space M]
  [secondCountableTopology : SecondCountableTopology M]
  [isManifold :
    IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ∞ M]

/-- Homotopy-torus rigidity: for `n ≥ 5`, every closed smooth `n`-manifold homotopy equivalent
to the torus `T^n` is homeomorphic to `T^n`. -/
def HomotopyTorusRigidity : Prop :=
  ∀ (n : ℕ),
    5 ≤ n →
      ∀ (M : Type u) [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin n)) M],
        ClosedSmoothRealManifold n M →
          Nonempty (ContinuousMap.HomotopyEquiv M (UnitAddTorus (Fin n))) →
            Nonempty (Homeomorph M (UnitAddTorus (Fin n)))

end Rigidity

/-! ## The main theorems -/

section MainTheorems

attribute [local instance] complex_isManifold_real

/-- Theorem A. A holomorphic Anosov diffeomorphism of a compact connected complex manifold
whose stable or unstable bundle has complex rank one is biholomorphically conjugate to a
hyperbolic linear automorphism of a complex torus (assuming homotopy-torus rigidity). -/
theorem zhang_theorem_A {d : ℕ} {X : Type u}
    [TopologicalSpace X] [ChartedSpace (ComplexModel d) X]
    [IsCompactComplexManifold d X]
    (f : Biholomorph d d X X) (a : AnosovDatum f)
    (hcodim : HasComplexRankOne a.splitting.stable.toDistribution ∨
      HasComplexRankOne a.splitting.unstable.toDistribution)
    (HS : HomotopyTorusRigidity.{u}) :
    HasHyperbolicComplexTorusModel (d := d) (fun x ↦ f x) := by
  sorry

/-- Theorem 1.1. If `d ≥ 2` and the stable bundle has complex rank one, then `f` is
topologically conjugate to a hyperbolic automorphism of the real torus `T^{2d}`
(assuming homotopy-torus rigidity). -/
theorem zhang_theorem_1_1 {d : ℕ} {X : Type u}
    [TopologicalSpace X] [ChartedSpace (ComplexModel d) X]
    [IsCompactComplexManifold d X]
    (hd : 2 ≤ d) (f : Biholomorph d d X X) (a : AnosovDatum f)
    (hstable : HasComplexRankOne a.splitting.stable.toDistribution)
    (HS : HomotopyTorusRigidity.{u}) :
    HyperbolicRealToralConjugacy (2 * d) X (fun x ↦ f x) := by
  sorry

/-- Theorem 1.2. If `X` is homeomorphic to a torus and both `E^s` and `E^u` are holomorphic
subbundles of the tangent bundle, then `f` is biholomorphically conjugate to a linear
automorphism of a complex torus. -/
theorem zhang_theorem_1_2 {d : ℕ} {X : Type u}
    [TopologicalSpace X] [ChartedSpace (ComplexModel d) X]
    [IsCompactComplexManifold d X]
    (f : Biholomorph d d X X) (a : AnosovDatum f)
    (hStable : ∃ (r : ℕ) (P : (x : X) → Submodule ℂ (TangentSpace (complexModel d) x)),
      IsHolomorphicTangentSubbundle r P ∧ ∀ x : X,
        ((P x).restrictScalars ℝ).map
          (complexTangentToReal d x).toLinearEquiv.toLinearMap =
            a.splitting.stable.toDistribution x)
    (hUnstable : ∃ (r : ℕ) (P : (x : X) → Submodule ℂ (TangentSpace (complexModel d) x)),
      IsHolomorphicTangentSubbundle r P ∧ ∀ x : X,
        ((P x).restrictScalars ℝ).map
          (complexTangentToReal d x).toLinearEquiv.toLinearMap =
            a.splitting.unstable.toDistribution x)
    (hT : ∃ n : ℕ, Nonempty (X ≃ₜ UnitAddTorus (Fin n))) :
    ∃ (L : FullComplexLattice d) (A : LatticeLinearEquiv L)
      (h : Biholomorph d d X (ComplexTorus L)),
      Function.Semiconj (fun x ↦ h x) (fun x ↦ f x)
        (fun t ↦ quotientLinearEquiv A t) := by
  sorry

/-- Theorem 1.3. If the stable bundle has complex rank one, then `E^s` and `E^u` are holomorphic
subbundles of the tangent bundle, of ranks `1` and `d - 1` (assuming homotopy-torus
rigidity). -/
theorem zhang_theorem_1_3 {d : ℕ} {X : Type u}
    [TopologicalSpace X] [ChartedSpace (ComplexModel d) X]
    [IsCompactComplexManifold d X]
    (f : Biholomorph d d X X) (a : AnosovDatum f)
    (hstable : HasComplexRankOne a.splitting.stable.toDistribution)
    (HS : HomotopyTorusRigidity.{u}) :
    ∃ S U : (x : X) → Submodule ℂ (TangentSpace (complexModel d) x),
      (∀ x, ((S x).restrictScalars ℝ).map
        (complexTangentToReal d x).toLinearEquiv.toLinearMap =
          a.splitting.stable.toDistribution x) ∧
      (∀ x, ((U x).restrictScalars ℝ).map
        (complexTangentToReal d x).toLinearEquiv.toLinearMap =
          a.splitting.unstable.toDistribution x) ∧
      IsHolomorphicTangentSubbundle 1 S ∧ IsHolomorphicTangentSubbundle (d - 1) U := by
  sorry

end MainTheorems

end HolomorphicAnosov
