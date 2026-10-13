import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Homology.Opposite
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.CategoryTheory.Linear.Yoneda

/-!
# Ordinary and relative singular cochains and cohomology

Source: Hatcher, *Algebraic Topology*, pp. 197--198 (cochains and coboundary),
pp. 199--200 (relative cochains), and p. 201 (pullback).
This is the definition node `topo.singular_cochain_cohomology_definition_g3`.

The chain object is Mathlib's unaugmented singular simplicial-set chain complex
with coefficient object `R` in `ModuleCat R`. Thus it is the free R-module on
the original continuous singular simplices, with the alternating face boundary.
Linear Yoneda sends an opposite module to its actual R-linear maps into R.
Applying it to the opposite chain complex therefore gives precisely
`δ(a) = a ∘ ∂`. Its differential-square and map laws are supplied by Mathlib's
existing functors, with no admitted data or proof.

Cohomology below is the literal module quotient of the outgoing kernel by
the range of the incoming differential restricted to that kernel. At degree
zero the incoming differential is zero by the unaugmented up-shape convention.
Relative cochains are the kernel complex of restriction to the subspace A:
equivalently they vanish on the R-submodule spanned by simplices in A.
The kernel complex uses the same coboundary, restricted by the chain-map law.
No topology on the coefficient ring and no finiteness assumption is used.
-/

open CategoryTheory CategoryTheory.Limits Opposite

universe u

noncomputable section

namespace HolomorphicAnosov.SingularCochain

variable (R : Type u) [CommRing R]

/-- The actual unaugmented singular R-chain functor. Source: Hatcher, pp. 197--198;
Mathlib `AlgebraicTopology.singularChainComplexFunctor`. -/
abbrev chainFunctor : TopCat.{u} ⥤ ChainComplex (ModuleCat.{u} R) ℕ :=
  (AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{u} R)).obj (ModuleCat.of R R)

/-- Transpose a chain complex by applying Hom_R(-,R) degreewise.
Source: Hatcher, pp. 197--198. The opposite reverses the differential shape,
and linear Yoneda acts by precomposition; functoriality supplies δ²=0. -/
def dualFunctor : (ChainComplex (ModuleCat.{u} R) ℕ)ᵒᵖ ⥤
    CochainComplex (ModuleCat.{u} R) ℕ :=
  HomologicalComplex.opFunctor (ModuleCat.{u} R) (ComplexShape.down ℕ) ⋙
    (((linearYoneda R (ModuleCat.{u} R)).obj (ModuleCat.of R R)).mapHomologicalComplex
      (ComplexShape.up ℕ))

/-- Ordinary singular cochains, contravariantly functorial in the original space.
Source: Hatcher, pp. 197--198 and 201. -/
def cochainFunctor : TopCat.{u}ᵒᵖ ⥤ CochainComplex (ModuleCat.{u} R) ℕ :=
  (chainFunctor R).op ⋙ dualFunctor R

/-- The singular cochain complex of X. Source: Hatcher, pp. 197--198. -/
abbrev complex (X : TopCat.{u}) := (cochainFunctor R).obj (op X)

/-- Degree-n singular cochains Hom_R(C_n(X;R),R).
Source: Hatcher, pp. 197--198. -/
abbrev cochains (X : TopCat.{u}) (n : ℕ) := (complex R X).X n

/-- The coboundary δ_n(a)=a∘∂_(n+1).
Source: Hatcher, pp. 197--198. -/
abbrev coboundary (X : TopCat.{u}) (n : ℕ) :
    cochains R X n ⟶ cochains R X (n + 1) :=
  (complex R X).d n (n + 1)

/-- A continuous map pulls a cochain back by precomposition with its chain map.
Source: Hatcher, p. 201. -/
abbrev pullback {X Y : TopCat.{u}} (f : X ⟶ Y) : complex R Y ⟶ complex R X :=
  (cochainFunctor R).map f.op

/-- The outgoing kernel in degree n. Source: Hatcher, p. 198. -/
abbrev cycles (Q : CochainComplex (ModuleCat.{u} R) ℕ) (n : ℕ) :=
  LinearMap.ker (Q.sc n).g.hom

/-- The incoming image, regarded as a submodule of cycles.
Source: Hatcher, p. 198. Mathlib's short-complex equation gives the restriction. -/
abbrev boundaries (Q : CochainComplex (ModuleCat.{u} R) ℕ) (n : ℕ) :=
  (Q.sc n).moduleCatToCycles.range

/-- The literal quotient Zⁿ/Bⁿ for a cochain complex.
Source: Hatcher, pp. 197--198; Mathlib's explicit module homology data. -/
abbrev quotient (Q : CochainComplex (ModuleCat.{u} R) ℕ) (n : ℕ) : ModuleCat.{u} R :=
  (Q.sc n).moduleCatLeftHomologyData.H

/-- The map induced on the actual kernel/image quotient by a cochain map.
Source: Hatcher, p. 201. The two canonical module-homology isomorphisms identify
Mathlib's homology functor with this same explicit quotient. -/
def quotientMap {Q Q' : CochainComplex (ModuleCat.{u} R) ℕ} (f : Q ⟶ Q') (n : ℕ) :
    quotient R Q n ⟶ quotient R Q' n :=
  (Q.sc n).moduleCatHomologyIso.inv ≫ HomologicalComplex.homologyMap f n ≫
    (Q'.sc n).moduleCatHomologyIso.hom

/-- Ordinary singular Hⁿ(X;R). Source: Hatcher, pp. 197--198. -/
abbrev cohomology (X : TopCat.{u}) (n : ℕ) := quotient R (complex R X) n

/-- The contravariant induced map f*:Hⁿ(Y;R)→Hⁿ(X;R).
Source: Hatcher, p. 201. -/
abbrev cohomologyPullback {X Y : TopCat.{u}} (f : X ⟶ Y) (n : ℕ) :
    cohomology R Y n ⟶ cohomology R X n :=
  quotientMap R (pullback R f) n

/-- The inclusion of A with its inherited subspace topology.
Source: Hatcher, pp. 199--200. -/
def subspaceInclusion (X : TopCat.{u}) (A : Set X) : TopCat.of A ⟶ X :=
  TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

/-- Relative singular cochains are the kernel of restriction to A, hence the
cochains vanishing on all singular chains in A. Source: Hatcher, pp. 199--200.
Limits of complexes and the module kernel are computed degreewise, so this
has the inherited coboundary rather than a different relative differential. -/
def relativeComplex (X : TopCat.{u}) (A : Set X) : CochainComplex (ModuleCat.{u} R) ℕ :=
  kernel (pullback R (subspaceInclusion X A))

/-- Relative singular Hⁿ(X,A;R), the same kernel/image quotient of the relative
cochain complex. Source: Hatcher, pp. 199--200. -/
abbrev relativeCohomology (X : TopCat.{u}) (A : Set X) (n : ℕ) :=
  quotient R (relativeComplex R X A) n

end HolomorphicAnosov.SingularCochain
