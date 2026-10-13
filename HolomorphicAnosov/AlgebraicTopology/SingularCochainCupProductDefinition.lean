import HolomorphicAnosov.AlgebraicTopology.SingularCochainCohomologyDefinition
import Mathlib.AlgebraicTopology.SimplexCategory.Basic
import Mathlib.Algebra.Module.LinearMap.Basic

/-!
# The singular front/back cochain cup formula

Source: Hatcher, *Algebraic Topology*, p. 206 (front/back cup formula),
p. 207 (constant-one zero-cochain), pp. 209–210 (same-subspace relative
variants); pp. 197–200 (cocycles modulo coboundaries).

The cochains, chain generators, relative kernel complex and homology quotient
are the previously defined genuine singular objects. `cupCochain` is their
literal linear extension from the singular simplex generators. It has no
assumed algebra laws or admitted data. The laws and quotient descent belong
to `topo.singular_cup_product_laws_g3`.
-/

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

universe u
noncomputable section
namespace HolomorphicAnosov.SingularCochain

/-- The ordered front face [0,…,p]. Source: Hatcher, cup formula p. 206. -/
def cupFront (p q : ℕ) : ⦋p⦌ ⟶ ⦋p + q⦌ :=
  SimplexCategory.mkHom
    { toFun := fun i => ⟨i.val, by omega⟩
      monotone' := fun _ _ h => h }

/-- The ordered back face [p,…,p+q], sharing vertex p with the front face.
Source: Hatcher, cup formula p. 206. -/
def cupBack (p q : ℕ) : ⦋q⦌ ⟶ ⦋p + q⦌ :=
  SimplexCategory.mkHom
    { toFun := fun i => ⟨p + i.val, by omega⟩
      monotone' := fun _ _ h => Nat.add_le_add_left h p }

variable (R : Type u) [CommRing R]

/-- Evaluate a cochain on a singular simplex with coefficient 1.
Source: Hatcher, pp. 197–198 and 206; Mathlib's canonical free-chain generator. -/
def simplexValue (X : TopCat.{u}) {n : ℕ} (a : cochains R X n)
    (σ : (TopCat.toSSet.obj X) _⦋n⦌) : R :=
  a.hom (((TopCat.toSSet.obj X).ιChainComplex (R := ModuleCat.of R R) σ).hom 1)

/-- The actual singular cup cochain, linearly extended from the front/back
formula on free-chain generators. Source: Hatcher, p. 206. -/
def cupCochain (X : TopCat.{u}) {p q : ℕ}
    (a : cochains R X p) (b : cochains R X q) : cochains R X (p + q) :=
  Sigma.desc fun (σ : (TopCat.toSSet.obj X) _⦋p + q⦌) =>
    ModuleCat.ofHom (LinearMap.mulLeft R
      (simplexValue R X a ((TopCat.toSSet.obj X).map (cupFront p q).op σ) *
       simplexValue R X b ((TopCat.toSSet.obj X).map (cupBack p q).op σ)))

/-- The degree-zero cochain assigning 1 to each singular zero-simplex.
Source: Hatcher, p. 207. -/
def oneCochain (X : TopCat.{u}) : cochains R X 0 :=
  Sigma.desc fun (_ : (TopCat.toSSet.obj X) _⦋0⦌) => 𝟙 (ModuleCat.of R R)

/-- The literal canonical projection of a cocycle to its kernel/image quotient.
Source: Hatcher, pp. 197–200. -/
def cocycleClass (Q : CochainComplex (ModuleCat.{u} R) ℕ) (n : ℕ) :
    cycles R Q n →ₗ[R] quotient R Q n :=
  (Q.sc n).moduleCatLeftHomologyData.π.hom

/-- Uniform notation for the two existing complexes: false means ordinary,
true means relative to A. Source: Hatcher, pp. 199–200 and 209–210. -/
def cupComplex (X : TopCat.{u}) (A : Set X) (relative : Bool) :
    CochainComplex (ModuleCat.{u} R) ℕ :=
  if relative then relativeComplex R X A else complex R X

/-- The canonical inclusion of ordinary or relative cochains into ordinary
cochains. Source: Hatcher, pp. 199–200. -/
def cupInclusion (X : TopCat.{u}) (A : Set X) (relative : Bool) :
    cupComplex R X A relative ⟶ complex R X :=
  match relative with
  | false => 𝟙 _
  | true => kernel.ι (pullback R (subspaceInclusion X A))

/-- Ordinary or relative singular cohomology, with the same Boolean notation.
Source: Hatcher, pp. 197–200; this is the literal existing quotient. -/
abbrev cupCohomology (X : TopCat.{u}) (A : Set X) (relative : Bool) (n : ℕ) :=
  quotient R (cupComplex R X A relative) n

end HolomorphicAnosov.SingularCochain
