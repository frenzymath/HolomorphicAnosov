import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.AlgebraicTopology.SimplicialSet.Homology.Relative
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Module.ULift
import Mathlib.Data.ZMod.Basic
import Mathlib.Topology.Category.TopCat.EpiMono

/-!
# Ordinary mod-two singular homology with prescribed support

Source: Hatcher, *Algebraic Topology*, singular chains and boundary p.108,
relative quotient chains p.115, maps of pairs p.118, coefficients p.153, and
support notation `H_k(X,X\A)` pp.233–235. This is the literal Mathlib
singular simplicial-set relative chain complex in modules over `ZMod 2`.
`ULift` adjusts only the universe of the coefficient module.
DAG node: `topo.def_mod2_singular_support_homology_g9`.

For a subset A of X, the pair is the actual singular inclusion of X\A into X,
not a freely supplied homology family. Decreasing the support A to B increases
the complement; the identity on X and that subspace inclusion give the canonical
map of pairs and hence the canonical homology homomorphism. Empty spaces, empty
supports, degree zero and arbitrary topological spaces are permitted. These
are concrete definitions, with no chosen inverse, vanishing or orientation axiom.
-/

noncomputable section

open CategoryTheory

universe u

namespace HolomorphicAnosov.Topology.Homology

/-- The singular pair of an original topological subspace inclusion.

Source: Hatcher pp.108,115,118. The inclusion is continuous and injective;
Mathlib's singular functor preserves its monomorphism. `SSetPair.of` retains
that exact inclusion, with the original subspace topology. -/
def singularSubspacePair (X : Type u) [TopologicalSpace X] (A : Set X) : SSetPair.{u} :=
  let i : TopCat.of A ⟶ TopCat.of X := TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩
  letI : Mono i := (TopCat.mono_iff_injective i).mpr Subtype.val_injective
  SSetPair.of (TopCat.toSSet.map i)

/-- Ordinary relative singular homology of `(X,X\A)` over `ZMod 2`.

Source: Hatcher pp.115,153,233. Mathlib takes the cokernel of the singular chain
inclusion and then its degree-k homology. The coefficient object is the lifted
rank-one module over `ZMod 2`, so the result is an actual mod-two module. -/
abbrev modTwoSupportHomology (X : Type u) [TopologicalSpace X] (A : Set X) (k : ℕ) :=
  (singularSubspacePair X Aᶜ).homology (ModuleCat.of (ZMod 2) (ULift.{u} (ZMod 2))) k

/-- The map of actual singular pairs induced by reverse inclusion of supports.

Source: Hatcher p.118 and support restriction pp.233–235. The complement map
forgets membership and keeps the underlying point; the ambient component is
identity. The commuting square is equality of these original point maps. -/
def singularSupportRestrictionPair (X : Type u) [TopologicalSpace X]
    (A B : Set X) (h : B ⊆ A) :
    singularSubspacePair X Aᶜ ⟶ singularSubspacePair X Bᶜ :=
  SSetPair.homMk
    (TopCat.toSSet.map (TopCat.ofHom
      ⟨fun z ↦ ⟨z.val, fun hz ↦ z.property (h hz)⟩,
        continuous_subtype_val.subtype_mk _⟩))
    (𝟙 _) (by
      simp only [singularSubspacePair]
      rfl)

/-- The canonical support-restriction map on ordinary mod-two singular homology.

Source: Hatcher pp.118,233–235. This is exactly `SSetPair.homologyMap` of the
preceding map of pairs. No assumption on compactness or a basepoint is needed
to define it, and no isomorphism property is asserted by this definition. -/
abbrev modTwoSupportRestriction (X : Type u) [TopologicalSpace X]
    (A B : Set X) (h : B ⊆ A) (k : ℕ) :=
  SSetPair.homologyMap (singularSupportRestrictionPair X A B h)
    (ModuleCat.of (ZMod 2) (ULift.{u} (ZMod 2))) k

end HolomorphicAnosov.Topology.Homology
