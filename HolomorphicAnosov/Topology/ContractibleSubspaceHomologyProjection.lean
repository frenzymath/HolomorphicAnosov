import HolomorphicAnosov.Topology.Homology.ContractibleSingularHomology
import HolomorphicAnosov.Topology.SingularSubspaceSubcomplex

/-!
# Relative homology projection for a contractible subspace

Source: Hatcher, *Algebraic Topology*, Corollary 2.11 p.112 and Theorem 2.16,
pp.116–118. Ordinary positive-degree homology of a space agrees with its
homology relative to a nonempty contractible subspace.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace HolomorphicAnosov

/-- For a contractible subspace, inclusion is split injective on every ordinary
homology group. The constant map back to a contraction point splits it on
homology, since its restriction is homotopic to the identity.

Source: Hatcher Corollary 2.11 p.112, applied to the contraction homotopy.
-/
theorem contractible_subspace_inclusion_homology_mono
    (X : TopCat.{0}) (A : Set X) [ContractibleSpace A]
    (R : ModuleCat.{0} ℤ) (n : ℕ) :
    Mono (SSet.homologyMap (singularSubspacePair X A).hom R n) := by
  obtain ⟨a, ⟨H⟩⟩ := id_nullhomotopic A
  let F := (AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) n).obj R
  let i := singularSubspaceInclusion X A
  let r : X ⟶ TopCat.of A := TopCat.ofHom (ContinuousMap.const X a)
  have h : F.map (𝟙 (TopCat.of A)) = F.map (i ≫ r) :=
    TopCat.Homotopy.congr_homologyMap_singularChainComplexFunctor
      (f := 𝟙 (TopCat.of A)) (g := i ≫ r) H R n
  rw [F.map_id, F.map_comp] at h
  exact mono_of_mono_fac h.symm

/-- The actual relative projection is an isomorphism in each positive degree
when its distinguished subspace is contractible.

Source: Hatcher Theorem 2.16 pp.116–118 and Corollary 2.11 p.112. Contractibility
annihilates the positive-degree homology of the subspace, so exactness makes
the projection injective. In every preceding degree, including degree zero,
inclusion of the contractible subspace is split injective: a constant map back
to its contraction point induces a retraction on homology. Thus the connecting
map is zero, and exactness makes the projection surjective. An isomorphism
follows in the abelian category of integral modules. The argument does not
claim that ordinary degree-zero homology of a contractible space vanishes.
-/
theorem contractible_subspace_homology_projection_isIso
    (X : TopCat.{0}) (A : Set X) [ContractibleSpace A]
    (R : ModuleCat.{0} ℤ) (n : ℕ) (hn : 0 < n) :
    IsIso ((singularSubspacePair X A).homologyπ R n) := by
  let P := singularSubspacePair X A
  have hz : IsZero (P.left.homology R n) :=
    singular_homology_isZero_of_contractible (TopCat.of A) R n (Nat.ne_of_gt hn)
  have : Mono (P.homologyπ R n) := (P.homology_exact₂ R n).mono_g (hz.eq_of_src _ _)
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  have : Mono (SSet.homologyMap P.hom R m) :=
    contractible_subspace_inclusion_homology_mono X A R m
  have hd : P.homologyδ R (m + 1) m = 0 := by
    apply (cancel_mono (SSet.homologyMap P.hom R m)).mp
    simp
  have : Epi (P.homologyπ R (m + 1)) := (P.homology_exact₃ R (m + 1) m).epi_f hd
  exact isIso_of_mono_of_epi _

end HolomorphicAnosov
