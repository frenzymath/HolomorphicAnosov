import Mathlib.AlgebraicTopology.SimplicialSet.Homology.Relative
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Abelian

/-!
# Ambient chain representatives for relative homology classes

Source: Hatcher, Algebraic Topology, relative chain quotient pp.115–117,
and the finite-chain argument in Lemma 3.27 step (4), pp.237–238.
-/

open CategoryTheory
namespace HolomorphicAnosov
universe u

/-- Every native relative simplicial homology class lifts to an ambient chain
whose boundary comes from the subspace chain complex. Source: Hatcher,
pp.115–117 and Lemma 3.27 step (4), pp.237–238.

Proof: the homology projection is surjective, so choose a cycle representing
the class. The relative quotient is degreewise surjective, so lift that cycle
to an ambient chain. Its boundary maps to zero in the quotient because the
quotient is a chain map and the chosen representative is a cycle. Degreewise
exactness of the subspace–ambient–relative short exact sequence lifts that
boundary to a subspace chain. This works in every degree, including zero. -/
theorem relative_cycle_ambient_representative
    (P : SSetPair.{u}) (R : ModuleCat.{u} ℤ) (i : ℕ)
    (a : (P.homology R i : ModuleCat.{u} ℤ)) :
    ∃ c : ((P.chainComplex R).cycles i : ModuleCat.{u} ℤ),
      ∃ z : ((P.right.chainComplex R).X i : ModuleCat.{u} ℤ),
        (P.chainComplex R).homologyπ i c = a ∧
        (P.chainComplexπ R).f i z = (P.chainComplex R).iCycles i c ∧
        ∀ j : ℕ, ∃ b : ((P.left.chainComplex R).X j : ModuleCat.{u} ℤ),
          (SSet.chainComplexMap P.hom R).f j b = (P.right.chainComplex R).d i j z := by
  obtain ⟨c, hc⟩ := (ModuleCat.epi_iff_surjective
    ((P.chainComplex R).homologyπ i)).mp inferInstance a
  obtain ⟨z, hz⟩ := (ModuleCat.epi_iff_surjective
    ((P.chainComplexπ R).f i)).mp inferInstance ((P.chainComplex R).iCycles i c)
  refine ⟨c, z, hc, hz, ?_⟩
  intro j
  have hzero : (P.chainComplexπ R).f j ((P.right.chainComplex R).d i j z) = 0 := by
    have hcomm := congrArg (fun f ↦ f z) ((P.chainComplexπ R).comm i j)
    change (P.chainComplex R).d i j ((P.chainComplexπ R).f i z) =
      (P.chainComplexπ R).f j ((P.right.chainComplex R).d i j z) at hcomm
    rw [← hcomm, hz]
    exact congrArg (fun f ↦ f c) ((P.chainComplex R).iCycles_d i j)
  have hex := (HomologicalComplex.shortExact_iff_degreewise_shortExact
    (P.chainComplexShortComplex R)).mp (P.shortExact_chainComplexShortComplex R) j
  exact (ShortComplex.moduleCat_exact_iff _).mp hex.exact _ hzero

end HolomorphicAnosov

