import HolomorphicAnosov.Topology.ZeroAugmentShortComplexMap

/-! Source: Hatcher, *Algebraic Topology*, p.118 (augmented relative chains)
and p.124 (collapse naturality). DAG node: `algebra.zero_augment_short_complex_map_homology_is_iso`. -/

noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject
namespace HolomorphicAnosov.GoodPair
universe u

/-- The comparison preserves homology even at degree zero: its first component
is epi, its middle component invertible and its last component mono.
Source: Hatcher p.118 and Mathlib's short-complex homology comparison criterion.
The first and middle components are identities. The last component is identity
in positive degrees and the monomorphism from the zero object at degree zero.
The epi/isomorphism/mono criterion therefore applies in every case. -/
theorem zeroAugmentShortComplexMap_homology_isIso
    (K : ChainComplex (ModuleCat.{u} ℤ) ℕ) (n : ℕ) :
    IsIso (ShortComplex.homologyMap (zeroAugmentShortComplexMap K n)) := by
  apply ShortComplex.isIso_homologyMap_of_epi_of_isIso_of_mono'
  · cases n <;> change Epi (𝟙 _) <;> infer_instance
  · cases n <;> change IsIso (𝟙 _) <;> infer_instance
  · cases n with
    | zero => change Mono (0 : (0 : ModuleCat.{u} ℤ) ⟶ K.X 0); infer_instance
    | succ n => change Mono (𝟙 (K.X n)); infer_instance

end HolomorphicAnosov.GoodPair

