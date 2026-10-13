import HolomorphicAnosov.Paper.Ghys.RankOneDefsG18

/-! This file proves holomorphicity of the native unstable iterates and their inverses (Ghys, Proposition 2.2). -/

namespace HolomorphicAnosov.Ghys

open scoped ContDiff Manifold

universe u

attribute [local instance] complex_isManifold_real

/-- The native unstable iterate and its inverse are holomorphic for the specified complex leaf structures. (Ghys, Proposition 2.2) -/
theorem native_unstable_iterate_holomorphic
    {d : ℕ} {M : Type u} [MetricSpace M] [T2Space M]
    [SecondCountableTopology M] [CompactSpace M] [ChartedSpace (ComplexModel d) M]
    [IsManifold (complexModel d) ∞ M]
    {f : Biholomorph d d M M} {S : InvariantRealTangentSplitting f.toReal}
    (L : RankOneNativeLeaves f S) (n : ℕ) (x : M) :
    letI := L.identification.unstableTopology x
    letI := L.identification.unstableCharts x
    letI := (L.complexUnstable x).charts
    letI := L.identification.unstableTopology ((f^[n]) x)
    letI := L.identification.unstableCharts ((f^[n]) x)
    letI := (L.complexUnstable ((f^[n]) x)).charts
    ContMDiff (complexModel 1) (complexModel 1) ∞ (L.iterateUnstable n x) ∧
      ContMDiff (complexModel 1) (complexModel 1) ∞ (L.iterateUnstable n x).symm := by
  let := L.identification.unstableTopology x
  let := L.identification.unstableCharts x
  let := (L.complexUnstable x).charts
  let := L.identification.unstableTopology ((f^[n]) x)
  let := L.identification.unstableCharts ((f^[n]) x)
  let := (L.complexUnstable ((f^[n]) x)).charts
  let := (L.complexUnstable x).complex_manifold
  let := (L.complexUnstable ((f^[n]) x)).complex_manifold
  constructor
  · intro z
    apply (ContMDiffAt.iff_comp_isImmersionAt
      ((L.complexUnstable ((f^[n]) x)).inclusion_immersion (L.iterateUnstable n x z))).mpr
    refine ⟨(L.iterateUnstable n x).continuous.continuousAt, ?_⟩
    have heq : Subtype.val ∘ L.iterateUnstable n x = (f^[n]) ∘ Subtype.val :=
      funext (L.iterateUnstable_points n x)
    rw [heq]
    exact ((f.contMDiff.iterate n).comp (L.complexUnstable x).inclusion_holomorphic) z
  · intro z
    apply (ContMDiffAt.iff_comp_isImmersionAt
      ((L.complexUnstable x).inclusion_immersion ((L.iterateUnstable n x).symm z))).mpr
    refine ⟨(L.iterateUnstable n x).symm.continuous.continuousAt, ?_⟩
    have heq : Subtype.val ∘ (L.iterateUnstable n x).symm =
        (f.symm^[n]) ∘ Subtype.val := by
      funext w
      have h := L.iterateUnstable_points n x ((L.iterateUnstable n x).symm w)
      rw [(L.iterateUnstable n x).apply_symm_apply] at h
      have hinv : Function.LeftInverse f.symm f := f.symm_apply_apply
      have h' := congrArg (f.symm^[n]) h
      rw [hinv.iterate n _] at h'
      exact h'.symm
    rw [heq]
    exact ((f.symm.contMDiff.iterate n).comp
      (L.complexUnstable ((f^[n]) x)).inclusion_holomorphic) z

end HolomorphicAnosov.Ghys

