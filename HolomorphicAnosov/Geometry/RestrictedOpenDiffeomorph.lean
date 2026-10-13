import HolomorphicAnosov.Geometry.Biholomorph
import Mathlib.Geometry.Manifold.ContMDiff.Basic

open scoped ContDiff Manifold Topology _root_.Topology
open Set TopologicalSpace
noncomputable section
namespace HolomorphicAnosov

/-- The restriction of a smooth diffeomorphism to a nonempty open set preserved by both it and its
inverse is a smooth diffeomorphism. (Lee, Prop. 1.8) -/
noncomputable def restricted_open_diffeomorph
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    (f : Diffeomorph I I M M ∞)
    (K : Opens M) (_hK : Nonempty K)
    (hmap : MapsTo (f : M → M) (K : Set M) (K : Set M))
    (hinv : MapsTo (f.symm : M → M) (K : Set M) (K : Set M)) :
    Diffeomorph I I K K ∞ := by
  let g : K → K := fun x => ⟨f x.1, hmap x.2⟩
  let ginv : K → K := fun x => ⟨f.symm x.1, hinv x.2⟩
  have hleft : Function.LeftInverse ginv g := by
    intro x
    apply Subtype.ext
    simp [g, ginv]
  have hright : Function.RightInverse ginv g := by
    intro x
    apply Subtype.ext
    simp [g, ginv]
  let e : K ≃ K := { toFun := g, invFun := ginv, left_inv := hleft, right_inv := hright }
  have hcont : ContMDiff I I ∞ (e : K → K) := by
    intro x
    change ContMDiffAt I I ∞ g x
    apply (ContMDiffAt.subtypeVal_comp_iff K g x).mp
    change ContMDiffAt I I ∞ (fun y : K => (f (y : M) : M)) x
    rw [contMDiffAt_subtype_iff]
    exact f.contMDiff.contMDiffAt
  have hcontinv : ContMDiff I I ∞ (e.symm : K → K) := by
    intro x
    change ContMDiffAt I I ∞ ginv x
    apply (ContMDiffAt.subtypeVal_comp_iff K ginv x).mp
    change ContMDiffAt I I ∞ (fun y : K => (f.symm (y : M) : M)) x
    rw [contMDiffAt_subtype_iff]
    exact f.symm.contMDiff.contMDiffAt
  exact { toEquiv := e, contMDiff_toFun := hcont, contMDiff_invFun := hcontinv }

end HolomorphicAnosov
