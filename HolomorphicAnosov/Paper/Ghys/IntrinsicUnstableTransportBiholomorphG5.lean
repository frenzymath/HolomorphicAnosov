import HolomorphicAnosov.Geometry.ContinuousUnstableLeafLiftG1
import HolomorphicAnosov.Geometry.ComplexDerivativeInjectiveOfRealCharts
import HolomorphicAnosov.Geometry.ComplexHolomorphicImmersionOfInjectiveDerivative
import HolomorphicAnosov.Paper.Ghys.Proposition31

noncomputable section
open Set Filter _root_.Topology
open scoped Manifold ContDiff
namespace HolomorphicAnosov.Ghys
universe u v
attribute [local instance] complex_isManifold_real

variable {d : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
  [SecondCountableTopology M] [ChartedSpace (ComplexModel d) M]
  [IsManifold (complexModel d) ∞ M]
  (f : Biholomorph d d M M) (AD : AnosovDatum f)
  (P : AnosovIntrinsicFoliationPresentation f AD)

/-- A continuous lift to an intrinsic unstable leaf of a holomorphic ambient map is holomorphic. (HPS, §7; Ghys, §2) -/
theorem intrinsicUnstable_holomorphic_of_inclusion_g5
    {X : Type v} [TopologicalSpace X] [ChartedSpace (ComplexModel 1) X]
    [IsManifold (complexModel 1) ∞ X] :
    letI := P.realCharts
    ∀ q : Quotient P.foliations.unstablePartition,
    letI := P.foliations.unstableTopology q
    letI := P.complexLeaves.charts q
    ∀ (g : X → IntrinsicFoliationLeaf P.foliations.unstablePartition q),
      Continuous g → ContMDiff (complexModel 1) (complexModel d) ∞
        (fun z ↦ (g z).val) → ContMDiff (complexModel 1) (complexModel 1) ∞ g := by
  let := P.realCharts
  intro q
  let := P.foliations.unstableTopology q
  let := P.foliations.unstableCharts q
  let := P.unstableSmooth q
  let := P.complexLeaves.charts q
  let := P.complexLeaves.complex_manifold q
  intro g hg hhol z
  have hderiv : Function.Injective (mfderiv (complexModel 1) (complexModel d)
      (Subtype.val : IntrinsicFoliationLeaf P.foliations.unstablePartition q → M) (g z)) := by
    apply complexDerivative_injective_of_compatible_real_charts (r := 2)
    · exact ((P.unstable_real_complex_compatible q).1 (g z)).mdifferentiableAt (by simp)
    · exact ((P.unstable_real_complex_compatible q).2 (g z)).mdifferentiableAt (by simp)
    · exact (P.unstable_holomorphic q (g z)).mdifferentiableAt (by simp)
    · rw [← P.unstable_inclusion_eq q]
      exact (P.unstableNative q).immersion.mfderiv_injective (by simp) (g z)
  have himm := complex_holomorphic_immersion_of_injective_derivative
    ((P.unstable_holomorphic q).contMDiffAt (x := g z)) hderiv
  exact (ContMDiffAt.iff_comp_isImmersionAt himm).mpr ⟨hg.continuousAt, hhol z⟩

/-- The Anosov map restricts to a biholomorphism between the unstable leaves of the supplied intrinsic presentation. (Ghys, Prop. 3.1(i)) -/
theorem intrinsicUnstable_transport_biholomorph_g5 :
    letI := P.realCharts
    ∀ x : M,
    letI := P.complexLeaves.charts (Quotient.mk P.foliations.unstablePartition x)
    letI := P.complexLeaves.charts (Quotient.mk P.foliations.unstablePartition (f x))
    ∃ E : Biholomorph 1 1 (P.foliations.ULeaf x) (P.foliations.ULeaf (f x)),
      ∀ z, (E z).val = f z.val := by
  let := P.realCharts
  intro x
  let q := Quotient.mk P.foliations.unstablePartition x
  let q' := Quotient.mk P.foliations.unstablePartition (f x)
  let := P.foliations.unstableTopology q
  let := P.foliations.unstableTopology q'
  let := P.foliations.unstableCharts q
  let := P.foliations.unstableCharts q'
  let := P.unstableSmooth q
  let := P.unstableSmooth q'
  let := P.complexLeaves.charts q
  let := P.complexLeaves.charts q'
  let := P.complexLeaves.complex_manifold q
  let := P.complexLeaves.complex_manifold q'
  let := (P.unstableNative q).countable
  let := (P.unstableNative q').countable
  let : LocallyConnectedSpace (P.foliations.ULeaf x) :=
    ChartedSpace.locallyConnectedSpace (ComplexModel 1) _
  let : LocallyConnectedSpace (P.foliations.ULeaf (f x)) :=
    ChartedSpace.locallyConnectedSpace (ComplexModel 1) _
  let e := P.unstableLeafEquiv x
  have hc : Continuous e := continuous_unstable_leaf_lift_g1 P.foliations q' inferInstance e
    (f.continuous.comp (P.foliations.unstable_inclusion q))
  have hi : Continuous e.symm := continuous_unstable_leaf_lift_g1 P.foliations q inferInstance e.symm
    (f.symm.continuous.comp (P.foliations.unstable_inclusion q'))
  have hh : ContMDiff (complexModel 1) (complexModel 1) ∞ e :=
    intrinsicUnstable_holomorphic_of_inclusion_g5 f AD P q' e hc
      (f.contMDiff.comp (P.unstable_holomorphic q))
  have hh' : ContMDiff (complexModel 1) (complexModel 1) ∞ e.symm :=
    intrinsicUnstable_holomorphic_of_inclusion_g5 f AD P q e.symm hi
      (f.symm.contMDiff.comp (P.unstable_holomorphic q'))
  exact ⟨{e with contMDiff_toFun := hh, contMDiff_invFun := hh'}, fun _ ↦ rfl⟩

end HolomorphicAnosov.Ghys
