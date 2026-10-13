import HolomorphicAnosov.Geometry.PositiveRealTangentTopFormNonzero

open scoped ContDiff

namespace HolomorphicAnosov

universe u

variable {d : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel d) X]

/-- The scalar multiplier of a positive top form is unique. (Demailly, I (1.13), VI (4.2)) -/
theorem positive_topForm_scale_injective [IsManifold (complexModel d) ∞ X]
    (ν : RealTangentTopForm d X) (hν : IsSmoothPositiveRealTangentTopForm ν)
    {J K : X → ℝ} (hJK : realTangentTopFormScale J ν = realTangentTopFormScale K ν) :
    J = K := by
  funext x
  exact (smul_left_injective ℝ (positive_topForm_ne_zero ν hν x)) (congrFun hJK x)


end HolomorphicAnosov
