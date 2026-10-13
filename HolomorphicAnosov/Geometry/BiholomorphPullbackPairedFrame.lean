import HolomorphicAnosov.Geometry.BiholomorphToReal
import HolomorphicAnosov.Geometry.RealTangentTopForm

open scoped ContDiff

namespace HolomorphicAnosov

universe u

variable {d : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel d) X]

/-- Pullback on a paired native real tangent frame uses the original complex derivative (Demailly, I §1.B.5, VI §4 p.296). -/
theorem biholomorph_pullback_paired_frame [IsManifold (complexModel d) ∞ X]
    (F : Biholomorph d d X X) (ν : RealTangentTopForm d X) (x : X)
    (v : ComplexPairedIndex d → TangentSpace (complexModel d) x) :
    realTangentTopFormPullback F ν x
      (fun i ↦ complexTangentToReal d x (v i)) =
    ν (F x) (fun i ↦ complexTangentToReal d (F x)
      (mfderiv (complexModel d) (complexModel d) F x (v i))) := by
  change ν (F x) (fun i ↦ mfderiv (realModel d) (realModel d) F x
    (complexTangentToReal d x (v i))) = _
  congr 1
  funext i
  exact Biholomorph.real_mfderiv_realification F x (v i)


end HolomorphicAnosov
