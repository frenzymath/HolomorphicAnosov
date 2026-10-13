import HolomorphicAnosov.Geometry.HermitianMetricVolumeDefinitions
import HolomorphicAnosov.Geometry.BiholomorphPullbackPairedFrame

open scoped ContDiff

namespace HolomorphicAnosov

universe u

variable {d : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel d) X]

/-- Evaluating a pullback identity on a source unitary frame reduces the Jacobian to the target form on the actual complex differential of that frame. (Demailly, VI §4.) -/
theorem hermitian_jacobian_eq_native_paired_image
    [IsManifold (complexModel d) ∞ X]
    (h : HermitianTangentMetricCore d X) (F : Biholomorph d d X X)
    (J : X → ℝ)
    (hJ : realTangentTopFormPullback F (hermitianMetricPreferredTopForm h) =
      realTangentTopFormScale J (hermitianMetricPreferredTopForm h))
    (x : X) (b : Module.Basis (Fin d) ℂ (TangentSpace (complexModel d) x))
    (hb : hermitianMetricPreferredTopForm h x
      (fun i ↦ complexTangentToReal d x
        (if i.2 = 0 then b i.1 else Complex.I • b i.1)) = 1) :
    J x = hermitianMetricPreferredTopForm h (F x)
      (fun i ↦ complexTangentToReal d (F x)
        (mfderiv (complexModel d) (complexModel d) F x
          (if i.2 = 0 then b i.1 else Complex.I • b i.1))) := by
  have heval := congrArg
    (fun ν : RealTangentTopForm d X ↦ ν x
      (fun i ↦ complexTangentToReal d x
        (if i.2 = 0 then b i.1 else Complex.I • b i.1))) hJ
  rw [biholomorph_pullback_paired_frame] at heval
  change _ = J x * hermitianMetricPreferredTopForm h x
    (fun i ↦ complexTangentToReal d x
      (if i.2 = 0 then b i.1 else Complex.I • b i.1)) at heval
  rw [hb, mul_one] at heval
  exact heval.symm

end HolomorphicAnosov

