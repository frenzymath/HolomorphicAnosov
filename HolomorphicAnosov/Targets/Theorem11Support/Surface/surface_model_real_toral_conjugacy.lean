import HolomorphicAnosov.Targets.Theorem11Support.Surface.lattice_basis_coordinates
import HolomorphicAnosov.Targets.Theorem11Support.Surface.integerMatrix_real_coordinates
import HolomorphicAnosov.Targets.Theorem11Support.Surface.lattice_quotient_homeomorph
import HolomorphicAnosov.Targets.Theorem11Support.Surface.toral_conjugacy_of_surface_coordinates
import HolomorphicAnosov.Targets.Theorem11Support.Surface.hyperbolic_integer_coordinates

/-!
A hyperbolic complex torus model in complex dimension two gives a hyperbolic real toral conjugacy in dimension four. (Zhang, §2, p.4; Ghys, Theorem A, pp.585, 598–600)
-/

noncomputable section

namespace HolomorphicAnosov

universe u

/-- A map with a hyperbolic complex torus model in complex dimension two is conjugate to a
hyperbolic integral automorphism of the real four-torus. -/
theorem surface_model_real_toral_conjugacy {X : Type u} [TopologicalSpace X]
    [ChartedSpace (ComplexModel 2) X] (f : X → X)
    (hm : HasHyperbolicComplexTorusModel (d := 2) f) :
    HyperbolicRealToralConjugacy 4 X f := by
  classical
  obtain ⟨L, B, c, hB, hc⟩ := hm
  obtain ⟨b, P, hcoeff, hlattice⟩ := Theorem11SupportW02.lattice_basis_coordinates L
  let A := Theorem11SupportW10.integerMatrix L B b
  have hPB := Theorem11SupportW10.integerMatrix_real_coordinates L B b P hcoeff
  obtain ⟨q, hq⟩ := Theorem11SupportW03.lattice_quotient_homeomorph L P hlattice
  exact Surface11SupportW06.toral_conjugacy_of_surface_coordinates f L B c hc P A q hq hPB
    (SurfaceSpectral.hyperbolic_integer_coordinates B.linear P A hPB hB)

end HolomorphicAnosov

