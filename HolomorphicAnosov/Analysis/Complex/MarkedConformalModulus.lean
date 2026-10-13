import HolomorphicAnosov.Analysis.QCSignedDistortionModulusRectangleConformalModel

/-!
# The conformal modulus of a marked quadrilateral

Source: Ahlfors, *Lectures on Quasiconformal Mappings* (1966), Chapter II A, p.21;
Lehto–Virtanen, *Quasiconformal Mappings in the Plane* (1973), I.§§2.3–2.4, pp.14–15.
The right and left sides are distinguished, so the modulus is width divided by height.
The existing marked rectangle theorem supplies these witnesses for every positively marked
Jordan quadrilateral and proves that the ratio is independent of their choice.
-/

namespace HolomorphicAnosov.Analysis.MarkedRectangle

open Set

/-- A positive real number is the conformal modulus of a marked quadrilateral when it is the
width/height ratio of a conformal rectangle model extending homeomorphically to the closure
and carrying the four corners, in order, to the four marks. Source: Ahlfors II A, p.21;
Lehto–Virtanen I.§§2.3–2.4, pp.14–15. The inverse is the literal inverse of the interior map.
Corner correspondence under the closure homeomorphism fixes the full four boundary arcs.
There is no boundary differentiability requirement, and all function values off their open
source domains are irrelevant. This relation avoids an arbitrary choice of a model. -/
def HasMarkedConformalModulus (Q : Set ℂ) (p : Fin 4 → ℂ) (m : ℝ) : Prop :=
  ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ m = a / b ∧
    ∃ F F_inv : ℂ → ℂ,
      DifferentiableOn ℂ F (OpenRectangle a b) ∧
      DifferentiableOn ℂ F_inv Q ∧
      BijOn F (OpenRectangle a b) Q ∧
      MapsTo F_inv Q (OpenRectangle a b) ∧
      (∀ z ∈ OpenRectangle a b, F_inv (F z) = z) ∧
      (∀ w ∈ Q, F (F_inv w) = w) ∧
      ∃ boundaryExtension : ClosedRectangle a b ≃ₜ closure Q,
        (∀ z : ClosedRectangle a b,
          (z : ℂ) ∈ OpenRectangle a b → (boundaryExtension z : ℂ) = F z) ∧
        ∀ (i : Fin 4) (z : ClosedRectangle a b),
          (z : ℂ) = RectangleCorner a b i → (boundaryExtension z : ℂ) = p i

end HolomorphicAnosov.Analysis.MarkedRectangle
