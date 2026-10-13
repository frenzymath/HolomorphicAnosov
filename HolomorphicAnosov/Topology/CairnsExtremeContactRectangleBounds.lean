import HolomorphicAnosov.Topology.CairnsExtremeContactOrdinateExtrema
import Mathlib.Analysis.Complex.Circle

open Set Metric

namespace HolomorphicAnosov

/--
An embedded circle has strict real-coordinate bounds.  The bounds are chosen
outside the compact real-coordinate image, providing the vertical sides of
Cairns's enclosing rectangle.
-/
theorem cairns_extreme_contact_rectangle_bounds
    (γ : Circle → ℂ) (hγ : Topology.IsEmbedding γ) :
    ∃ L R : ℝ, ∀ z ∈ Set.range γ, L < z.re ∧ z.re < R := by
  have hcompact : IsCompact (Set.range γ) := isCompact_range hγ.continuous
  have hnonempty : (Set.range γ).Nonempty := Set.range_nonempty γ
  obtain ⟨L₀, hL₀, hLmin⟩ :=
    hcompact.exists_isMinOn hnonempty Complex.continuous_re.continuousOn
  obtain ⟨R₀, hR₀, hRmax⟩ :=
    hcompact.exists_isMaxOn hnonempty Complex.continuous_re.continuousOn
  refine ⟨L₀.re - 1, R₀.re + 1, ?_⟩
  intro z hz
  constructor
  · have hzmin : L₀.re ≤ z.re := (isMinOn_iff.mp hLmin) z hz
    linarith
  · have hzmax : z.re ≤ R₀.re := (isMaxOn_iff.mp hRmax) z hz
    linarith

end HolomorphicAnosov
