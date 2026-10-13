import HolomorphicAnosov.Analysis.Distribution.MollifierFirstDerivative

open Function Set Filter MeasureTheory TopologicalSpace
open scoped BigOperators ContDiff Distributions ENNReal Topology _root_.Topology
attribute [local instance] Classical.propDecidable

namespace HolomorphicAnosov.Analysis.Distribution

/-- Ordered distributional derivative identities for local mollification.

Source: Demailly, *Complex Analytic and Differential Geometry*, I §2.A (2.6),
p.15, and I §2.D.3 (2.23), p.19; smooth parameter pairing follows Dyatlov,
Proposition 6.3, pp.68–69. The chain-rule and ordered-derivative details below
expand the step omitted in the source regularization argument.

Proof: Fix ε>0 and a point x of the strict interior. Choose r>ε smaller than
its extended distance to the complement of U. For parameters p in the ball
B(x,r-ε), all translated ε-ball supports lie in the compact ball K=B̅(x,r)⊂U.
The kernel H(p,y)=ε⁻ᵐρ(ε⁻¹(p-y)) is jointly smooth, with all parameter and
spatial derivatives supported in K. The fixed-support family theorem therefore
pairs every parameter coordinate derivative with T. Its bundled sections equal
κ on the strict interior by equality of their underlying functions, so its
paired function agrees locally with F. Within derivatives on this open ball
are the ordinary derivatives at x.

For a coordinate direction e, the chain rule gives ∂ₚ,e H=-∂ᵧ,e H.
Repeated differentiation gives the corresponding ordered identity, one minus
sign for each direction. The pointwise evaluation of TestFunction.lineDerivCLM
is the spatial derivative, because its input and output orders are both ∞.
Extensionality identifies these derivatives as test functions. Induction in the
recursion for D, using complex linearity of T, then gives D k v φ as (-1)^k
T of the spatial test derivatives in reverse order. Smoothness commutes the
spatial coordinate derivatives, so this equals the kernel parameter derivative
paired with T. The fixed-support theorem states sorted coordinate multiindices;
commuting smooth mixed partials and the iterated Fréchet derivative recursion
identifies any ordered tuple with its sorted tuple. This proves the requested
identity for arbitrary v. For k=0, the zeroth Fréchet derivative evaluates to F
and the conclusion is exactly the pairing equation and D's base equation.
Empty U gives no evaluation points. No normalization or evenness is needed. -/
theorem distribution_mollifier_derivative_identity
    {m : ℕ} (hm : 1 ≤ m) (U : Opens (EuclideanSpace ℝ (Fin m)))
    (T : TestFunction U ℂ ⊤ →L[ℂ] ℂ)
    (ρ : TestFunction (⊤ : Opens (EuclideanSpace ℝ (Fin m))) ℝ ⊤)
    (hρ_support : tsupport (ρ : EuclideanSpace ℝ (Fin m) → ℝ) ⊆
      Metric.closedBall 0 1)
    (κ : ∀ ε : ℝ, 0 < ε → ∀ x,
      x ∈ {x | x ∈ U ∧ ENNReal.ofReal ε < Metric.infEDist x ((U : Set _)ᶜ)} →
        TestFunction U ℂ ⊤)
    (F : ∀ ε : ℝ, 0 < ε → EuclideanSpace ℝ (Fin m) → ℂ)
    (D : ∀ k : ℕ, (Fin k → Fin m) → TestFunction U ℂ ⊤ → ℂ)
    (hκ : ∀ ε (hε : 0 < ε) x hx y,
      κ ε hε x hx y = (((ε⁻¹) ^ m : ℝ) : ℂ) *
        ((ρ (ε⁻¹ • (x - y)) : ℝ) : ℂ))
    (hF : ∀ ε (hε : 0 < ε) x
      (hx : x ∈ {x | x ∈ U ∧ ENNReal.ofReal ε < Metric.infEDist x ((U : Set _)ᶜ)}),
      F ε hε x = T (κ ε hε x hx))
    (hD0 : ∀ v φ, D 0 v φ = T φ)
    (hDsucc : ∀ k v φ, D (k + 1) v φ =
      - D k (Fin.tail v) ((TestFunction.lineDerivCLM ℂ
        (EuclideanSpace.single (v 0) 1)) φ)) :
    ∀ ε (hε : 0 < ε) k (v : Fin k → Fin m) x
      (hx : x ∈ {x | x ∈ U ∧ ENNReal.ofReal ε < Metric.infEDist x ((U : Set _)ᶜ)}),
      iteratedFDeriv ℝ k (F ε hε) x
        (fun i ↦ EuclideanSpace.single (v i) 1) = D k v (κ ε hε x hx) := by
  classical
  have hDclm : ∀ k (v : Fin k → Fin m),
      ∃ S : TestFunction U ℂ ⊤ →L[ℂ] ℂ, ∀ φ, S φ = D k v φ := by
    intro k
    induction k with
    | zero =>
      intro v
      exact ⟨T, fun φ ↦ (hD0 v φ).symm⟩
    | succ k ih =>
      intro v
      obtain ⟨S, hS⟩ := ih (Fin.tail v)
      refine ⟨-(S.comp (TestFunction.lineDerivCLM ℂ
        (EuclideanSpace.single (v 0) 1))), ?_⟩
      intro φ
      simp only [neg_apply, ContinuousLinearMap.comp_apply, hS, hDsucc]
  intro ε hε k
  induction k with
  | zero =>
    intro v x hx
    simpa only [iteratedFDeriv_zero_apply, hD0] using hF ε hε x hx
  | succ k ih =>
    intro v x hx
    obtain ⟨S, hS⟩ := hDclm k (Fin.tail v)
    let G : EuclideanSpace ℝ (Fin m) → ℂ := fun p ↦
      iteratedFDeriv ℝ k (F ε hε) p (fun j ↦ EuclideanSpace.single (v j.succ) 1)
    have hG : ∀ p hp, G p = S (κ ε hε p hp) := by
      intro p hp
      exact (ih (Fin.tail v) p hp).trans (hS _).symm
    have hfirst := distribution_mollifier_first_derivative hm U S ρ hρ_support ε hε
      (κ ε hε) G (hκ ε hε) hG x hx
    have hsmooth := (distribution_mollifier_first_derivative hm U T ρ hρ_support ε hε
      (κ ε hε) (F ε hε) (hκ ε hε) (hF ε hε) x hx).1
    rw [hsmooth.differentiableAt_iteratedFDeriv (by exact_mod_cast ENat.natCast_lt_top k)
      |>.iteratedFDeriv_succ_apply_left']
    exact (hfirst.2 (v 0)).trans (by rw [hDsucc, hS])

end HolomorphicAnosov.Analysis.Distribution

