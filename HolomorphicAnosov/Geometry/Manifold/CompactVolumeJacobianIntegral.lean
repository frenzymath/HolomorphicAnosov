import HolomorphicAnosov.Geometry.Manifold.CompactVolumeJacobianIntegral.PresentationJacobianIntegral

/-!
# Integral of the volume-form Jacobian

Source: Zhang, Codimension-one holomorphic Anosov diffeomorphisms, Lemma 4.3,
equation (31) and the following sentence, printed p.16. Demailly, Complex Analytic
and Differential Geometry (2012), I §1.B.5 (1.13), p.10 and I §1.C (1.16)--(1.17),
p.11 supplies the actual oriented-chart integration and change-of-variables proof.
-/

open scoped Manifold ContDiff ENNReal
open Set MeasureTheory
noncomputable section
namespace HolomorphicAnosov.VolumePrototype

universe u
variable {n : ℕ} {M : Type u} [TopologicalSpace M] [ChartedSpace (CoordinateSpace n) M]
  [IsManifold 𝓘(ℝ, CoordinateSpace n) ∞ M] [CompactSpace M] [T2Space M]
  [MeasurableSpace M] [BorelSpace M]

/-- The smooth volume measure of a compact oriented manifold is finite and the integral
of the Jacobian of an orientation-preserving diffeomorphism is its total volume.

Source: Zhang Lemma 4.3 p.16 (31); Demailly I (1.13) p.10 and (1.16)--(1.17) p.11.
The Borel measurable structure records the standard Borel sets, and Hausdorffness is the
usual topological condition in the source's smooth manifold convention. No connectedness,
nonempty manifold, positive dimension, volume invariance or chosen finite presentation
is assumed. The measure and scalar ratio below are constructed from the same native top form.

Proof:
Set m=dim_R M. In a positively oriented chart φ:O→A⊂R^m write ν=ρ_φ(z) dz_1∧⋯∧dz_m, where ρ_φ is
smooth and strictly positive. On an overlap with a positively oriented chart ψ and transition
t=ψ∘φ^{-1}, the top-form transformation law gives ρ_φ(z)=ρ_ψ(t(z)) det Dt(z), with det Dt(z)>0.
Exhaust the open transition domain A_overlap by increasing compact sets C_k lying inside it; for
example impose norm(z)≤k and distance(z,R^m\A_overlap)≥1/k, omitting the distance condition if
the complement is empty. For a Borel subset B of the overlap apply Euclidean change of variables
on B∩C_k, with integrand ρ_ψ on its image. This measurable domain has the derivative at every
point by restriction of the smooth transition, and the map is injective. Both densities are
integrable there because they are bounded on the respective compact containing sets C_k and
t(C_k), which have finite Lebesgue mass. Thus the two coordinate measures agree on B∩C_k.
Continuity from below of measures gives their equality on B, including when its mass is
infinite. These compatible measures are the local representatives of μ_ν. In particular for an
integrable measurable scalar h supported in O, ∫_M h dμ_ν=∫_A h(φ^{-1}(z))ρ_φ(z) dz. This is
Demailly (1.16); the density transformation law, rather than an invariant-measure hypothesis,
makes the rule independent of the chosen oriented chart.

For every x choose an oriented source chart and an oriented target chart around F(x). Shrink
their source intersection with F^{-1} of the target domain to an open neighborhood O_x of x
whose closure is compact and stays within both required domains; choose still smaller
neighborhoods covering M. Compactness gives finitely many such O_i, with charts φ_i on O_i and
ψ_i on a neighborhood containing F(closure O_i). The subordinate smooth partition theorem gives
nonnegative χ_i with Σ_iχ_i=1 and K_i=tsupport χ_i contained in O_i. Each K_i is closed in
compact M, hence compact. The same construction is valid when F permutes connected components.

In chart φ_i the function χ_i(φ_i^{-1}(z))ρ_{φ_i}(z), extended by zero outside φ_i(O_i), is
continuous and supported on the compact set φ_i(K_i). Indeed K_i is compactly contained in the
chart domain, so the extension vanishes near every boundary point of that domain. Continuous
compactly supported real functions are Lebesgue integrable, by compact-set integrability and
vanishing off their support. Consequently ∫χ_i dμ_ν is finite. The finite sum of the nonnegative
χ_i equals 1, so summing their masses gives μ_ν(M)=Σ_i∫χ_i dμ_ν<∞. This also constructs the
global finite measure explicitly: μ_ν(B)=Σ_i∫_{φ_i(B∩O_i)}χ_i(φ_i^{-1}(z))ρ_{φ_i}(z) dz. The
overlap identity in V1 shows that this sum restricts on every chart to its density ρ_φ dz and is
independent of the chosen partition. Since J_νF is smooth on compact M, it is bounded and Borel
measurable; hence J_νF and every χ_i J_νF are integrable for this finite measure.

On A_i=φ_i(O_i), put T_i=ψ_i∘F∘φ_i^{-1}. This is a smooth diffeomorphism onto the open set
ψ_i(F(O_i)); it is injective and has a derivative at every point of the measurable open domain
A_i. Both charts are oriented and F preserves orientation, so det DT_i(z)>0. The top-form
pullback formula (Demailly (1.13)) and the defining identity F*ν=(J_νF)ν give
J_νF(φ_i^{-1}(z))ρ_{φ_i}(z)=ρ_{ψ_i}(T_i(z))det DT_i(z). The left density is therefore exactly
the absolute-determinant density in the Euclidean change-of-variables formula; no assertion that
J_νF=1 is made.

On T_i(A_i), define g_i(w)=χ_i(F^{-1}(ψ_i^{-1}(w)))ρ_{ψ_i}(w), and extend it by zero to R^m. Its
support is contained in the compact set ψ_i(F(K_i)), which stays within the target chart domain,
so g_i is integrable by the same compact-support argument as in V3. Apply the named Euclidean
change-of-variables theorem with domain A_i, map T_i, derivative DT_i, and integrand g_i. All
every-point derivative, domain measurability and injectivity guards were checked in V4. Since
g_i(T_i(z))=χ_i(φ_i^{-1}(z))ρ_{ψ_i}(T_i(z)), the pullback identity turns the source integral
into ∫_M χ_i J_νF dμ_ν. The target integral is ∫_{F(O_i)}χ_i(F^{-1}(y)) dμ_ν(y), which equals
the integral over M because χ_i vanishes off O_i. Thus ∫_M χ_i J_νF dμ_ν=∫_M (χ_i∘F^{-1}) dμ_ν.
Both sides are genuine finite integrals, not merely an equality of totalized nonintegrable
expressions.

Sum the finite identities of V5. Finite linearity is applicable because V3 and V5 prove
integrability of every summand. On the source, Σ_iχ_i=1, so the left sum is ∫_M J_νF dμ_ν. On
the target, Σ_iχ_i(F^{-1}(y))=1 for every y because F^{-1} is a globally defined inverse, so the
right sum is ∫_M1 dμ_ν=μ_ν(M). This proves the identity without volume invariance or
connectedness. If M is empty both sides vanish. In dimension zero a compact manifold is a finite
discrete set, ν gives positive point weights, J_νF(x)=ν(F(x))/ν(x), and the formula is directly
the finite-sum identity for the bijection F. The stated oriented-volume formulation requires
orientability; an absolute-density theorem on a nonorientable manifold would use a different
object. Zhang’s complex manifold has its complex orientation and holomorphic f^n preserves it,
so no such extension is needed for (31).
-/
theorem compact_volume_jacobian_integral
    (o : OrientedAtlas (n := n) (M := M)) (ν : PositiveVolumeForm o)
    (F : Diffeomorph 𝓘(ℝ, CoordinateSpace n) 𝓘(ℝ, CoordinateSpace n) M M ∞)
    (hF : PreservesOrientation o F) :
    volumeFormMeasure ν Set.univ < ⊤ ∧
      (∫ x, jacobian ν F x ∂volumeFormMeasure ν) = (volumeFormMeasure ν Set.univ).toReal := by
  exact ⟨finite_presentation_mass o ν (chosenVolumePresentation o),
    presentation_jacobian_integral o ν (chosenVolumePresentation o) F hF⟩


end HolomorphicAnosov.VolumePrototype
