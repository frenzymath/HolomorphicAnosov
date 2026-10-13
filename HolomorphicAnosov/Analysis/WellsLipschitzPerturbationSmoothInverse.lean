import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ApproximatesLinearOn
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Smooth inverse of a Lipschitz perturbation of the identity

Source: John C. Wells, *Invariant manifolds of non-linear operators*, Pacific Journal of
Mathematics 62(1) (1976), pp. 285–287: Lipschitz inverse function theorem and ordinary
Fréchet inverse function theorem, specialized to the identity linear part.

All smoothness and inverse assertions concern the original open source and its actual image.
Total function representatives merely permit Mathlib's ambient open-set calculus notation;
no regularity is imposed on their values outside those sets.
-/

open scoped ContDiff ENat NNReal Topology _root_.Topology

namespace HolomorphicAnosov.Analysis

/-- Wells's smooth inverse theorem for a strict Lipschitz perturbation of the identity.

Source: Wells (1976), pp. 285–287; DAG node
`analysis.wells_lipschitz_perturbation_smooth_inverse_g5`.

The order `r : ℕ∞` is a positive finite integer or smooth infinity, embedded into `ℕ∞ω`.
It excludes analytic `ω`. The maps `Γ` and `J` are total representatives of maps on the
open sets `U` and `V`, respectively. There is no hypothesis on either representative outside
its stated domain, and the derivatives are their ordinary open-set Fréchet derivatives.
The continuous-linear-equivalence witness `A` expresses that `Id - DΓ(J(b))` has an actual
bounded linear inverse and that the derivative of `J` is exactly this inverse.

Complete natural-language proof from the current DAG node:

W0. If U is empty, V is empty and the unique inverse between empty sets satisfies all assertions
vacuously. If X is the zero Banach space and U is nonempty, U=V={0}; H and J are its unique maps,
smooth at every order, and the identity and its inverse are the zero operator on this zero space.
The formula and all norm estimates hold. Thus the following construction may be read on a nonzero X
with a chosen point of U. Q=0 is allowed throughout: Γ is then constant on nonempty U by the given
pairwise estimate, and H is a translation with translation inverse; no division by Q or by a nonzero
vector norm is used.

W1. Specialize Wells’s linear part T to Id and his perturbation f to −Γ. For every x,y∈U, the
reverse triangle inequality gives ‖H(x)−H(y)‖≥‖x−y‖−‖Γ(x)−Γ(y)‖≥(1−Q)‖x−y‖. Since 1−Q>0, H is
injective on ALL of U, including disconnected U. Consequently any two inverse values x=J(b), y=J(c)
satisfy ‖J(b)−J(c)‖≤(1−Q)⁻¹‖b−c‖. This is a global pairwise estimate, not merely a bound within one
coordinate neighborhood. The printed p286 lower bound with a general T uses ‖T‖ incorrectly; the
general correct lower factor would be ‖T⁻¹‖⁻¹. Here the direct identity calculation just written
proves exactly the needed estimate and does not rely on that source typo.

W2. Fix x₀∈U. Choose R>0 with the open ball x₀+B(0,R) contained in U. Write b₀=H(x₀),
Γ₀(z)=Γ(x₀+z)−Γ(x₀) for z∈B(0,R), so Γ₀(0)=0 and Γ₀ is Q-Lipschitz there. The translated equation
H(x₀+z)=b₀+y is z−Γ₀(z)=y. Put ρ=(1−Q)R>0, D=B(0,ρ), and L=Q/(1−Q)≥0. Follow the literal source
function-space construction: let ℒ be the family of maps g:D→X with g(0)=0 and ‖g(y)−g(z)‖≤L‖y−z‖.
Every such g is continuous and ‖g(y)‖≤Lρ, so it is a bounded continuous function; equip ℒ with the
inherited uniform distance d∞. The zero function belongs to ℒ. For g∈ℒ and y∈D,
‖y+g(y)‖≤(1+L)‖y‖<ρ/(1−Q)=R, so Γ₀(y+g(y)) is defined. Only these local source points are used; Γ
has no required extension outside U.

W3. The ambient bounded-continuous-function space D→ᵇX is complete by
mathlib.boundedContinuousFunction_instCompleteSpace_g7 because X is Banach. By
mathlib.boundedContinuousFunction_dist_le_g7, evaluation at each fixed y has pointwise distance
bounded by d∞ and is therefore continuous. The condition g(0)=0 is closed, and for each fixed y,z
the condition ‖g(y)−g(z)‖≤L‖y−z‖ is closed: it is the inverse image of the closed real interval
(−∞,L‖y−z‖] under the continuous evaluation/difference/norm map. Intersect these closed conditions
over y,z. Thus ℒ is a closed subset of the ambient complete space;
mathlib.isClosed_completeSpace_coe_g7 gives completeness of ℒ with its induced metric. Its zero
element supplies nonemptiness. No compactness of D, or compactness of a Banach ball, is asserted.

W4. Define Φ(g)(y)=Γ₀(y+g(y)); this is precisely g↦−T⁻¹∘f∘(T⁻¹+g) for the translated source
perturbation f=−Γ₀ and T=Id. It satisfies Φ(g)(0)=0 and ‖Φ(g)(y)−Φ(g)(z)‖≤Q(1+L)‖y−z‖=L‖y−z‖. Hence
Φ maps ℒ into itself, with continuous bounded values supplied by this anchored Lipschitz bound. For
g,h∈ℒ, at every y, ‖Φ(g)(y)−Φ(h)(y)‖≤Q‖g(y)−h(y)‖≤Qd∞(g,h). Since Qd∞≥0,
mathlib.boundedContinuousFunction_dist_le_g7 gives d∞(Φ(g),Φ(h))≤Qd∞(g,h). The same inequality in
extended distances is ContractingWith Q, with Q encoded as a nonnegative real and Q<1. This includes
Q=0.

W5. Apply g9.mathlib_contracting_exists_fixedPoint on the complete nonempty metric space ℒ, using
the zero function as basepoint; its distance to Φ(0) is finite, as all distances in this ordinary
metric space are finite. Obtain a fixed correction g*. Its equation is g*(y)=Γ₀(y+g*(y)), hence
(Id−Γ₀)(y+g*(y))=y on D. Thus x₀+y+g*(y)∈U solves H(x)=b₀+y for every ‖y‖<ρ. Therefore
b₀+B(0,ρ)⊆H(U). Since x₀ was arbitrary, every point of V=H(U) is interior and V is open. H:U→V is
onto by definition and is one-to-one by the global estimate, so it has a unique inverse J. The local
formula J(b₀+y)=x₀+y+g*(y) agrees with this same J by injectivity; no local inverses are chosen
incompatibly.

W6. The pairwise estimate above, now applied to actual inverse values in U, proves the required
Lipschitz bound on all of V and hence continuity of J. Γ is continuous on U because it is C^r (or
directly by its Lipschitz hypothesis), so H is continuous on U. The continuous mutually inverse maps
H:U→V and J:V→U form a homeomorphism of these open subsets. They can equivalently be represented as
an open partial homeomorphism e of X with source U and target V. Any ambient totalization of its
functions is used only through these open source/target germs and supplies no global smooth or
Lipschitz extension of Γ.

W7. For x∈U, r≥1 gives the actual Frechet derivative DΓ(x). Extend the function arbitrarily off U
only to express this open-set germ in the Mathlib fderiv API. Since U∈nhds x and the pairwise
hypothesis is LipschitzOnWith Q on U, mathlib.norm_fderiv_le_of_lipschitzOn_g7 gives ‖DΓ(x)‖≤Q<1.
The complete real continuous-endomorphism algebra of X has the standard operator norm and is
complete by mathlib.continuousLinearMap_instCompleteSpace. Apply
mathlib.isUnit_one_sub_of_norm_lt_one to DΓ(x). This proves Aₓ=Id−DΓ(x) is a unit, with an actual
bounded continuous-linear inverse. Its unit and inverse, with their multiplication identities,
explicitly give the forward and inverse maps of a continuous linear equivalence; algebraic unit data
are not mistaken for an unproved bounded inverse. The identity derivative comes from
mathlib.continuousLinearMap_hasFDerivAt; subtraction gives HasFDerivAt H Aₓ x by
mathlib.hasFDerivAt_sub.

W8. Let b∈V and x=J(b). Wells’s written differentiability argument is as follows. For small k with
b+k∈V put δ=J(b+k)−x. The inverse Lipschitz bound gives ‖δ‖≤(1−Q)⁻¹‖k‖, and
H(x+δ)−H(x)=k=Aₓδ+o(‖δ‖). Multiply by the bounded operator Aₓ⁻¹: δ−Aₓ⁻¹k=−Aₓ⁻¹o(‖δ‖)=o(‖k‖), using
that same Lipschitz bound. Thus DJ(b)=Aₓ⁻¹=(Id−DΓ(J(b)))⁻¹. The existing exact
mathlib.hasFDerivAt_of_local_left_inverse supplies this derivative conclusion from ContinuityAt J b,
HasFDerivAt H Aₓ at J(b), and H(J(c))=c eventually near b. Those guards hold because V is open and
H∘J=id there. mathlib.hasFDerivAt_fderiv identifies the resulting certificate with the displayed
derivative operator. No norm division at δ=0 is made.

W9. H is C^r on U: the identity is smooth at every order, represented by a continuous affine map;
use mathlib.continuousAffineMap_contDiff and restrict with mathlib.contDiff_contDiffOn. Subtract the
given C^r map Γ via the existing normed-space identity-model conversion
mathlib.contMDiffOn_iff_contDiffOn and smooth subtraction mathlib.contMDiffOn_sub. Its LieAddGroup
instance here is the ordinary additive group of a real normed space, at the same order r. On open U,
mathlib.isOpen_contDiffOn_iff gives ContDiffAt H at every x∈U, for the SAME map and smoothness
order.

W10. Follow Wells’s ordinary finite-order induction on p287: starting with the continuous inverse,
the displayed derivative is Inverse∘DH∘J. At a finite step k≥1, DH is C^(k−1) because H is C^k; this
exact guard is mathlib.contDiffOn_fderiv_of_isOpen with (k−1)+1≤k on U. Inversion is smooth at every
invertible operator Aₓ by mathlib.contDiffAt_continuousLinearMap_inverse, using completeness of X
and the continuous-linear-equivalence witness already constructed. If J is C^(k−1), the displayed
composition is C^(k−1), so DJ is C^(k−1) and J is C^k. No uniform-continuity or boundedness of
higher derivatives is used: these are local ordinary calculus assertions. The existing exact
mathlib.openPartialHomeomorph_contDiffAt_symm encapsulates precisely this inverse-derivative
induction: for each b∈V it takes e with target membership b, the actual HasFDerivAt e A_{J(b)}
certificate, and ContDiffAt e of the requested order at e.symm(b); X is complete. It yields
ContDiffAt J of that order at b. Its forward and derivative germs agree with H on open U. Finally
mathlib.isOpen_contDiffOn_iff on the proved open V packages this into C^r on V. This is a lower
calculus result for an ALREADY constructed inverse, not an assumption of the combined Lipschitz
inverse theorem being proved.

W11. For r=infinity, Wells’s p285 definition is C^p for every finite p. Apply the preceding
finite-order result to each p on the identical U,V,H,J; the source hypothesis supplies each such
order. The exact existing mathlib.contMDiffOn_infty, through mathlib.contMDiffOn_iff_contDiffOn on
the identity models, packages these finite orders into smooth infinity on the same V. This is
embedded smooth infinity in WithTop ENat, not analytic omega, and does not require a common
shrinking neighborhood for infinitely many orders. Together with the already proved openness,
bijectivity, global inverse Lipschitz bound and inverse-derivative formula, this gives every
assertion of the unchanged statement. The uniform/bounded classes and perturbation-continuity table
later in Wells p287 are outside this claim.

-/
theorem wellsLipschitzPerturbationSmoothInverse
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    {U : Set X} (hU : IsOpen U) {r : ℕ∞} (hr : 1 ≤ r)
    {Γ : X → X} (hΓ : ContDiffOn ℝ (r : ℕ∞ω) Γ U)
    {Q : ℝ} (hQ₀ : 0 ≤ Q) (hQ₁ : Q < 1)
    (hLip : ∀ x ∈ U, ∀ y ∈ U, ‖Γ x - Γ y‖ ≤ Q * ‖x - y‖) :
    let H : X → X := fun x ↦ x - Γ x
    let V : Set X := H '' U
    IsOpen V ∧ Set.BijOn H U V ∧
      ∃ J : X → X,
        Set.MapsTo J V U ∧
        (∀ x ∈ U, J (H x) = x) ∧
        (∀ b ∈ V, H (J b) = b) ∧
        ContDiffOn ℝ (r : ℕ∞ω) J V ∧
        (∀ b ∈ V, ∀ c ∈ V, ‖J b - J c‖ ≤ (1 - Q)⁻¹ * ‖b - c‖) ∧
        (∀ b ∈ V, ∃ A : X ≃L[ℝ] X,
          A.toContinuousLinearMap = ContinuousLinearMap.id ℝ X - fderiv ℝ Γ (J b) ∧
          HasFDerivAt J A.symm.toContinuousLinearMap b) := by
  classical
  let C : ℝ≥0 := ⟨Q, hQ₀⟩
  let H : X → X := fun x ↦ x - Γ x
  have happrox : ApproximatesLinearOn H (ContinuousLinearEquiv.refl ℝ X).toContinuousLinearMap U C := by
    intro x hx y hy
    have he : H x - H y - (ContinuousLinearEquiv.refl ℝ X) (x - y) = -(Γ x - Γ y) := by
      simp only [H, ContinuousLinearEquiv.refl_apply]
      abel
    change ‖H x - H y - (ContinuousLinearEquiv.refl ℝ X) (x - y)‖ ≤ Q * ‖x - y‖
    rw [he, norm_neg]
    exact hLip x hx y hy
  have hc : Subsingleton X ∨ C < ‖(ContinuousLinearEquiv.refl ℝ X).symm.toContinuousLinearMap‖₊⁻¹ := by
    rcases subsingleton_or_nontrivial X with hX | hX
    · exact Or.inl hX
    · apply Or.inr
      simpa only [ContinuousLinearEquiv.refl_symm, ContinuousLinearEquiv.coe_refl,
        ContinuousLinearMap.nnnorm_id, inv_one] using (show C < 1 by exact_mod_cast hQ₁)
  -- Mathlib supplies this topology by its guarded closed-ball contraction proof.
  -- This realizes the source inverse theorem without redefining Wells’s correction space.
  let e := happrox.toOpenPartialHomeomorph H U hc hU
  have hsource : e.source = U := rfl
  have htarget : e.target = H '' U := rfl
  have hefun : (e : X → X) = H := rfl
  have hsmooth : ContDiffOn ℝ (r : ℕ∞ω) H U := contDiffOn_id.sub hΓ
  have horder : (1 : ℕ∞ω) ≤ (r : ℕ∞ω) := by exact_mod_cast hr
  have hdiff : DifferentiableOn ℝ Γ U := hΓ.differentiableOn (ne_of_gt (lt_of_lt_of_le (by simp) horder))
  have hΓLip : LipschitzOnWith C Γ U := lipschitzOnWith_iff_norm_sub_le.mpr hLip
  have hlinear : ∀ x ∈ U, ∃ A : X ≃L[ℝ] X,
      A.toContinuousLinearMap = ContinuousLinearMap.id ℝ X - fderiv ℝ Γ x ∧
      HasFDerivAt H A.toContinuousLinearMap x := by
    intro x hx
    have hnorm : ‖fderiv ℝ Γ x‖ < 1 :=
      (norm_fderiv_le_of_lipschitzOn ℝ (hU.mem_nhds hx) hΓLip).trans_lt hQ₁
    -- The unit contains the actual bounded inverse, including in the zero Banach space.
    obtain ⟨a, ha⟩ := isUnit_one_sub_of_norm_lt_one hnorm
    let A := ContinuousLinearEquiv.ofUnit a
    have hA : A.toContinuousLinearMap = ContinuousLinearMap.id ℝ X - fderiv ℝ Γ x := ha
    refine ⟨A, hA, ?_⟩
    rw [hA]
    exact (hasFDerivAt_id x).sub ((hdiff x hx).differentiableAt (hU.mem_nhds hx)).hasFDerivAt
  refine ⟨e.open_target, e.bijOn, e.symm, (fun b hb ↦ e.symm.map_source hb), (fun x hx ↦ e.left_inv hx),
    (fun b hb ↦ e.right_inv hb), ?_, ?_, ?_⟩
  · intro b hb
    have hx : e.symm b ∈ U := e.symm.map_source hb
    obtain ⟨A, hA, hderiv⟩ := hlinear (e.symm b) hx
    exact (e.contDiffAt_symm hb hderiv (hsmooth.contDiffAt (hU.mem_nhds hx))).contDiffWithinAt
  · intro b hb c hc
    have hx : e.symm b ∈ U := e.symm.map_source hb
    have hy : e.symm c ∈ U := e.symm.map_source hc
    have hbound := hLip (e.symm b) hx (e.symm c) hy
    have hlo : (1 - Q) * ‖e.symm b - e.symm c‖ ≤ ‖b - c‖ := by
      have htri := norm_sub_le (e.symm b - e.symm c - (Γ (e.symm b) - Γ (e.symm c)))
        (-(Γ (e.symm b) - Γ (e.symm c)))
      have he : (e.symm b - e.symm c - (Γ (e.symm b) - Γ (e.symm c))) -
          (-(Γ (e.symm b) - Γ (e.symm c))) = e.symm b - e.symm c := by abel
      rw [he, norm_neg] at htri
      have hH : e.symm b - e.symm c - (Γ (e.symm b) - Γ (e.symm c)) = b - c := by
        have hb' := e.right_inv hb
        have hc' := e.right_inv hc
        change H (e.symm b) = b at hb'
        change H (e.symm c) = c at hc'
        calc
          _ = H (e.symm b) - H (e.symm c) := by simp only [H]; abel
          _ = b - c := by rw [hb', hc']
      rw [hH] at htri
      nlinarith
    have hp : 0 < 1 - Q := sub_pos.mpr hQ₁
    rw [mul_comm (1 - Q)⁻¹]
    apply (le_mul_inv_iff₀ hp).2
    nlinarith
  · intro b hb
    have hx : e.symm b ∈ U := e.symm.map_source hb
    obtain ⟨A, hA, hd⟩ := hlinear (e.symm b) hx
    exact ⟨A, hA, e.hasFDerivAt_symm hb hd⟩


end HolomorphicAnosov.Analysis
