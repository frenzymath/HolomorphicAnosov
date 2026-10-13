import Mathlib.Analysis.Complex.BranchLogRoot
import Mathlib.Analysis.Calculus.Deriv.Inverse
import HolomorphicAnosov.Topology.PlaneDomainChartConnected
import HolomorphicAnosov.Topology.PlaneSquareRootSimplyConnected
import HolomorphicAnosov.Analysis.Complex.ConwayFinitePolygonCauchyRepresentation
import HolomorphicAnosov.Topology.PlaneDomainRootRegularity
import HolomorphicAnosov.Topology.OnePointSphereChartG9

/-!
# Simply connected sphere domains and connected complements

Source: Conway, Functions of One Complex Variable I, VIII Theorem 2.2, pp. 202–204;
Functions of One Complex Variable II, Chapter 13 Proposition 1.1, pp. 1–2.

The Riemann sphere is represented by Mathlib's `OnePoint ℂ`, with its native one-point
compactification topology. Its finite chart is `OnePoint.some`, and the added point is
`OnePoint.infty`. This is the usual extended-complex-plane topology; no complex structure
on the sphere is needed for this topological criterion. Mathlib also supplies
`onePointEquivSphereOfFinrankEq` in its one-point sphere module.

`IsSimplyConnected` uses the induced topology and continuous path homotopies.
`IsConnected` includes nonemptiness; the properness hypothesis makes the complement
nonempty, so the source's empty-connected convention causes no difference.
-/

namespace HolomorphicAnosov.Topology

open Set Filter
open scoped _root_.Topology

/-- A nonempty proper connected open sphere domain is simply connected exactly when its
sphere complement is connected. Plane domains are included through `OnePoint.some`, with
infinity in their sphere complement. The whole finite plane is allowed.

Source: John B. Conway, Functions of One Complex Variable, second edition, GTM11, Springer1978;
Functions of One Complex VariableII, GTM159, Springer1995. VolumeI VIII Theorem2.2 printed
pp202–204 / PDF213–215; IV6.16–17 printed pp94–95 / PDF105–106; VolumeII13 Proposition1.1 printed
pp1–2 / PDF16–17.

Natural-language proof, following the source with the node's expanded lower steps:

Choose p in the nonempty sphere complement of G. A sphere Mobius homeomorphism sending p to
infinity takes G to a nonempty connected open plane subset U. Explicitly if p is finite use
z↦1/(z-p), with p↦infinity and infinity↦0; its inverse is w↦p+1/w with the corresponding endpoint
values. The finite formulas are mutually inverse and continuous; at the pole and infinity
continuity is exactly the one-point/spherical neighborhood condition |1/(z-p)|→infinity as z→p and
→0 as z→infinity. If p=infinity use the identity. Hence the full sphere complements correspond by
this homeomorphism and have equivalent connectedness. Conjugating every loop homotopy by the
homeomorphism gives equivalent simple connectedness. It is therefore enough to prove Conway
VIII2.2(a)⇔(c) for U⊂C. U may equal C even though the original G is proper; this case is retained.

Assume U simply connected. For any z outside U, the exponential covering supplies a
continuous logarithm L of w-z on U. The derivative-of-composition inverse theorem applies
because exp has nonzero derivative and L is continuous; differentiating exp(L(w))=w-z
therefore gives L'(w)=1/(w-z). Along each affine polygon segment in U, the real chain rule
and interval FTC identify its reciprocal integral with the difference of L at its
endpoints. These differences telescope to zero on every closed polygon.

If the sphere complement is disconnected, choose two closed sets A and B that cover it,
each meeting it, with their intersection missing it. Swap them so that B contains
infinity. The set K of finite points of the complement lying in A is compact, nonempty,
and contained in the open plane set V which is the finite preimage of the complement
of B. Every point of V outside K belongs to U. The finite polygon Cauchy representation
provider applies to arbitrary open sets, so V need not be connected. Apply it to V,K
and the constant function 1 at a point z of K. Every representing polygon lies in
V\K and hence in U. All its reciprocal integrals vanish by the logarithm argument,
whereas the representation says their normalized sum equals 1. This contradiction
proves that the sphere complement is connected.

Conversely assume sphere\U connected. The polynomial approximation provider gives, for any
holomorphic f on U, polynomials p_n tending uniformly to f on compact subsets. Every polynomial
has the explicit polynomial primitive P(z)=sum_k a_k*z^(k+1)/(k+1). The polynomial derivative leaf
and the real-parameter FTC on each segment of any closed polygon gamma give integral_gamma p_n=0
by endpoint telescoping. Its total segment length ell is finite, and the interval integral norm
bound gives |integral_gamma(f-p_n)|<=ell*sup_(gamma)|f-p_n|→0. Integrability holds on each compact
segment by continuity before subtracting or estimating integrals. Hence every closed polygon
integral of f is zero. This is the needed specialization of sourceVIII2.2(d)⇒(e).

Fix a in U. The points joined to a by a finite polygonal path in U form a nonempty relatively open
and relatively closed subset: a small ball about any point is contained in U and a straight
segment inside it appends or reverses such a path. Connectedness gives all U. Define F(z) as the
integral of f along any such path from a to z. Joining one path to the reverse of another gives a
closed polygon, so CC4 makes the value independent of path; reversal and addition are the segment
integral substitutions and finite sums. For z close to z0 with B(z0,r)⊂U, append the segment z0→z.
Then (F(z)-F(z0))/(z-z0)=integral_0^1 f(z0+t*(z-z0))dt. Its difference from f(z0) has norm bounded
by sup_(t∈[0,1])|f(z0+t*(z-z0))-f(z0)|, which tends to0 by continuity at z0. Thus F'(z0)=f(z0) by
the slope derivative criterion. This proves a holomorphic primitive for every f directly from zero
polygon integrals, as in IV6.16p94; the simply-connected hypothesis of that corollary is not
assumed in this converse.

Let f be holomorphic and nowhere zero on U. Its derivative is holomorphic, so f'/f is holomorphic.
Apply CC5 to obtain H with H'=f'/f. Put q=f*exp(-H), holomorphic and nowhere zero. The exponential
derivative and product/quotient chain calculation give q'=exp(-H)*(f'-f*H')=0. Openness and
connectedness imply q is constant c, and evaluation at a gives c!=0. Choose d=Complex.log c with
exp d=c. Then L=H+d is holomorphic and exp L=f by exp-add. The holomorphic function exp(L/2)
squares to f. This is precisely the source IV6.17pp94–95 and VIII2.2(f)⇒(g)⇒(h), with its
constancy, derivative, and logarithm inputs named.

If U=C, every continuous based loop gamma contracts by (t,s)↦(1-s)*gamma(t)+s*gamma(0), preserving
its basepoint. If U is proper, CC6 establishes the exact square-root premise of ConwayVII4.3;
apply the square-root criterion to obtain a homeomorphism h:U→D. For an arbitrary continuous based
loop gamma, the homotopy (t,s)↦h^-1((1-s)*h(gamma(t))+s*h(gamma(0))) stays in U by convexity of D,
is continuous, fixes the basepoint, starts at gamma and ends at its constant loop. U is path
connected by the polygon-path argument in CC5. Thus it is simply connected for arbitrary
continuous loops, not merely rectifiable ones. Transport back through CC1 to prove the unchanged
proper-sphere statement.
-/
theorem conway_plane_domain_connected_complement_criterion
    (G : Set (OnePoint ℂ)) (_hne : G.Nonempty) (hproper : G ≠ Set.univ)
    (hopen : IsOpen G) (hconnected : IsConnected G) :
    IsSimplyConnected G ↔ IsConnected Gᶜ := by
  classical
  have hfinite (G : Set (OnePoint ℂ)) (hopen : IsOpen G) (hconnected : IsConnected G)
      (hinfty : (OnePoint.infty : OnePoint ℂ) ∉ G) :
      IsSimplyConnected G ↔ IsConnected Gᶜ := by
    let U : Set ℂ := OnePoint.some ⁻¹' G
    have hUopen : IsOpen U := hopen.preimage OnePoint.continuous_coe
    have hG : OnePoint.some '' U = G := by
      apply Set.Subset.antisymm
      · rintro _ ⟨z, hz, rfl⟩
        exact hz
      · intro z hz
        obtain ⟨w, rfl⟩ := OnePoint.ne_infty_iff_exists.mp
          (show z ≠ OnePoint.infty from fun he ↦ hinfty (he ▸ hz))
        exact ⟨w, hz, rfl⟩
    have hUconnected : IsConnected U := by
      exact isConnected_onePoint_some_preimage hconnected hinfty
    rw [← hG, OnePoint.isOpenEmbedding_coe.isEmbedding.isSimplyConnected_image]
    constructor
    · intro hsimple
      have hzero (z : ℂ) (hz : z ∉ U) (m : ℕ) (v : Fin (m + 1) → ℂ)
          (hv : v 0 = v (Fin.last m))
          (hseg : ∀ (k : Fin m) (t : ℝ), t ∈ Icc (0 : ℝ) 1 →
            AffineMap.lineMap (v k.castSucc) (v k.succ) t ∈ U) :
          (∑ k : Fin m, (v k.succ - v k.castSucc) *
            ∫ t in (0 : ℝ)..1,
              1 / (AffineMap.lineMap (v k.castSucc) (v k.succ) t - z)) = 0 := by
        obtain ⟨L, hLc, hLe⟩ := Complex.exists_continuousOn_eqOn_exp_comp hsimple hUopen
          (g := fun w : ℂ ↦ w - z) (continuous_id.sub continuous_const).continuousOn
          (by rintro ⟨w, hw, hwz⟩; exact hz ((sub_eq_zero.mp hwz) ▸ hw))
        have hLd (w : ℂ) (hw : w ∈ U) : HasDerivAt L (1 / (w - z)) w := by
          have heq : Complex.exp ∘ L =ᶠ[𝓝 w] (fun w ↦ w - z) := by
            filter_upwards [hUopen.mem_nhds hw] with x hx
            exact hLe hx
          have hval : Complex.exp (L w) = w - z := hLe hw
          simpa only [hval] using
            HasDerivAt.of_comp_left ((hLc w hw).continuousAt (hUopen.mem_nhds hw))
              (Complex.hasDerivAt_exp (L w)) ((hasDerivAt_id w).sub_const z)
              (Complex.exp_ne_zero _) heq
        have hedge (k : Fin m) :
            (v k.succ - v k.castSucc) *
              (∫ t in (0 : ℝ)..1,
                1 / (AffineMap.lineMap (v k.castSucc) (v k.succ) t - z)) =
              L (v k.succ) - L (v k.castSucc) := by
          let a := v k.castSucc
          let b := v k.succ
          have hne (t : ℝ) (ht : t ∈ Set.uIcc (0 : ℝ) 1) :
              AffineMap.lineMap a b t - z ≠ 0 := by
            intro h
            exact hz ((sub_eq_zero.mp h) ▸ hseg k t (by simpa using ht))
          have hd (t : ℝ) (ht : t ∈ Set.uIcc (0 : ℝ) 1) :
              HasDerivAt (fun t : ℝ ↦ L (AffineMap.lineMap a b t))
                ((b - a) * (1 / (AffineMap.lineMap a b t - z))) t := by
            simpa only [Function.comp_def, smul_eq_mul] using
              (hLd _ (hseg k t (by simpa using ht))).scomp t
                (AffineMap.hasDerivAt_lineMap (𝕜 := ℝ) (a := a) (b := b) (x := t))
          have hc : ContinuousOn (fun t : ℝ ↦
              (b - a) * (1 / (AffineMap.lineMap a b t - z))) (Set.uIcc (0 : ℝ) 1) := by
            apply continuousOn_const.mul
            exact continuousOn_const.div ((by fun_prop : Continuous
              (fun t : ℝ ↦ AffineMap.lineMap a b t - z)).continuousOn) hne
          have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hc.intervalIntegrable
          simpa only [intervalIntegral.integral_const_mul, AffineMap.lineMap_apply_zero,
            AffineMap.lineMap_apply_one] using hi
        simp_rw [hedge]
        rw [Finset.sum_sub_distrib]
        have hs := (Fin.sum_univ_succ (fun i ↦ L (v i))).symm.trans
          (Fin.sum_univ_castSucc (fun i ↦ L (v i)))
        rw [← hv] at hs
        linear_combination hs
      have hsep (A B : Set (OnePoint ℂ)) (hA : IsClosed A) (hB : IsClosed B)
          (hcov : (OnePoint.some '' U)ᶜ ⊆ A ∪ B)
          (hneA : ((OnePoint.some '' U)ᶜ ∩ A).Nonempty)
          (hinfB : (OnePoint.infty : OnePoint ℂ) ∈ B)
          (hdis : ¬ ((OnePoint.some '' U)ᶜ ∩ (A ∩ B)).Nonempty) : False := by
        let K : Set ℂ := OnePoint.some ⁻¹' ((OnePoint.some '' U)ᶜ ∩ A)
        let V : Set ℂ := OnePoint.some ⁻¹' Bᶜ
        have hKinf : (OnePoint.infty : OnePoint ℂ) ∉ (OnePoint.some '' U)ᶜ ∩ A := by
          intro h
          exact hdis ⟨_, h.1, h.2, hinfB⟩
        have hKc : IsCompact K := by
          exact ((OnePoint.isClosed_iff_of_notMem hKinf).mp
            ((OnePoint.isOpenEmbedding_coe.isOpenMap _ hUopen).isClosed_compl.inter hA)).2
        have hVo : IsOpen V := hB.isOpen_compl.preimage OnePoint.continuous_coe
        have hKV : K ⊆ V := by
          intro w hw hwB
          exact hdis ⟨_, hw.1, hw.2, hwB⟩
        obtain ⟨q, hq⟩ := hneA
        obtain ⟨z, rfl⟩ := OnePoint.ne_infty_iff_exists.mp
          (show q ≠ OnePoint.infty from fun h ↦ hKinf (h ▸ hq))
        have hzK : z ∈ K := hq
        have hzU : z ∉ U := fun hz ↦ hq.1 ⟨z, hz, rfl⟩
        have hVU : V \ K ⊆ U := by
          intro w hw
          by_contra hwU
          have hwc : (OnePoint.some w) ∈ (OnePoint.some '' U)ᶜ := by
            rintro ⟨x, hx, heq⟩
            exact hwU (OnePoint.coe_injective heq ▸ hx)
          exact (hcov hwc).elim (fun hwA ↦ hw.2 ⟨hwc, hwA⟩) hw.1
        obtain ⟨n, m, v, hm, hv, hseg, hformula⟩ :=
          HolomorphicAnosov.Analysis.Complex.conway_finite_polygon_cauchy_representation
            V K hVo hKc hKV
        have heq := hformula (fun _ ↦ (1 : ℂ)) (differentiableOn_const 1) z hzK
        have hsum (j : Fin n) := hzero z hzU (m j) (v j) (hv j)
          (fun k t ht ↦ hVU (hseg j k t ht))
        simp only [hsum, Finset.sum_const_zero, mul_zero] at heq
        exact one_ne_zero heq
      refine ⟨⟨OnePoint.infty, by simp⟩, isPreconnected_closed_iff.mpr ?_⟩
      intro A B hA hB hcov hneA hneB
      by_contra hdis
      have hinf : (OnePoint.infty : OnePoint ℂ) ∈ (OnePoint.some '' U)ᶜ := by simp
      rcases hcov hinf with hiA | hiB
      · exact hsep B A hB hA (by simpa [union_comm] using hcov) hneB hiA
          (by simpa [inter_comm A B] using hdis)
      · exact hsep A B hA hB hcov hneA hiB hdis
    · intro hcomplement
      apply conway_square_root_criterion_simply_connected hUopen hUconnected
      -- Polynomial approximation gives primitives, logarithms and square roots.
      intro f hf hfn
      exact conway_square_root_of_connected_complement hUopen hUconnected hcomplement f hf hfn

  obtain ⟨p, hp⟩ := Set.nonempty_compl.mpr hproper
  obtain ⟨e, he⟩ := HolomorphicAnosov.onePoint_homeomorph_send_to_infty p
  have hnot : (OnePoint.infty : OnePoint ℂ) ∉ e '' G := by
    rintro ⟨z, hz, hze⟩
    have : z = p := e.injective (hze.trans he.symm)
    exact hp (this ▸ hz)
  have h := hfinite (e '' G) (e.isOpenMap _ hopen)
    (e.isConnected_image.mpr hconnected) hnot
  rw [e.isSimplyConnected_image, ← e.image_compl, e.isConnected_image] at h
  exact h

end HolomorphicAnosov.Topology

