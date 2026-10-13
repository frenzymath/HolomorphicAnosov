import HolomorphicAnosov.Analysis.Complex.ConwayBoundedHolomorphicSequenceNormality
import HolomorphicAnosov.Analysis.Complex.ConwayCompactOpenAscoliNormality
import HolomorphicAnosov.Analysis.Complex.HurwitzZeroFreeLimit
import HolomorphicAnosov.Analysis.Complex.ConwayReciprocalBoundedNormality
import HolomorphicAnosov.Analysis.Complex.ConwayOmittedValuesUnboundedBranch
import HolomorphicAnosov.Geometry.LyubichModularLambdaCover
import Mathlib.Analysis.Complex.LocallyUniformLimit

/-!
Conway's sequential Montel–Carathéodory theorem for holomorphic functions omitting 0 and 1.
Source: Conway II, Chapter XVI, §4, Theorem 4.2, pp.124–125; Conway I, Chapter VII.
-/

namespace HolomorphicAnosov

/--
Conway, Functions of One Complex Variable II (1995), Chapter XVI, §4, Theorem 4.2,
printed pp.124–125 (PDF pp.139–140), with I (second edition, 1978), Chapter VII,
Theorem 1.23 pp.148–150, Theorem 2.9 p.153, Corollary 2.6 p.152 and Theorem 3.4
pp.156–157. This is the sequential Montel–Carathéodory omitted-values conclusion.

The functions are totalized on ℂ only for the calculus interface; all hypotheses and
conclusions concern G. IsPreconnected permits the empty domain, as in the DAG.
On a nonempty open G it is the source connected-region condition. Complex
DifferentiableOn expresses holomorphicity, and TendstoUniformlyOn in ℂ expresses
ordinary uniform convergence on K. The modulus alternative is precisely uniform
convergence to constant infinity in the spherical metric.

Natural-language proof (the named lower providers remain Stage 3 obligations):

M1. First work on a disk B=B(z0,R) contained in the open domain. ConwayII4.2p124 starts by
extracting a subsequence for which f_n(z0) converges in the sphere to α. One can state this
extraction with the existing complex closed-ball and sequential-compactness primitives: either some
closed complex ball contains infinitely many center values, giving a convergent strictly increasing
subsequence, or each such ball contains only finitely many values, giving |f_n(z0)|→∞. In the finite
case α may be0,1, or a point of Ω=ℂ\{0,1}. In the infinity case use the reciprocal case below. This
is extraction for one center only, not the unproved global compact-convergence extraction. The
generic bounded-family extraction used below is now represented by
analysis.conway_bounded_holomorphic_sequence_normality_g2, with the exact Cauchy-difference/Ascoli
source proof.

M2. Suppose α is finite and not0,1. Reuse the independent modular-lambda analytic cover λ:D→Ω.
Choose a sufficiently small evenly covered disk Δ about α and one sheet U; λ|U is biholomorphic.
After discarding a finite prefix, f_n(z0)∈Δ. Prescribe the lift value T_n(z0)=(λ|U)⁻¹(f_n(z0)). The
disk B is contractible by its affine contraction, hence simply connected and locally path connected;
the pointed covering-lift theorem gives continuous T_n:B→D with λT_n=f_n. ConwayIIXVI1.3pp110–111
and XVI2.1p113 prove its analyticity locally: by continuity of T_n choose an evenly covered sheet
neighborhood at any point; there T_n equals its holomorphic inverse branch composed with f_n. Thus
T_n is holomorphic and |T_n|<1. By the bounded-holomorphic sequence provider, pass to a compact-
uniform holomorphic limit T, with |T|≤1. Its center value is (λ|U)⁻¹(α)∈D. If |T|=1 anywhere, the
local maximum-modulus theorem gives local constancy; conversion to analytic-on and the connected-
disk identity theorem give constancy on B, contradicting its center value. Hence |T|<1 throughout B.
For compact K⊂B take max_K|T|<r<1. Eventually |T_n|≤r on K, so |f_n|=|λT_n| is bounded there by
max_closedBall(0,r)|λ|. Include the finitely discarded functions by their finite compact maxima. The
bounded-holomorphic sequence provider then extracts a finite holomorphic compact-uniform
subsequential limit of f_n on B. No puncture cusp or omitted-values spherical derivative theorem is
used.

M3. Suppose α=1. The nowhere-zero holomorphic f_n on the simply connected disk has a continuous
square root g_n by the existing exact continuous-root theorem, with g_n²=f_n. This branch is
holomorphic as the source asserts: at w, g_n(w)≠0; continuity keeps g_n(z)+g_n(w) nonzero near w,
and [g_n(z)−g_n(w)]/[z−w]=[f_n(z)−f_n(w)]/([z−w][g_n(z)+g_n(w)]) tends to f_n′(w)/(2g_n(w)). Choose
the sign so g_n(z0)→−1. To justify the sign choice, the two square roots of a value tending to1 tend
to the two separated roots ±1; select the root near−1 for the center and change the continuous
branch sign if needed. Each g_n omits0 because f_n omits0, and omits1 because g_n=1 would imply
f_n=1. Its center limit−1 is in Ω, so M2 applies to give a subsequence bounded on every compact
subset. Squaring bounds f_n on every compact subset; the bounded-holomorphic sequence provider gives
a finite holomorphic compact-uniform subsequential limit. If α=0, replace f_n by1−f_n, still
omitting0,1 with center limit1; apply this case and then subtract from1. These are the exact square-
root and reflection cases on ConwayIIp125.

M4. Suppose α=∞. Put g_n=1/f_n, holomorphic and still omitting0,1, with g_n(z0)→0. The α=0 case and
the bounded-holomorphic sequence provider give a subsequence converging compact-uniformly to a
holomorphic g on B with g(z0)=0. The exact represented Hurwitz provider says that a compact-uniform
limit of nowhere-zero holomorphic functions on a connected open set is identically zero or nowhere
zero. Since g(z0)=0, g≡0. For compact K⊂B and M>0, eventually sup_K|g_n|<1/M; since g_n never
vanishes, |f_n|>M throughout K. This is ConwayIIp125’s reciprocal case, using the written
ConwayI2.5–2.6/McMullen straight-line zero-count source composite.

M5. M2–M4 give spherical disk normality using the represented bounded-family and Hurwitz providers.
Apply the necessary direction of the general compact-open Ascoli provider on each contained disk,
with the compact complete metric sphere as target: each point has equicontinuity for the
restrictions of the original family. Every point of G lies in a contained disk, hence the original
family is equicontinuous at every point of G. Sphere compactness gives pointwise relatively compact
values. The sufficient direction of that SAME Ascoli provider on G now extracts one strictly
increasing subsequence with continuous sphere-valued compact-uniform limit. These are two
applications of the actual written ConwayI VII1.23pp148–150 theorem, not a fresh rational-disk
diagonal substitute. The source child is now complete at its own level: its actual pinned Mathlib
finite-entourage source specialization supplies relative normality→total boundedness→compact closure
in the SAME canonical C(G,Ω) compact-convergence uniformity, with no IsSeqCompact F premise. This
parent remains complete relative to its named child, without transitive or Lean closure.

M6. Given the spherical compact-uniform global limit F from M5, follow ConwayIVII3.4pp156–157 to
classify it. If F(a) is finite, continuity and spherical uniform convergence on a small closed disk
about a keep F and a tail of f_n inside a finite complex ball. Use the positive radius1+|F(a)|
rather than the printed zero radiusM=|F(a)| when F(a)=0. The chordal formula
d(v,w)=2|v−w|/(sqrt(1+|v|²)sqrt(1+|w|²)) then converts spherical uniform convergence there to
ordinary uniform convergence. The existing holomorphic-limit theorem makes F holomorphic near a. If
F(a)=∞, inversion of the sphere is continuous and preserves chordal distance; on a small disk the
reciprocals 1/f_n converge in ordinary modulus to the finite holomorphic reciprocal1/F, by the
preceding finite-case argument. Their zeros are absent, while1/F(a)=0, so the represented Hurwitz
provider makes1/F identically zero on that disk. Thus the sets of finite values and infinite values
are both open in G. Connectedness makes F finite everywhere or identically∞. In the finite case its
local holomorphic descriptions agree as the same function, and compactness plus a finite local cover
gives ordinary uniform convergence on every compact subset. In the infinity case
d(f_n,∞)=2/sqrt(1+|f_n|²) gives exactly eventual |f_n|>M uniformly on each compact subset for every
M>0. This expands the actual VII3.4 classification without a meromorphic-pole assumption on F.

M7. The finite branch gives the first conclusion with its holomorphic h=F; the infinite branch gives
the quantified modulus statement. All subsequences in the source are strictly increasing
subsequences of the original natural-number sequence; composing successive extractions preserves
this. Empty G is included without a nonemptiness assumption: choose h=0 and any strictly increasing
sequence, and the first alternative is vacuous on every compact subset. The source proof only uses
simply connected disks locally and connectedness for the final classification, not simple
connectedness of G. All three former analytic/normality guards are now named source children. The
generic Ascoli child is now split/complete at its own level with all SAME-uniformity guards named;
no transitive or Lean completion is claimed.
-/
theorem conway_montel_caratheodory_omitted_values_g2
    {G : Set ℂ} (hG : IsOpen G) (hconn : IsPreconnected G) (f : ℕ → ℂ → ℂ)
    (hf : ∀ n, DifferentiableOn ℂ (f n) G)
    (homit : ∀ n z, z ∈ G → f n z ≠ 0 ∧ f n z ≠ 1) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ((∃ h : ℂ → ℂ, DifferentiableOn ℂ h G ∧
          ∀ K : Set ℂ, IsCompact K → K ⊆ G →
            TendstoUniformlyOn (fun k z ↦ f (φ k) z) h Filter.atTop K) ∨
        (∀ K : Set ℂ, IsCompact K → K ⊆ G →
          ∀ M : ℝ, 0 < M → ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k →
            ∀ z : ℂ, z ∈ K → M < ‖f (φ k) z‖)) := by
  by_cases hEmpty : G = ∅
  · subst G
    refine ⟨id, strictMono_id, Or.inl ⟨(fun _ ↦ 0), differentiableOn_empty, ?_⟩⟩
    intro K hK hKG
    rw [Set.subset_empty_iff.mp hKG]
    exact tendstoUniformlyOn_empty
  · by_cases hSub : ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
        ((∀ K : Set ℂ, IsCompact K → K ⊆ G →
          ∃ M : ℝ, 0 ≤ M ∧ ∀ n z, z ∈ K → ‖f (ψ n) z‖ ≤ M) ∨
        (∀ K : Set ℂ, IsCompact K → K ⊆ G →
          ∃ M : ℝ, 0 ≤ M ∧ ∀ n z, z ∈ K → ‖(f (ψ n) z)⁻¹‖ ≤ M))
    · obtain ⟨ψ, hψ, hcases⟩ := hSub
      rcases hcases with hBound | hInvBound
      · obtain ⟨φ, hφ, g, hg, hconv⟩ :=
          conway_bounded_holomorphic_sequence_normality_g2 hG (fun n ↦ f (ψ n))
            (fun n ↦ hf (ψ n)) hBound
        exact ⟨ψ ∘ φ, hψ.comp hφ, Or.inl ⟨g, hg, hconv⟩⟩
      · obtain ⟨φ, hφ, hconv⟩ := conway_reciprocal_bounded_normality_g19 hG hconn
          (fun n ↦ f (ψ n)) (fun n ↦ hf (ψ n))
          (fun n z hz ↦ (homit (ψ n) z hz).1) hInvBound
        exact ⟨ψ ∘ φ, hψ.comp hφ, hconv⟩
    · exact conway_omitted_values_unbounded_branch_g7 hG hconn f hf homit hSub

end HolomorphicAnosov

