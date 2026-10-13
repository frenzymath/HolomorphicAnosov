import HolomorphicAnosov.Topology.CairnsHalfDiskBoundaryTransport
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity

open Set Metric
open scoped ComplexConjugate
namespace HolomorphicAnosov

/-- The chord through two distinct unit-circle points meets the circle only
at those two points. Source: elementary Euclidean line-circle intersection,
used for the arc labels in Cairns (1951), Lemma 5.1, p.866. Write a point
on the chord line as u+t(v-u). Equality of the three squared norms gives
 t(t-1)‖v-u‖²=0, hence t=0 or t=1. -/
theorem circle_chord_det_eq_zero {u v z : ℂ}
    (hu : u ∈ sphere (0 : ℂ) 1) (hv : v ∈ sphere (0 : ℂ) 1)
    (hz : z ∈ sphere (0 : ℂ) 1) (huv : u ≠ v)
    (hdet : (conj (v-u) * (z-u)).im = 0) : z = u ∨ z = v := by
  let d := v - u
  have hd : d ≠ 0 := sub_ne_zero.mpr huv.symm
  have hqim : ((z-u)/d).im = 0 := by
    rw [Complex.div_im]
    have hnum : (z-u).im * d.re - (z-u).re * d.im = 0 := by
      dsimp [d]
      simp only [Complex.mul_im, Complex.conj_re, Complex.conj_im,
        Complex.sub_re, Complex.sub_im] at hdet
      nlinarith [hdet]
    rw [← sub_div, hnum, zero_div]
  let t := ((z-u)/d).re
  have hqt : (t : ℂ) = (z-u)/d := by
    apply Complex.ext <;> simp [t, hqim]
  have hzform : z = u + (t : ℂ) * d := by
    rw [hqt, div_mul_cancel₀ _ hd]
    ring
  have hnu : u.re^2 + u.im^2 = 1 := by
    have hn : ‖u‖ = 1 := by simpa using hu
    simpa [Complex.normSq_apply, pow_two] using
      (Complex.normSq_eq_norm_sq u).trans (by rw [hn]; norm_num)
  have hnv : v.re^2 + v.im^2 = 1 := by
    have hn : ‖v‖ = 1 := by simpa using hv
    simpa [Complex.normSq_apply, pow_two] using
      (Complex.normSq_eq_norm_sq v).trans (by rw [hn]; norm_num)
  have hnz : z.re^2 + z.im^2 = 1 := by
    have hn : ‖z‖ = 1 := by simpa using hz
    simpa [Complex.normSq_apply, pow_two] using
      (Complex.normSq_eq_norm_sq z).trans (by rw [hn]; norm_num)
  have hr : z.re = u.re + t * (v.re-u.re) := by
    rw [hzform]; simp [d]
  have hi : z.im = u.im + t * (v.im-u.im) := by
    rw [hzform]; simp [d]
  rw [hr, hi] at hnz
  have heq : t * (t-1) * ((v.re-u.re)^2 + (v.im-u.im)^2) = 0 := by
    linear_combination hnz - t * hnv + (t-1) * hnu
  have hnorm : (v.re-u.re)^2 + (v.im-u.im)^2 ≠ 0 := by
    intro h
    apply huv
    apply Complex.ext <;> nlinarith [sq_nonneg (v.re-u.re), sq_nonneg (v.im-u.im)]
  rcases mul_eq_zero.mp ((mul_eq_zero.mp heq).resolve_right hnorm) with ht | ht
  · left
    simpa [ht] using hzform
  · right
    have ht' : t = 1 := sub_eq_zero.mp ht
    simpa [ht', d] using hzform

/-- A chord between distinct circle points has circle points on both strict
sides. Source: elementary Euclidean geometry used in Cairns Lemma 5.1.
If d=v-u and w=conj(d)u, then Re(w)=-normSq(d)/2 is nonzero and
norm(w)=norm(d). Hence |Im(w)|<norm(d). The two unit normals ±Id/norm(d)
have chord determinants ±norm(d)-Im(w), which have opposite signs. -/
theorem circle_chord_both_signs {u v : ℂ}
    (hu : u ∈ sphere (0 : ℂ) 1) (hv : v ∈ sphere (0 : ℂ) 1)
    (huv : u ≠ v) :
    (∃ z ∈ sphere (0 : ℂ) 1, (conj (v-u)*(z-u)).im < 0) ∧
    (∃ z ∈ sphere (0 : ℂ) 1, 0 < (conj (v-u)*(z-u)).im) := by
  let d := v-u
  let w := conj d * u
  let r := ‖d‖
  have hd : d ≠ 0 := sub_ne_zero.mpr huv.symm
  have hr : 0 < r := norm_pos_iff.mpr hd
  have hnu : ‖u‖ = 1 := by simpa using hu
  have hnv : ‖v‖ = 1 := by simpa using hv
  have hnu' : u.re^2 + u.im^2 = 1 := by
    simpa [Complex.normSq_apply, pow_two] using
      (Complex.normSq_eq_norm_sq u).trans (by rw [hnu]; norm_num)
  have hnv' : v.re^2 + v.im^2 = 1 := by
    simpa [Complex.normSq_apply, pow_two] using
      (Complex.normSq_eq_norm_sq v).trans (by rw [hnv]; norm_num)
  have hr2 : r^2 = d.re^2+d.im^2 := by
    simpa [Complex.normSq_apply, pow_two] using (Complex.sq_norm d)
  have hwre : w.re = -(r^2)/2 := by
    simp only [w, Complex.mul_re, Complex.conj_re, Complex.conj_im]
    dsimp [d] at *
    nlinarith
  have hwnorm : ‖w‖ = r := by simp [w, hnu, r]
  have hwsq : w.re^2 + w.im^2 = r^2 := by
    calc
      _ = Complex.normSq w := by simp [Complex.normSq_apply, pow_two]
      _ = ‖w‖^2 := Complex.normSq_eq_norm_sq w
      _ = r^2 := by rw [hwnorm]
  have hwr : w.re ≠ 0 := by
    intro h
    rw [h] at hwre
    nlinarith [sq_pos_of_pos hr]
  have him : -r < w.im ∧ w.im < r := by
    have hre : 0 < w.re^2 := sq_pos_of_ne_zero hwr
    constructor <;> nlinarith [sq_nonneg (w.im-r), sq_nonneg (w.im+r)]
  let z := Complex.I * d / (r : ℂ)
  have hz : z ∈ sphere (0 : ℂ) 1 := by
    have hn : ‖z‖ = 1 := by simp [z, r, hd]
    simpa using hn
  have hdet : (conj d * z).im = r := by
    have heq : conj d * z = Complex.I * (r : ℂ) := by
      dsimp [z]
      rw [← mul_div_assoc]
      apply (div_eq_iff (Complex.ofReal_ne_zero.mpr hr.ne')).mpr
      calc
        conj d * (Complex.I * d) = Complex.I * (conj d * d) := by ring
        _ = Complex.I * (Complex.normSq d : ℂ) := by
          rw [← Complex.normSq_eq_conj_mul_self]
        _ = Complex.I * (r : ℂ) * (r : ℂ) := by
          rw [Complex.normSq_eq_norm_sq]
          simp only [r, Complex.ofReal_pow]
          ring
    rw [heq]
    simp
  constructor
  · refine ⟨-z, ?_, ?_⟩
    · simpa only [mem_sphere, dist_zero_right, norm_neg] using hz
    · change (conj d * (-z-u)).im < 0
      rw [mul_sub, mul_neg, Complex.sub_im, Complex.neg_im, hdet]
      exact sub_neg.mpr him.1
  · refine ⟨z, hz, ?_⟩
    change 0 < (conj d * (z-u)).im
    rw [mul_sub, Complex.sub_im, hdet]
    exact sub_pos.mpr him.2

/-- The two closed circle arcs cut by distinct endpoints are precisely the
signed closed half-plane sections for their chord. Source: Cairns Lemma 5.1,
elementary circle geometry. Split the circle into its two simple arcs. On each
open arc the continuous chord determinant has no zero, so has constant sign.
Both signs occur on the circle, hence on different arcs. Label by this sign;
the endpoints have determinant zero and belong to both closed arcs. -/
theorem circle_chord_signed_arcs {u v : ℂ}
    (hu : u ∈ sphere (0 : ℂ) 1) (hv : v ∈ sphere (0 : ℂ) 1)
    (huv : u ≠ v) :
    ∃ b : Fin 2 → unitInterval → ℂ,
      (∀ i, Topology.IsEmbedding (b i)) ∧
      (∀ i, b i 0 = u ∧ b i 1 = v) ∧
      (∀ i, range (b i) = {z | z ∈ sphere (0 : ℂ) 1 ∧
        if i = 0 then (conj (v-u)*(z-u)).im ≤ 0
        else 0 ≤ (conj (v-u)*(z-u)).im}) := by
  classical
  have hcircle : range (fun z : Circle ↦ (z : ℂ)) = sphere (0 : ℂ) 1 :=
    Subtype.range_coe
  obtain ⟨_, _, _, _, _, a, c, ha, hc, ha0, ha1, hc0, hc1, hcover, hmeet⟩ :=
    Topology.circle_split_two_arcs (fun z : Circle ↦ (z : ℂ))
      Topology.IsEmbedding.subtypeVal u v ⟨⟨u, hu⟩, rfl⟩ ⟨⟨v, hv⟩, rfl⟩ huv
  let e : Fin 2 → unitInterval → ℂ := ![a, c ∘ unitInterval.symm]
  have he (i) : Topology.IsEmbedding (e i) := by
    fin_cases i
    · exact ha
    · exact hc.comp unitInterval.symmHomeomorph.isEmbedding
  have he0 (i) : e i 0 = u := by fin_cases i <;> simp [e, ha0, hc1]
  have he1 (i) : e i 1 = v := by fin_cases i <;> simp [e, ha1, hc0]
  have hr0 : range (e 0) = range a := rfl
  have hr1 : range (e 1) = range c :=
    Topology.cairns_range_comp_unitInterval_symm c
  have hEcover : range (e 0) ∪ range (e 1) = sphere (0 : ℂ) 1 := by
    rw [hr0, hr1, hcover, hcircle]
  let B : Fin 2 → Set ℂ := fun i ↦ range (e i) \ {u,v}
  have hB (i) : IsConnected (B i) := by
    rw [show B i = e i '' Ioo 0 1 from
      Topology.cairns_embedded_seam_relative_interior _ u v (e i) (he i) rfl (he0 i) (he1 i)]
    exact (isConnected_Ioo (show (0 : unitInterval) < 1 by norm_num)).image
      (e i) (he i).continuous.continuousOn
  have hEs (i) : range (e i) ⊆ sphere (0 : ℂ) 1 := by
    fin_cases i
    · exact fun _ hz ↦ hEcover ▸ Or.inl hz
    · exact fun _ hz ↦ hEcover ▸ Or.inr hz
  let f : ℂ → ℝ := fun z ↦ (conj (v-u)*(z-u)).im
  have hf : Continuous f := Complex.continuous_im.comp (continuous_const.mul
    (continuous_id.sub continuous_const))
  have hf0 : f u = 0 := by simp [f]
  have hf1 : f v = 0 := by
    dsimp [f]
    rw [← Complex.normSq_eq_conj_mul_self]
    simp
  have hno (i) : ∀ z ∈ B i, f z ≠ 0 := by
    intro z hz hzero
    rcases circle_chord_det_eq_zero hu hv (hEs i hz.1) huv hzero with rfl | rfl
    · exact hz.2 (by simp)
    · exact hz.2 (by simp)
  have hBcover : B 0 ∪ B 1 = sphere (0 : ℂ) 1 \ {u,v} := by
    rw [← hEcover]
    exact union_sdiff_distrib.symm
  obtain ⟨⟨zn, hzn, hn⟩, ⟨zp, hzp, hp⟩⟩ := circle_chord_both_signs hu hv huv
  have hnB : zn ∈ B 0 ∪ B 1 := by
    rw [hBcover]
    refine ⟨hzn, ?_⟩
    rintro (rfl | rfl) <;> simp_all [f]
  have hpB : zp ∈ B 0 ∪ B 1 := by
    rw [hBcover]
    refine ⟨hzp, ?_⟩
    rintro (rfl | rfl) <;> simp_all [f]
  obtain ⟨j, hnj⟩ : ∃ j : Fin 2, zn ∈ B j := by
    rcases hnB with hnB | hnB
    · exact ⟨0, hnB⟩
    · exact ⟨1, hnB⟩
  obtain ⟨k, hpk⟩ : ∃ k : Fin 2, zp ∈ B k := by
    rcases hpB with hpB | hpB
    · exact ⟨0, hpB⟩
    · exact ⟨1, hpB⟩
  have hneg : ∀ z ∈ B j, f z < 0 := fun _ hz ↦ (hB j).isPreconnected.gt_of_ne
    hf.continuousOn (hno j) ⟨zn, hnj, hn⟩ hz
  have hpos : ∀ z ∈ B k, 0 < f z := fun _ hz ↦ (hB k).isPreconnected.lt_of_ne
    hf.continuousOn (hno k) ⟨zp, hpk, hp⟩ hz
  have hjk : j ≠ k := by
    intro h
    subst k
    exact (hneg zp hpk).not_gt hp
  have hcov : B j ∪ B k = sphere (0 : ℂ) 1 \ {u,v} := by
    fin_cases j <;> fin_cases k <;> simp_all [union_comm]
  have hend (i) : ({u,v} : Set ℂ) ⊆ range (e i) := by
    rintro z (rfl | rfl)
    · exact ⟨0, he0 i⟩
    · exact ⟨1, he1 i⟩
  have hnegative : range (e j) = {z | z ∈ sphere (0 : ℂ) 1 ∧ f z ≤ 0} := by
    ext z
    constructor
    · intro hz
      refine ⟨hEs j hz, ?_⟩
      by_cases hzE : z ∈ ({u,v} : Set ℂ)
      · rcases hzE with rfl | rfl <;> simp_all
      · exact (hneg z ⟨hz, hzE⟩).le
    · rintro ⟨hz, hfz⟩
      by_cases hzE : z ∈ ({u,v} : Set ℂ)
      · exact hend j hzE
      have hmem : z ∈ B j ∪ B k := hcov.symm ▸ (show z ∈ sphere (0 : ℂ) 1 \ {u,v} from ⟨hz,hzE⟩)
      rcases hmem with hmem | hmem
      · exact hmem.1
      · exact False.elim ((hpos z hmem).not_ge hfz)
  have hpositive : range (e k) = {z | z ∈ sphere (0 : ℂ) 1 ∧ 0 ≤ f z} := by
    ext z
    constructor
    · intro hz
      refine ⟨hEs k hz, ?_⟩
      by_cases hzE : z ∈ ({u,v} : Set ℂ)
      · rcases hzE with rfl | rfl <;> simp_all
      · exact (hpos z ⟨hz, hzE⟩).le
    · rintro ⟨hz, hfz⟩
      by_cases hzE : z ∈ ({u,v} : Set ℂ)
      · exact hend k hzE
      have hmem : z ∈ B j ∪ B k := hcov.symm ▸ (show z ∈ sphere (0 : ℂ) 1 \ {u,v} from ⟨hz,hzE⟩)
      rcases hmem with hmem | hmem
      · exact False.elim ((hneg z hmem).not_ge hfz)
      · exact hmem.1
  refine ⟨![e j, e k], ?_, ?_, ?_⟩
  · intro i; fin_cases i <;> exact he _
  · intro i; fin_cases i <;> exact ⟨he0 _, he1 _⟩
  · intro i; fin_cases i
    · simpa [f] using hnegative
    · simpa [f] using hpositive

end HolomorphicAnosov

