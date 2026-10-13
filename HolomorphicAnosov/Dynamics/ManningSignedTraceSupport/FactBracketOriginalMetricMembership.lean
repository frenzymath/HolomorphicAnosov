import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.MetricSpace.Pseudo.Pi
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Tactic.Linarith
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.CompatibleMetricModulus
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.ContinuousBracketDiagonalBuffer

namespace HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7.MetricAdapter

open Set Filter _root_.Topology
open scoped BigOperators ENNReal Classical
noncomputable section

/-- Shrink the SAME continuous Fact1 bracket to any positive original-metric plaque radius. Its diagonal buffer gives small adapted initial distances to both endpoints. The actual source pairwise contraction bounds keep every future and inverse adapted distance below this buffer, since 0≤kappa≤1. The compact identity modulus into the requested old radius proves all original closed plaque inequalities. No new tensor, bracket, partition or connectedness assumption is introduced; the source contract explicitly supplies these contraction estimates. -/
theorem fact_bracket_original_metric_membership {X : Type*}
 [new:MetricSpace X] [CompactSpace X]
 (F : @Homeomorph X X new.toUniformSpace.toTopologicalSpace new.toUniformSpace.toTopologicalSpace)
 {ε₀ κ:ℝ} (hε₀:0≤ε₀) (hκ0:0≤κ) (hκ1:κ≤1)
 (B:{p:X×X //new.dist p.1 p.2≤ε₀}→X) (hB:Continuous B)
 (hdiag:∀x:X,B ⟨(x,x),by simpa using hε₀⟩=x)
 (hs:∀p,∀n:ℕ,new.dist ((F^(n:ℤ)) (B p)) ((F^(n:ℤ)) p.val.1)≤κ^n*new.dist (B p) p.val.1)
 (hu:∀p,∀n:ℕ,new.dist ((F^(-(n:ℤ))) (B p)) ((F^(-(n:ℤ))) p.val.2)≤κ^n*new.dist (B p) p.val.2)
 (old:MetricSpace X)
 (ht : old.toUniformSpace.toTopologicalSpace = new.toUniformSpace.toTopologicalSpace)
 {b:ℝ} (hb:0<b) :
 ∃t>0,∀p:{p:X×X //new.dist p.1 p.2≤ε₀},new.dist p.val.1 p.val.2<t →
 (∀n:ℕ,old.dist ((F^(n:ℤ)) (B p)) ((F^(n:ℤ)) p.val.1)≤b) ∧
 (∀n:ℕ,old.dist ((F^(-(n:ℤ))) (B p)) ((F^(-(n:ℤ))) p.val.2)≤b) := by
 let:MetricSpace X:=new
 have holdcomp : @CompactSpace X old.toUniformSpace.toTopologicalSpace := ht.symm ▸
   (inferInstance : @CompactSpace X new.toUniformSpace.toTopologicalSpace)
 obtain ⟨r,hr,hmod⟩ := @compatible_metric_modulus X old holdcomp new ht.symm b hb
 obtain ⟨t,htpos,hbuf⟩ := continuous_bracket_diagonal_buffer hε₀ B hB hdiag hr
 refine ⟨t,htpos,?_⟩
 intro p hp
 have hbp := hbuf p hp
 constructor
 · intro n
   have hpow : κ^n≤1 := pow_le_one₀ hκ0 hκ1
   have hdist : new.dist ((F^(n:ℤ)) (B p)) ((F^(n:ℤ)) p.val.1)<r :=
    (hs p n).trans_lt ((mul_le_of_le_one_left (dist_nonneg) hpow).trans_lt hbp.1)
   exact (hmod _ _ hdist).le
 · intro n
   have hpow : κ^n≤1 := pow_le_one₀ hκ0 hκ1
   have hdist : new.dist ((F^(-(n:ℤ))) (B p)) ((F^(-(n:ℤ))) p.val.2)<r :=
    (hu p n).trans_lt ((mul_le_of_le_one_left (dist_nonneg) hpow).trans_lt hbp.2)
   exact (hmod _ _ hdist).le



end
end HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7.MetricAdapter
