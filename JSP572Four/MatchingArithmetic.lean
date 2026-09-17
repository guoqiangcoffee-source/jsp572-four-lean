import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
Elementary arithmetic for the nonintersecting branch of the four-uniform
no-singleton-intersection theorem. This module avoids the more precise
variational estimate in Keevash--Mubayi--Wilson, Section 3; its weaker
intermediate estimate still suffices for the numerical upper bound.
-/

namespace JSP572Four

open Finset

/-- Maximum permitted size of a two-intersecting cluster, after its matching
block is removed. The geometry supplies `c = 0 ∨ 3 ≤ c`. -/
def clusterExtraBound (c : ℕ) : ℕ :=
  if c = 0 then 0 else if c = 3 then 14 else if c = 4 then 16
  else (c + 2).choose 2 - 1

theorem clusterExtraBound_quadratic (c : ℕ) (hc : c = 0 ∨ 3 ≤ c) :
    2 * clusterExtraBound c ≤ c ^ 2 + 7 * c := by
  by_cases h0 : c = 0
  · subst c
    norm_num [clusterExtraBound]
  by_cases h3 : c = 3
  · subst c
    norm_num [clusterExtraBound]
  by_cases h4 : c = 4
  · subst c
    norm_num [clusterExtraBound]
  have hc5 : 5 ≤ c := by omega
  simp only [clusterExtraBound, h0, h3, h4, ite_false, Nat.choose_two_right]
  have hsub : c + 2 - 1 = c + 1 := by omega
  rw [hsub]
  have hd : 2 * ((c + 2) * (c + 1) / 2) ≤ (c + 2) * (c + 1) := by
    simpa [Nat.mul_comm] using Nat.div_mul_le_self ((c + 2) * (c + 1)) 2
  have hs : (c + 2) * (c + 1) / 2 - 1 ≤ (c + 2) * (c + 1) / 2 :=
    Nat.sub_le _ _
  nlinarith

theorem sum_clusterExtraBound_quadratic {ι : Type*} (s : Finset ι)
    (c : ι → ℕ) (hc : ∀ i ∈ s, c i = 0 ∨ 3 ≤ c i) :
    2 * ∑ i ∈ s, clusterExtraBound (c i) ≤
      (∑ i ∈ s, c i) ^ 2 + 7 * ∑ i ∈ s, c i := by
  have hb := Finset.sum_le_sum (fun i hi => clusterExtraBound_quadratic (c i) (hc i hi))
  have hs : (∑ i ∈ s, (c i) ^ 2) ≤ (∑ i ∈ s, c i) ^ 2 :=
    sum_sq_le_sq_sum_of_nonneg (fun _ _ => Nat.zero_le _)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hb
  omega

/-- Pure integer comparison after partitioning the residual vertices into
colored clusters, isolated pairs, and singleton leftovers. -/
theorem matching_polynomial_comparison (t c d e : ℤ)
    (ht : 2 ≤ t) (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e)
    (hdgap : d = 0 ∨ 2 ≤ d) :
    12 * t ^ 2 - 10 * t + max (6 * t) 14 * d + 8 * e + c ^ 2 + 7 * c ≤
      (4 * t + c + d + e - 2) * (4 * t + c + d + e - 3) := by
  by_cases ht2 : t = 2
  · subst t
    norm_num
    have hdd : 0 ≤ d ^ 2 - 3 * d + 2 := by
      rcases hdgap with rfl | hd2
      · norm_num
      · have := mul_nonneg (show 0 ≤ d - 1 by omega) (show 0 ≤ d - 2 by omega)
        nlinarith
    have hcd := mul_nonneg hc hd
    have hce := mul_nonneg hc he
    have hde := mul_nonneg hd he
    have hee := sq_nonneg e
    nlinarith
  · have ht3 : 3 ≤ t := by omega
    rw [max_eq_left (by omega : 14 ≤ 6 * t)]
    have hb := mul_nonneg (show 0 ≤ 2 * t - 3 by omega)
      (show 0 ≤ t - 1 by omega)
    have htc := mul_nonneg (show 0 ≤ 8 * t - 12 by omega) hc
    have htd := mul_nonneg (show 0 ≤ 2 * t - 5 by omega) hd
    have hte := mul_nonneg (show 0 ≤ 8 * t - 13 by omega) he
    have hcross := mul_nonneg hc (show 0 ≤ d + e by omega)
    have hsq := sq_nonneg (d + e)
    nlinarith

/-- Natural-number interface for the final cardinal comparison. The input
inequality avoids truncated subtraction in the internal matching bound. -/
theorem matching_bound_of_partition_counts (q t c d e : ℕ)
    (ht : 2 ≤ t) (hdgap : d = 0 ∨ 2 ≤ d)
    (hbound : 2 * q + 10 * t ≤
      12 * t ^ 2 + max (6 * t) 14 * d + 8 * e + c ^ 2 + 7 * c) :
    q ≤ (4 * t + c + d + e - 2).choose 2 := by
  have htZ : (2 : ℤ) ≤ t := by exact_mod_cast ht
  have hdZ : (d : ℤ) = 0 ∨ 2 ≤ (d : ℤ) := by exact_mod_cast hdgap
  have hp := matching_polynomial_comparison (t : ℤ) c d e htZ
    (Int.natCast_nonneg c) (Int.natCast_nonneg d) (Int.natCast_nonneg e) hdZ
  have hb : (2 : ℤ) * q + 10 * t ≤
      12 * (t : ℤ) ^ 2 + max (6 * (t : ℤ)) 14 * d + 8 * e + (c : ℤ) ^ 2 + 7 * c := by
    exact_mod_cast hbound
  let n := 4 * t + c + d + e
  have hn : 8 ≤ n := by dsimp [n]; omega
  have hnZ : (n : ℤ) = 4 * (t : ℤ) + c + d + e := by simp [n]
  have hm2 : ((n - 2 : ℕ) : ℤ) = (n : ℤ) - 2 := by omega
  have hm3 : ((n - 3 : ℕ) : ℤ) = (n : ℤ) - 3 := by omega
  have hprodZ : (q : ℤ) * 2 ≤ ((n - 2 : ℕ) : ℤ) * ((n - 3 : ℕ) : ℤ) := by
    rw [hm2, hm3, hnZ]
    linarith
  have hprod : q * 2 ≤ (n - 2) * (n - 3) := by exact_mod_cast hprodZ
  change q ≤ (n - 2).choose 2
  rw [Nat.choose_two_right]
  apply (Nat.le_div_iff_mul_le (by decide : 0 < 2)).mpr
  have hsub : n - 2 - 1 = n - 3 := by omega
  simpa only [hsub] using hprod

end JSP572Four
