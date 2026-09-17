import JSP572Four.TwoIntersectingBound
import JSP572Four.GlobalCounting
import JSP572Four.ResidualCCount
import JSP572Four.ResidualDCount
import JSP572Four.ResidualECount

/-!
The complete numerical four-uniform theorem: all natural-number ground sizes,
unconditional upper bounds, and matching constructions attaining every bound.
No uniqueness claim about equality cases is included.
-/

namespace JSP572Four
open Finset
variable {α : Type*} [DecidableEq α]

theorem nonintersecting_four_bound {X : Finset α} {F : Finset (Finset α)}
    (hX : Supported X F) (hu : Uniform 4 F) (hn : NoSingleton F)
    (hd : ∃ A ∈ F, ∃ B ∈ F, Disjoint A B) :
    F.card ≤ (X.card - 2).choose 2 := by
  classical
  obtain ⟨M, hm⟩ := exists_maximumMatching F
  let B := X \ covered M
  let C := residualC F M B
  let D := residualD F M B
  let E := residualE F M B
  have ht := maximumMatching_card_ge_two hu hm hd
  have hcover := global_card_cover (M := M) hX
  have hint := internal_matching_card_bound hu hn hm
  have hc := residualC_count_le hX hu hn hm
  have hdc := residualD_count_le hX hu hn hm
  have he := residualE_count hX hu hn hm
  have hB : Disjoint B (covered M) := disjoint_sdiff_self_left
  have hCcard := card_residualC hn hm.2.1 hB
  have hcluster := sum_clusterExtraBound_quadratic M
    (fun Q => (colourSupport F M B Q).card)
    (fun Q hQ => colourSupport_card_zero_or_three hn hm.2.1 hB hQ)
  rw [← hCcard] at hcluster
  have hc2 : 2 * (F.filter (fun S => ¬ Disjoint S C)).card ≤ C.card ^ 2 + 7 * C.card :=
    (Nat.mul_le_mul_left 2 hc).trans hcluster
  have hd2 := Nat.mul_le_mul_left 2 hdc
  have hmax : 2 * max (3 * M.card) 7 = max (6 * M.card) 14 := by omega
  rw [← Nat.mul_assoc, hmax] at hd2
  have hbound : 2 * F.card + 10 * M.card ≤
      12 * M.card ^ 2 + max (6 * M.card) 14 * D.card + 8 * E.card + C.card ^ 2 + 7 * C.card := by
    change F.card ≤ _ + (F.filter (fun S => ¬ Disjoint S C)).card +
      (F.filter (fun S => ¬ Disjoint S D)).card +
      (F.filter (fun S => ¬ Disjoint S E)).card at hcover
    change 2 * (F.filter (fun S => ¬ Disjoint S D)).card ≤ max (6 * M.card) 14 * D.card at hd2
    change (F.filter (fun S => ¬ Disjoint S E)).card ≤ 4 * E.card at he
    omega
  have hdgap : D.card = 0 ∨ 2 ≤ D.card := isolated_union_card_zero_or_two F M B
  have hb := matching_bound_of_partition_counts F.card M.card C.card D.card E.card ht hdgap hbound
  have hpartition := ground_partition_card hX hu hm
  change X.card = 4 * M.card + C.card + D.card + E.card at hpartition
  rwa [← hpartition] at hb

/-- The sharp upper bound, on an arbitrary finite ground set. -/
theorem singletonFree_four_bound {X : Finset α} {F : Finset (Finset α)}
    (hX : Supported X F) (hu : Uniform 4 F) (hn : NoSingleton F) :
    F.card ≤ sharpBound X.card := by
  classical
  by_cases hi : TwoIntersecting F
  · exact twoIntersecting_bound hX hu hi
  have hd : ∃ A ∈ F, ∃ B ∈ F, Disjoint A B := by
    by_contra! h
    exact hi (twoIntersecting_of_no_disjoint hn h)
  have hb := nonintersecting_four_bound hX hu hn hd
  obtain ⟨A, hA, B, hB, hAB⟩ := hd
  have h8 := nonintersecting_ground_large (hX A hA) (hX B hB) (hu A hA) (hu B hB) hAB
  by_cases he : X.card = 8
  · rw [he] at hb
    simpa [sharpBound, he] using hb.trans (by decide : (8 - 2).choose 2 ≤ 17)
  · simpa [sharpBound, show ¬ X.card ≤ 6 by omega, show X.card ≠ 7 by omega, he] using hb

/-- The official numerical statement, with every natural-number ground size quantified. -/
theorem singletonFree_four_bound_fin {n : ℕ} {F : Finset (Finset (Fin n))}
    (hu : Uniform 4 F) (hn : NoSingleton F) : F.card ≤ sharpBound n := by
  simpa using singletonFree_four_bound (X := univ) (fun S _ => subset_univ S) hu hn

/-- Complete exact extremal value: an upper bound for every family, attained by a family. -/
theorem exact_extremal_value (n : ℕ) :
    (∀ F : Finset (Finset (Fin n)), Uniform 4 F → NoSingleton F → F.card ≤ sharpBound n) ∧
    ∃ F : Finset (Finset (Fin n)), Uniform 4 F ∧ NoSingleton F ∧ F.card = sharpBound n := by
  exact ⟨fun _ hu hn => singletonFree_four_bound_fin hu hn, sharpBound_attained n⟩

/-- Single entry point combining a maximizing witness with universal optimality. -/
theorem jsp572_four_complete :
    ∀ n : ℕ, ∃ F : Finset (Finset (Fin n)),
      Uniform 4 F ∧ NoSingleton F ∧ F.card = sharpBound n ∧
      ∀ G : Finset (Finset (Fin n)), Uniform 4 G → NoSingleton G → G.card ≤ F.card := by
  intro n
  obtain ⟨F, hu, hn, hc⟩ := sharpBound_attained n
  refine ⟨F, hu, hn, hc, ?_⟩
  intro G hG hN
  rw [hc]
  exact singletonFree_four_bound_fin hG hN

end JSP572Four
