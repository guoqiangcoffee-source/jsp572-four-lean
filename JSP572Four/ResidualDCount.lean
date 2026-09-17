import JSP572Four.ResidualPartition
import JSP572Four.MatchingStructure

/-! Counting members meeting the isolated residual pairs. -/

namespace JSP572Four

open Finset

variable {α : Type*} [DecidableEq α]

theorem residual_singleton_meeting_pair_subset
    {S B p : Finset α} (hpB : p ⊆ B)
    (hcard : (S ∩ B).card = 1) (hmeet : ¬ Disjoint S p) : S ∩ B ⊆ p := by
  obtain ⟨x, hxS, hxp⟩ := not_disjoint_iff.mp hmeet
  have hpos : 0 < ((S ∩ B) ∩ p).card :=
    card_pos.mpr ⟨x, mem_inter.mpr ⟨mem_inter.mpr ⟨hxS, hpB hxp⟩, hxp⟩⟩
  have hle : ((S ∩ B) ∩ p).card ≤ 1 := (card_le_card inter_subset_left).trans_eq hcard
  have heq : (S ∩ B) ∩ p = S ∩ B := eq_of_subset_of_card_le inter_subset_left (by omega)
  rw [← heq]
  exact inter_subset_right

theorem residual_singleton_anchor_eq_colour
    {F M : Finset (Finset α)} {S B Q R p : Finset α}
    (hn : NoSingleton F) (hM : Matching M) (hB : Disjoint B (covered M))
    (hQ : Q ∈ M) (hR : R ∈ M) (hSF : S ∈ F) (hsub : S ⊆ Q ∪ B)
    (hpB : p ⊆ B) (hcard : (S ∩ B).card = 1)
    (hmeet : ¬ Disjoint S p) (hcolour : ColouredBy F R p) : Q = R := by
  by_contra hQR
  obtain ⟨a, ha, haF⟩ := hcolour
  have hpS := residual_singleton_meeting_pair_subset hpB hcard hmeet
  have hinter := residual_witness_inter hM hQ hR hQR hB
    (inter_subset_right : S ∩ Q ⊆ Q) (mem_powersetCard.mp ha).1
    (inter_subset_right : S ∩ B ⊆ B) hpB
  have hdec := member_decomposition hsub
  have hh := hn S hSF (a ∪ p) haF
  apply hh
  calc
    (S ∩ (a ∪ p)).card = ((S ∩ B) ∩ p).card := by
      conv_lhs => rw [hdec]
      rw [hinter]
    _ = (S ∩ B).card := by rw [Finset.inter_eq_left.mpr hpS]
    _ = 1 := hcard

/-- A member meeting an isolated pair lives over one of its colors. If the
member does not contain the whole pair, this color is its only color. -/
theorem isolated_pair_member_structure
    {X S p : Finset α} {F M : Finset (Finset α)}
    (hX : Supported X F) (hU : Uniform 4 F) (hn : NoSingleton F)
    (hM : MaximumMatching F M) (hSF : S ∈ F)
    (hp : p ∈ isolatedPairs F M (X \ covered M)) (hmeet : ¬ Disjoint S p) :
    ∃ Q ∈ M, ColouredBy F Q p ∧ S ⊆ Q ∪ p ∧
      (p ⊆ S ∨ ∀ R ∈ M, ColouredBy F R p → R = Q) := by
  classical
  let B := X \ covered M
  have hB : Disjoint B (covered M) := disjoint_sdiff_self_left
  have hpcol : p ∈ colouredPairs F M B := (mem_filter.mp hp).1
  obtain ⟨hpPow, R, hRM, hpR⟩ := mem_colouredPairs.mp hpcol
  have hpB : p ⊆ B := (mem_powersetCard.mp hpPow).1
  obtain ⟨x, hxS, hxp⟩ := not_disjoint_iff.mp hmeet
  have hres : (S ∩ B).Nonempty := ⟨x, mem_inter.mpr ⟨hxS, hpB hxp⟩⟩
  obtain ⟨Q, hQM, hSQB, hcounts⟩ := residual_member_anchor_counts hX hU hn hM hSF hres
  have hdec : S = (S ∩ Q) ∪ (S ∩ B) := member_decomposition hSQB
  rcases hcounts with ⟨hQ2, hB2⟩ | ⟨hQ3, hB1⟩
  · have hcolour : ColouredBy F Q (S ∩ B) := by
      refine ⟨S ∩ Q, mem_powersetCard.mpr ⟨inter_subset_right, hQ2⟩, ?_⟩
      rw [← hdec]
      exact hSF
    have hcol : S ∩ B ∈ colouredPairs F M B := mem_colouredPairs.mpr
      ⟨mem_powersetCard.mpr ⟨inter_subset_right, hB2⟩, Q, hQM, hcolour⟩
    have heq : p = S ∩ B := by
      by_contra hne
      have hd := (mem_filter.mp hp).2 (S ∩ B) hcol hne
      exact disjoint_left.mp hd hxp (mem_inter.mpr ⟨hxS, hpB hxp⟩)
    refine ⟨Q, hQM, ?_, ?_, Or.inl ?_⟩
    · simpa only [heq] using hcolour
    · calc
        S = (S ∩ Q) ∪ (S ∩ B) := hdec
        _ ⊆ Q ∪ p := union_subset (inter_subset_right.trans subset_union_left)
          (by rw [← heq]; exact subset_union_right)
    · rw [heq]
      exact inter_subset_left
  · have hQR : Q = R := residual_singleton_anchor_eq_colour hn hM.2.1 hB
      hQM hRM hSF hSQB hpB hB1 hmeet hpR
    have hpS := residual_singleton_meeting_pair_subset hpB hB1 hmeet
    refine ⟨Q, hQM, hQR ▸ hpR, ?_, Or.inr ?_⟩
    · rw [hdec]
      exact union_subset (inter_subset_right.trans subset_union_left)
        (hpS.trans subset_union_right)
    · intro T hTM hpT
      exact (residual_singleton_anchor_eq_colour hn hM.2.1 hB
        hQM hTM hSF hSQB hpB hB1 hmeet hpT).symm

theorem meeting_pair_card_le_fourteen_of_local_support
    {F : Finset (Finset α)} {Q p : Finset α}
    (hU : Uniform 4 F) (hQ : Q.card = 4) (hp : p.card = 2)
    (hdis : Disjoint Q p)
    (hsupport : ∀ S ∈ F, ¬ Disjoint S p → S ⊆ Q ∪ p) :
    (F.filter (fun S => ¬ Disjoint S p)).card ≤ 14 := by
  classical
  have hsub : F.filter (fun S => ¬ Disjoint S p) ⊆ ((Q ∪ p).powersetCard 4).erase Q := by
    intro S hS
    obtain ⟨hSF, hmeet⟩ := mem_filter.mp hS
    apply mem_erase.mpr
    refine ⟨?_, mem_powersetCard.mpr ⟨hsupport S hSF hmeet, hU S hSF⟩⟩
    intro heq
    exact hmeet (heq ▸ hdis)
  have hQc : Q ∈ (Q ∪ p).powersetCard 4 :=
    mem_powersetCard.mpr ⟨subset_union_left, hQ⟩
  have hground : (Q ∪ p).card = 6 := by rw [card_union_of_disjoint hdis, hQ, hp]
  have hcount : (((Q ∪ p).powersetCard 4).erase Q).card = 14 := by
    rw [card_erase_of_mem hQc, card_powersetCard, hground]
    decide
  exact (card_le_card hsub).trans_eq hcount

theorem meeting_pair_card_le_six_mul_of_pair_contained
    {F M : Finset (Finset α)} {p : Finset α}
    (hU : Uniform 4 F) (hUM : Uniform 4 M) (hp : p.card = 2)
    (hsupport : ∀ S ∈ F, ¬ Disjoint S p →
      p ⊆ S ∧ ∃ Q ∈ M, S ⊆ Q ∪ p) :
    (F.filter (fun S => ¬ Disjoint S p)).card ≤ 6 * M.card := by
  classical
  have hcover : F.filter (fun S => ¬ Disjoint S p) ⊆
      M.biUnion (fun Q => (Q.powersetCard 2).image (fun a => a ∪ p)) := by
    intro S hS
    obtain ⟨hSF, hmeet⟩ := mem_filter.mp hS
    obtain ⟨hpS, Q, hQM, hSQ⟩ := hsupport S hSF hmeet
    have hdiff : S \ p ⊆ Q := by
      intro x hx
      obtain ⟨hxS, hxp⟩ := mem_sdiff.mp hx
      exact (mem_union.mp (hSQ hxS)).resolve_right hxp
    have hcard : (S \ p).card = 2 := by
      rw [card_sdiff_of_subset hpS, hU S hSF, hp]
    apply mem_biUnion.mpr
    refine ⟨Q, hQM, mem_image.mpr ⟨S \ p, mem_powersetCard.mpr ⟨hdiff, hcard⟩, ?_⟩⟩
    exact Finset.sdiff_union_of_subset hpS
  calc
    (F.filter (fun S => ¬ Disjoint S p)).card ≤
        (M.biUnion (fun Q => (Q.powersetCard 2).image (fun a => a ∪ p))).card := card_le_card hcover
    _ ≤ ∑ Q ∈ M, ((Q.powersetCard 2).image (fun a => a ∪ p)).card := card_biUnion_le
    _ ≤ ∑ Q ∈ M, (Q.powersetCard 2).card := sum_le_sum (fun _ _ => card_image_le)
    _ = ∑ _Q ∈ M, 6 := by
      apply sum_congr rfl
      intro Q hQM
      rw [card_powersetCard, hUM Q hQM]
      decide
    _ = 6 * M.card := by simp [Nat.mul_comm]

theorem isolated_pair_meeting_card_le_max
    {X p : Finset α} {F M : Finset (Finset α)}
    (hX : Supported X F) (hU : Uniform 4 F) (hn : NoSingleton F)
    (hM : MaximumMatching F M)
    (hp : p ∈ isolatedPairs F M (X \ covered M)) :
    (F.filter (fun S => ¬ Disjoint S p)).card ≤ max (6 * M.card) 14 := by
  classical
  have hpcol := (mem_filter.mp hp).1
  obtain ⟨hpPow, Q, hQM, hpQ⟩ := mem_colouredPairs.mp hpcol
  have hp2 : p.card = 2 := (mem_powersetCard.mp hpPow).2
  have hpB : p ⊆ X \ covered M := (mem_powersetCard.mp hpPow).1
  by_cases hunique : ∀ R ∈ M, ColouredBy F R p → R = Q
  · have hQp : Disjoint Q p :=
      (disjoint_sdiff_self_left.mono hpB (subset_covered hQM)).symm
    have hsupp : ∀ S ∈ F, ¬ Disjoint S p → S ⊆ Q ∪ p := by
      intro S hSF hmeet
      obtain ⟨R, hRM, hpR, hSR, _⟩ := isolated_pair_member_structure hX hU hn hM hSF hp hmeet
      simpa only [hunique R hRM hpR] using hSR
    exact (meeting_pair_card_le_fourteen_of_local_support hU (hU Q (hM.1 hQM))
      hp2 hQp hsupp).trans (le_max_right _ _)
  · have hsupp : ∀ S ∈ F, ¬ Disjoint S p →
        p ⊆ S ∧ ∃ R ∈ M, S ⊆ R ∪ p := by
      intro S hSF hmeet
      obtain ⟨R, hRM, hpR, hSR, hcases⟩ := isolated_pair_member_structure hX hU hn hM hSF hp hmeet
      refine ⟨?_, R, hRM, hSR⟩
      rcases hcases with hpS | hAll
      · exact hpS
      · exfalso
        apply hunique
        intro T hTM hpT
        exact (hAll T hTM hpT).trans (hAll Q hQM hpQ).symm
    exact (meeting_pair_card_le_six_mul_of_pair_contained hU
      (fun R hR => hU R (hM.1 hR)) hp2 hsupp).trans (le_max_left _ _)

/-- The isolated residual pairs contribute at most `max (3t) 7` members per
vertex, where `t` is the size of the maximum matching. -/
theorem residualD_count_le
    {X : Finset α} {F M : Finset (Finset α)}
    (hX : Supported X F) (hU : Uniform 4 F) (hn : NoSingleton F)
    (hM : MaximumMatching F M) :
    (F.filter (fun S => ¬ Disjoint S (residualD F M (X \ covered M)))).card ≤
      max (3 * M.card) 7 * (residualD F M (X \ covered M)).card := by
  classical
  let B := X \ covered M
  let P := isolatedPairs F M B
  have hcover : F.filter (fun S => ¬ Disjoint S (residualD F M B)) ⊆
      P.biUnion (fun p => F.filter (fun S => ¬ Disjoint S p)) := by
    intro S hS
    obtain ⟨hSF, hmeet⟩ := mem_filter.mp hS
    obtain ⟨x, hxS, hxD⟩ := not_disjoint_iff.mp hmeet
    obtain ⟨p, hpP, hxp⟩ := mem_biUnion.mp hxD
    apply mem_biUnion.mpr
    refine ⟨p, hpP, mem_filter.mpr ⟨hSF, ?_⟩⟩
    exact not_disjoint_iff.mpr ⟨x, hxS, hxp⟩
  have hD : (residualD F M B).card = 2 * P.card := isolated_union_card F M B
  have hmax : max (6 * M.card) 14 = 2 * max (3 * M.card) 7 := by omega
  calc
    (F.filter (fun S => ¬ Disjoint S (residualD F M (X \ covered M)))).card ≤
        (P.biUnion (fun p => F.filter (fun S => ¬ Disjoint S p))).card := card_le_card hcover
    _ ≤ ∑ p ∈ P, (F.filter (fun S => ¬ Disjoint S p)).card := card_biUnion_le
    _ ≤ ∑ _p ∈ P, max (6 * M.card) 14 :=
      sum_le_sum (fun p hp => isolated_pair_meeting_card_le_max hX hU hn hM hp)
    _ = max (3 * M.card) 7 * (residualD F M (X \ covered M)).card := by
      change (∑ _p ∈ P, max (6 * M.card) 14) =
        max (3 * M.card) 7 * (residualD F M B).card
      rw [hD, hmax]
      simp [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]

end JSP572Four
