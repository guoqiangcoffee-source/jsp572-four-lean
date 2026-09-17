import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.Linarith

/-! Elementary geometry of the six two-element subsets of a four-element set. -/

namespace JSP572Four

open Finset

variable {α : Type*} [DecidableEq α]

theorem pair_eq_or_complement_of_inter_card_ne_one
    {X A B : Finset α} (hX : X.card = 4)
    (hAX : A ⊆ X) (hBX : B ⊆ X) (hA : A.card = 2) (hB : B.card = 2)
    (havoid : (A ∩ B).card ≠ 1) : B = A ∨ B = X \ A := by
  have hle : (A ∩ B).card ≤ 2 := (card_le_card inter_subset_left).trans_eq hA
  have hcases : (A ∩ B).card = 0 ∨ (A ∩ B).card = 2 := by omega
  rcases hcases with hzero | htwo
  · right
    have hempty : A ∩ B = ∅ := card_eq_zero.mp hzero
    have hsub : B ⊆ X \ A := by
      intro x hx
      apply mem_sdiff.mpr
      refine ⟨hBX hx, ?_⟩
      intro hxa
      have hmem : x ∈ A ∩ B := mem_inter.mpr ⟨hxa, hx⟩
      rw [hempty] at hmem
      exact notMem_empty x hmem
    have hdiff : (X \ A).card = 2 := by
      rw [card_sdiff_of_subset hAX, hX, hA]
    exact eq_of_subset_of_card_le hsub (by omega)
  · left
    have heqA : A ∩ B = A := eq_of_subset_of_card_le inter_subset_left (by omega)
    have heqB : A ∩ B = B := eq_of_subset_of_card_le inter_subset_right (by omega)
    exact heqB.symm.trans heqA

theorem pair_inter_card_one_of_ne_and_ne_complement
    {X A B : Finset α} (hX : X.card = 4)
    (hAX : A ⊆ X) (hBX : B ⊆ X) (hA : A.card = 2) (hB : B.card = 2)
    (hne : B ≠ A) (hcomp : B ≠ X \ A) : (A ∩ B).card = 1 := by
  by_contra h
  exact (pair_eq_or_complement_of_inter_card_ne_one hX hAX hBX hA hB h).elim hne hcomp

theorem pair_complement_mem {X A : Finset α} (hX : X.card = 4)
    (hA : A ∈ X.powersetCard 2) : X \ A ∈ X.powersetCard 2 := by
  rcases mem_powersetCard.mp hA with ⟨hAX, hAc⟩
  apply mem_powersetCard.mpr
  refine ⟨sdiff_subset, ?_⟩
  rw [card_sdiff_of_subset hAX, hX, hAc]

theorem pair_complement_involutive {X A : Finset α}
    (hA : A ∈ X.powersetCard 2) : X \ (X \ A) = A :=
  Finset.sdiff_sdiff_eq_self (mem_powersetCard.mp hA).1

theorem pair_family_card_le_two_of_avoids_one_fixed_pair
    {X A : Finset α} {L : Finset (Finset α)} (hX : X.card = 4)
    (hAX : A ⊆ X) (hA : A.card = 2)
    (hL : L ⊆ X.powersetCard 2)
    (havoid : ∀ B ∈ L, (A ∩ B).card ≠ 1) : L.card ≤ 2 := by
  have hsub : L ⊆ {A, X \ A} := by
    intro B hB
    rcases mem_powersetCard.mp (hL hB) with ⟨hBX, hBc⟩
    rcases pair_eq_or_complement_of_inter_card_ne_one hX hAX hBX hA hBc
      (havoid B hB) with hEq | hEq
    · simp [hEq]
    · simp [hEq]
  exact (card_le_card hsub).trans (card_insert_le _ _ |>.trans (by simp))

end JSP572Four
