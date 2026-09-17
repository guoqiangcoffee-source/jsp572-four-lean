import JSP572Four.PairGeometry
import JSP572Four.TwoBlockDegree

/-! Link counting for two disjoint four-element blocks. -/

namespace JSP572Four

open Finset

variable {α : Type*} [DecidableEq α]

def pairLink (Y : Finset α) (R : Finset (Finset α × Finset α)) (A : Finset α) :
    Finset (Finset α) :=
  (Y.powersetCard 2).filter (fun B => (A, B) ∈ R)

theorem two_block_link_sum_le_twelve
    (X Y : Finset α) (R : Finset (Finset α × Finset α))
    (hX : X.card = 4) (hY : Y.card = 4)
    (hcompatible : ∀ A ∈ X.powersetCard 2, ∀ B ∈ Y.powersetCard 2,
      ∀ C ∈ X.powersetCard 2, ∀ D ∈ Y.powersetCard 2,
      (A, B) ∈ R → (C, D) ∈ R → (A ∩ C).card + (B ∩ D).card ≠ 1) :
    ∑ A ∈ X.powersetCard 2, (pairLink Y R A).card ≤ 12 := by
  classical
  have hpairX : (X.powersetCard 2).card = 6 := by
    rw [Finset.card_powersetCard, hX]
    decide
  have hpairY : (Y.powersetCard 2).card = 6 := by
    rw [Finset.card_powersetCard, hY]
    decide
  have hlink (A : Finset α) : pairLink Y R A ⊆ Y.powersetCard 2 :=
    filter_subset _ _
  apply six_pair_degree_sum_le_twelve (X.powersetCard 2) (fun A => X \ A)
    (fun A => (pairLink Y R A).card) hpairX
    (fun A hA => pair_complement_mem hX hA)
    (fun A hA => pair_complement_involutive hA)
  · intro A hA
    exact (card_le_card (hlink A)).trans_eq hpairY
  · intro A hA hlarge
    by_contra hnonzero
    obtain ⟨B, hB⟩ := card_pos.mp (Nat.pos_of_ne_zero hnonzero)
    have hBY : B ∈ Y.powersetCard 2 := hlink _ hB
    have hBR : (X \ A, B) ∈ R := (mem_filter.mp hB).2
    have hsmall : (pairLink Y R A).card ≤ 2 := by
      apply pair_family_card_le_two_of_avoids_one_fixed_pair hY
        (mem_powersetCard.mp hBY).1 (mem_powersetCard.mp hBY).2 (hlink A)
      intro D hD
      have hDY : D ∈ Y.powersetCard 2 := hlink _ hD
      have hDR : (A, D) ∈ R := (mem_filter.mp hD).2
      have hh := hcompatible A hA D hDY (X \ A) (pair_complement_mem hX hA)
        B hBY hDR hBR
      simpa [Finset.inter_comm] using hh
    omega
  · intro A hA C hC hAC hCO
    have hrow : (A ∩ C).card = 1 :=
      pair_inter_card_one_of_ne_and_ne_complement hX
        (mem_powersetCard.mp hA).1 (mem_powersetCard.mp hC).1
        (mem_powersetCard.mp hA).2 (mem_powersetCard.mp hC).2 (Ne.symm hAC) hCO
    let K := (pairLink Y R C).image (fun D => Y \ D)
    have hKsub : K ⊆ Y.powersetCard 2 := by
      intro B hB
      obtain ⟨D, hD, rfl⟩ := mem_image.mp hB
      exact pair_complement_mem hY (hlink _ hD)
    have hKcard : K.card = (pairLink Y R C).card := by
      apply card_image_of_injOn
      intro B hB D hD hBD
      have hh := congrArg (fun S => Y \ S) hBD
      simpa only [pair_complement_involutive (hlink _ hB),
        pair_complement_involutive (hlink _ hD)] using hh
    have hdisjoint : Disjoint (pairLink Y R A) K := by
      apply Finset.disjoint_left.mpr
      intro B hB hBK
      obtain ⟨D, hD, rfl⟩ := mem_image.mp hBK
      have hDY : D ∈ Y.powersetCard 2 := hlink _ hD
      have hh := hcompatible A hA (Y \ D) (hlink _ hB) C hC D hDY
        (mem_filter.mp hB).2 (mem_filter.mp hD).2
      simp [hrow] at hh
    calc
      (pairLink Y R A).card + (pairLink Y R C).card =
          ((pairLink Y R A) ∪ K).card := by
            rw [card_union_of_disjoint hdisjoint, hKcard]
      _ ≤ (Y.powersetCard 2).card := card_le_card (union_subset (hlink A) hKsub)
      _ = 6 := hpairY

end JSP572Four
