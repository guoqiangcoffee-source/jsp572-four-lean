import JSP572Four.Basic
import Mathlib.Tactic

namespace JSP572Four
open Finset

variable {α : Type*} [DecidableEq α]

omit [DecidableEq α] in
theorem card_le_choose {X : Finset α} {F : Finset (Finset α)} {k : ℕ}
    (hX : Supported X F) (hF : Uniform k F) : F.card ≤ X.card.choose k := by
  calc
    F.card ≤ (X.powersetCard k).card := card_le_card (by
      intro A hA
      exact mem_powersetCard.mpr ⟨hX A hA, hF A hA⟩)
    _ = X.card.choose k := card_powersetCard k X

omit [DecidableEq α] in
theorem uniform_powersetCard (X : Finset α) (k : ℕ) :
    Uniform k (X.powersetCard k) := by
  intro A hA
  exact (mem_powersetCard.mp hA).2

omit [DecidableEq α] in
theorem supported_powersetCard (X : Finset α) (k : ℕ) :
    Supported X (X.powersetCard k) := by
  intro A hA
  exact (mem_powersetCard.mp hA).1

theorem twoIntersecting_of_small {X : Finset α} {F : Finset (Finset α)}
    (hX : Supported X F) (hF : Uniform 4 F) (hn : X.card ≤ 6) :
    TwoIntersecting F := by
  intro A hA B hB
  have hU : (A ∪ B).card ≤ X.card := card_le_card (union_subset (hX A hA) (hX B hB))
  have hi := card_union_add_card_inter A B
  have ha := hF A hA
  have hb := hF B hB
  omega

theorem TwoIntersecting.noSingleton {F : Finset (Finset α)}
    (hF : TwoIntersecting F) : NoSingleton F := by
  intro A hA B hB
  have := hF A hA B hB
  omega

theorem small_attainment (X : Finset α) (hn : X.card ≤ 6) :
    ∃ F : Finset (Finset α), Supported X F ∧ Uniform 4 F ∧
      NoSingleton F ∧ F.card = X.card.choose 4 := by
  refine ⟨X.powersetCard 4, supported_powersetCard X 4,
    uniform_powersetCard X 4, ?_, card_powersetCard 4 X⟩
  exact (twoIntersecting_of_small (supported_powersetCard X 4)
    (uniform_powersetCard X 4) hn).noSingleton

/-- All four-sets obtained by adjoining two new points to a fixed pair. -/
def pairStar (X P : Finset α) : Finset (Finset α) :=
  ((X \ P).powersetCard 2).image (fun B => P ∪ B)

theorem pairStar_properties {X P : Finset α} (hPX : P ⊆ X) (hP : P.card = 2) :
    Supported X (pairStar X P) ∧ Uniform 4 (pairStar X P) ∧
    TwoIntersecting (pairStar X P) ∧
    (pairStar X P).card = (X.card - 2).choose 2 := by
  have hdis : ∀ B ∈ (X \ P).powersetCard 2, Disjoint P B := by
    intro B hB
    exact disjoint_sdiff_self_right.mono_right (mem_powersetCard.mp hB).1
  have hsub : ∀ B ∈ (X \ P).powersetCard 2, B ⊆ X := by
    intro B hB
    exact (mem_powersetCard.mp hB).1.trans sdiff_subset
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro A hA
    obtain ⟨B, hB, rfl⟩ := mem_image.mp hA
    exact union_subset hPX (hsub B hB)
  · intro A hA
    obtain ⟨B, hB, rfl⟩ := mem_image.mp hA
    rw [card_union_of_disjoint (hdis B hB), hP, (mem_powersetCard.mp hB).2]
  · intro A hA B hB
    obtain ⟨S, hS, rfl⟩ := mem_image.mp hA
    obtain ⟨T, hT, rfl⟩ := mem_image.mp hB
    simpa [hP] using card_le_card (subset_inter (subset_union_left : P ⊆ P ∪ S)
      (subset_union_left : P ⊆ P ∪ T))
  · unfold pairStar
    rw [card_image_iff.mpr ?_]
    · rw [card_powersetCard, card_sdiff_of_subset hPX, hP]
    · intro B hB C hC heq
      change P ∪ B = P ∪ C at heq
      have hb := (mem_powersetCard.mp hB).1
      have hc := (mem_powersetCard.mp hC).1
      apply Subset.antisymm
      · intro x hx
        have hxP : x ∉ P := (mem_sdiff.mp (hb hx)).2
        have hxU : x ∈ P ∪ C := by rw [← heq]; exact mem_union_right P hx
        exact (mem_union.mp hxU).resolve_left hxP
      · intro x hx
        have hxP : x ∉ P := (mem_sdiff.mp (hc hx)).2
        have hxU : x ∈ P ∪ B := by rw [heq]; exact mem_union_right P hx
        exact (mem_union.mp hxU).resolve_left hxP

theorem pairStar_attainment (X : Finset α) (hn : 2 ≤ X.card) :
    ∃ F : Finset (Finset α), Supported X F ∧ Uniform 4 F ∧
      NoSingleton F ∧ F.card = (X.card - 2).choose 2 := by
  obtain ⟨P, hPX, hP⟩ := exists_subset_card_eq hn
  obtain ⟨hS, hU, hI, hC⟩ := pairStar_properties hPX hP
  exact ⟨pairStar X P, hS, hU, hI.noSingleton, hC⟩

theorem twoIntersecting_of_three_core {C : Finset α} {F : Finset (Finset α)}
    (hC : C.card = 4) (hF : ∀ A ∈ F, 3 ≤ (A ∩ C).card) :
    TwoIntersecting F := by
  intro A hA B hB
  have hU : ((A ∩ C) ∪ (B ∩ C)).card ≤ C.card :=
    card_le_card (union_subset inter_subset_right inter_subset_right)
  have hI : ((A ∩ C) ∩ (B ∩ C)).card ≤ (A ∩ B).card :=
    card_le_card (by intro x hx; simp only [mem_inter] at hx ⊢; exact ⟨hx.1.1, hx.2.1⟩)
  have hsum := card_union_add_card_inter (A ∩ C) (B ∩ C)
  have ha := hF A hA
  have hb := hF B hB
  omega

def eightWitness : Finset (Finset (Fin 8)) :=
  (univ.powersetCard 4).filter (fun A => 3 ≤ (A ∩ {0, 1, 2, 3}).card)

theorem eightWitness_uniform : Uniform 4 eightWitness := by
  intro A hA
  exact (mem_powersetCard.mp (mem_filter.mp hA).1).2

theorem eightWitness_noSingleton : NoSingleton eightWitness := by
  apply TwoIntersecting.noSingleton
  apply twoIntersecting_of_three_core (C := {0, 1, 2, 3}) (by decide)
  intro A hA
  exact (mem_filter.mp hA).2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem eightWitness_card : eightWitness.card = 17 := by decide

def sevenWitness : Finset (Finset (Fin 7)) :=
  ({0, 1, 2, 3, 4, 5} : Finset (Fin 7)).powersetCard 4

theorem sevenWitness_uniform : Uniform 4 sevenWitness := uniform_powersetCard _ _

theorem sevenWitness_noSingleton : NoSingleton sevenWitness := by
  exact (twoIntersecting_of_small (supported_powersetCard _ _)
    (uniform_powersetCard _ _) (by decide)).noSingleton

theorem sevenWitness_card : sevenWitness.card = 15 := by
  rw [sevenWitness, card_powersetCard]
  decide

theorem sharpBound_attained (n : ℕ) :
    ∃ F : Finset (Finset (Fin n)), Uniform 4 F ∧ NoSingleton F ∧
      F.card = sharpBound n := by
  by_cases h6 : n ≤ 6
  · obtain ⟨F, _, hU, hI, hC⟩ := small_attainment (univ : Finset (Fin n)) (by simpa)
    exact ⟨F, hU, hI, by simpa [sharpBound, h6] using hC⟩
  by_cases h7 : n = 7
  · subst n
    exact ⟨sevenWitness, sevenWitness_uniform, sevenWitness_noSingleton,
      by simpa [sharpBound] using sevenWitness_card⟩
  by_cases h8 : n = 8
  · subst n
    exact ⟨eightWitness, eightWitness_uniform, eightWitness_noSingleton,
      by simpa [sharpBound] using eightWitness_card⟩
  obtain ⟨F, _, hU, hI, hC⟩ := pairStar_attainment (univ : Finset (Fin n)) (by simp; omega)
  exact ⟨F, hU, hI, by simpa [sharpBound, h6, h7, h8] using hC⟩

end JSP572Four
