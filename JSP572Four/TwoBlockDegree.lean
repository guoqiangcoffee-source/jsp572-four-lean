import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.Linarith

/-!
The arithmetic portion of the two-block lemma. For four-element blocks,
`s` is the family of their six pairs and `opposite` takes complements.
The remaining geometric work is to derive the two degree constraints
from the absence of singleton intersections.
-/

namespace JSP572Four

open Finset

theorem six_pair_degree_sum_le_twelve {α : Type*} [DecidableEq α]
    (s : Finset α) (opposite : α → α) (degree : α → ℕ)
    (hcard : s.card = 6)
    (hmem : ∀ a ∈ s, opposite a ∈ s)
    (hinv : ∀ a ∈ s, opposite (opposite a) = a)
    (hdegree : ∀ a ∈ s, degree a ≤ 6)
    (hlarge : ∀ a ∈ s, 3 ≤ degree a → degree (opposite a) = 0)
    (hadjacent : ∀ a ∈ s, ∀ b ∈ s, a ≠ b → b ≠ opposite a →
      degree a + degree b ≤ 6) :
    ∑ a ∈ s, degree a ≤ 12 := by
  classical
  by_cases hsmall : ∀ a ∈ s, degree a ≤ 4
  · have hpairs : ∀ a ∈ s, degree a + degree (opposite a) ≤ 4 := by
      intro a ha
      by_cases hda : degree a ≤ 2
      · by_cases hdo : degree (opposite a) ≤ 2
        · omega
        · have hz := hlarge (opposite a) (hmem a ha) (by omega)
          rw [hinv a ha] at hz
          have hh := hsmall (opposite a) (hmem a ha)
          omega
      · have hz := hlarge a ha (by omega)
        have hh := hsmall a ha
        omega
    have hperm : (∑ a ∈ s, degree (opposite a)) = ∑ a ∈ s, degree a := by
      refine Finset.sum_bij (fun a _ => opposite a) hmem ?_ ?_ ?_
      · intro a ha b hb hab
        have h := congrArg opposite hab
        simpa only [hinv a ha, hinv b hb] using h
      · intro a ha
        exact ⟨opposite a, hmem a ha, hinv a ha⟩
      · intro a ha
        rfl
    have hs := Finset.sum_le_sum hpairs
    simp only [Finset.sum_add_distrib, hperm, Finset.sum_const, hcard,
      nsmul_eq_mul] at hs
    omega
  · have hex : ∃ a ∈ s, 5 ≤ degree a := by
      by_contra hn
      apply hsmall
      intro a ha
      by_contra hna
      exact hn ⟨a, ha, by omega⟩
    obtain ⟨a, ha, hda⟩ := hex
    have hrest : ∀ b ∈ s.erase a, degree b ≤ 1 := by
      intro b hb
      have hba : b ≠ a := (Finset.mem_erase.mp hb).1
      have hbs : b ∈ s := (Finset.mem_erase.mp hb).2
      by_cases hbo : b = opposite a
      · have hz := hlarge a ha (by omega)
        rw [hbo, hz]
        omega
      · have hh := hadjacent a ha b hbs (Ne.symm hba) hbo
        omega
    have hsum := Finset.sum_le_sum hrest
    have hcarderase : (s.erase a).card = 5 := by
      rw [Finset.card_erase_of_mem ha, hcard]
    simp only [Finset.sum_const, hcarderase, nsmul_eq_mul, mul_one] at hsum
    have hsplit := Finset.sum_erase_add s degree ha
    have hda6 := hdegree a ha
    omega

end JSP572Four
