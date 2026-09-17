import JSP572Four.Constructions

namespace JSP572Four
open Finset
variable {α : Type*} [DecidableEq α]

theorem card_meeting_le_sum (F : Finset (Finset α)) (E : Finset α) :
    (F.filter (fun S => ¬ Disjoint S E)).card ≤
      ∑ x ∈ E, (F.filter (fun S => x ∈ S)).card := by
  classical
  have hsub : F.filter (fun S => ¬ Disjoint S E) ⊆
      E.biUnion (fun x => F.filter (fun S => x ∈ S)) := by
    intro S hS
    obtain ⟨hSF, hSE⟩ := mem_filter.mp hS
    obtain ⟨x, hxS, hxE⟩ := not_disjoint_iff.mp hSE
    exact mem_biUnion.mpr ⟨x, hxE, mem_filter.mpr ⟨hSF, hxS⟩⟩
  exact (card_le_card hsub).trans card_biUnion_le

theorem card_meeting_le_mul {F : Finset (Finset α)} {E : Finset α} {k : ℕ}
    (hk : ∀ x ∈ E, (F.filter (fun S => x ∈ S)).card ≤ k) :
    (F.filter (fun S => ¬ Disjoint S E)).card ≤ k * E.card := by
  calc
    _ ≤ ∑ x ∈ E, (F.filter (fun S => x ∈ S)).card := card_meeting_le_sum F E
    _ ≤ ∑ _x ∈ E, k := sum_le_sum hk
    _ = k * E.card := by simp [Nat.mul_comm]

theorem card_le_choose_fixed_core {X P : Finset α} {F : Finset (Finset α)} {k : ℕ}
    (hX : Supported X F) (hU : Uniform k F) (hP : ∀ S ∈ F, P ⊆ S)
    (hPX : P ⊆ X) (hPk : P.card ≤ k) :
    F.card ≤ (X.card - P.card).choose (k - P.card) := by
  calc
    F.card ≤ ((X.powersetCard k).filter (P ⊆ ·)).card := card_le_card (by
      intro S hS
      exact mem_filter.mpr ⟨mem_powersetCard.mpr ⟨hX S hS, hU S hS⟩, hP S hS⟩)
    _ = _ := card_filter_powersetCard_subset P X k hPX hPk

theorem card_four_containing_point_le_four {Q : Finset α} {x : α}
    {F : Finset (Finset α)} (hQ : Q.card = 4) (hx : x ∉ Q)
    (hX : Supported (insert x Q) F) (hU : Uniform 4 F) (hF : ∀ S ∈ F, x ∈ S) :
    F.card ≤ 4 := by
  have hP : ∀ S ∈ F, ({x} : Finset α) ⊆ S := by simpa using hF
  have hc := card_le_choose_fixed_core hX hU hP
    (singleton_subset_iff.mpr (mem_insert_self x Q)) (by simp)
  simpa [card_insert_of_notMem hx, hQ] using hc

theorem inter_eq_singleton_of_card_one {S B : Finset α} {x : α}
    (hc : (S ∩ B).card = 1) (hxS : x ∈ S) (hxB : x ∈ B) : S ∩ B = {x} := by
  exact eq_of_subset_of_card_le (singleton_subset_iff.mpr (mem_inter.mpr ⟨hxS, hxB⟩))
    (by simp [hc]) |>.symm

end JSP572Four
