import JSP572Four.MatchingCore
import JSP572Four.TwoBlocks

/-! The perfect-matching bound, obtained by counting unordered pairs of blocks. -/

namespace JSP572Four

open Finset

variable {α : Type*} [DecidableEq α]

theorem exists_two_block_support_of_not_mem
    {F M : Finset (Finset α)} (hMF : M ⊆ F) (hM : Matching M)
    (hU : Uniform 4 F) (hN : NoSingleton F) (hS : Supported (covered M) F)
    {S : Finset α} (hSF : S ∈ F) (hSM : S ∉ M) :
    ∃ A ∈ M, ∃ B ∈ M, A ≠ B ∧ S ⊆ A ∪ B ∧
      (S ∩ A).card = 2 ∧ (S ∩ B).card = 2 := by
  have hSc : S.card = 4 := hU S hSF
  have hSnonempty : S.Nonempty := card_pos.mp (by omega)
  obtain ⟨x, hxS⟩ := hSnonempty
  obtain ⟨A, hAM, hxA⟩ := mem_biUnion.mp (hS S hSF hxS)
  have hnsub : ¬ S ⊆ A := by
    intro hSA
    have hEq : S = A := eq_of_subset_of_card_le hSA (by rw [hSc, hU A (hMF hAM)])
    apply hSM
    rw [hEq]
    exact hAM
  obtain ⟨y, hyS, hyA⟩ := Finset.not_subset.mp hnsub
  obtain ⟨B, hBM, hyB⟩ := mem_biUnion.mp (hS S hSF hyS)
  have hAB : A ≠ B := by
    intro hEq
    apply hyA
    rw [hEq]
    exact hyB
  have hdis : Disjoint A B := hM hAM hBM hAB
  have haPos : 0 < (S ∩ A).card := card_pos.mpr ⟨x, mem_inter.mpr ⟨hxS, hxA⟩⟩
  have hbPos : 0 < (S ∩ B).card := card_pos.mpr ⟨y, mem_inter.mpr ⟨hyS, hyB⟩⟩
  have haOne := hN S hSF A (hMF hAM)
  have hbOne := hN S hSF B (hMF hBM)
  have hdisInter : Disjoint (S ∩ A) (S ∩ B) :=
    hdis.mono inter_subset_right inter_subset_right
  have hUnionSub : (S ∩ A) ∪ (S ∩ B) ⊆ S := union_subset inter_subset_left inter_subset_left
  have hsum := card_le_card hUnionSub
  rw [card_union_of_disjoint hdisInter, hSc] at hsum
  have haTwo : (S ∩ A).card = 2 := by omega
  have hbTwo : (S ∩ B).card = 2 := by omega
  have hEq : (S ∩ A) ∪ (S ∩ B) = S := by
    apply eq_of_subset_of_card_le hUnionSub
    rw [hSc, card_union_of_disjoint hdisInter, haTwo, hbTwo]
  refine ⟨A, hAM, B, hBM, hAB, ?_, haTwo, hbTwo⟩
  rw [← hEq]
  exact union_subset (inter_subset_right.trans subset_union_left)
    (inter_subset_right.trans subset_union_right)

def twoBlockCrossFamily (F P : Finset (Finset α)) : Finset (Finset α) :=
  F.filter (fun S => S ⊆ covered P ∧ ∀ A ∈ P, (S ∩ A).card = 2)

theorem twoBlockCrossFamily_card_le_twelve
    {F M P : Finset (Finset α)} (hMF : M ⊆ F) (hM : Matching M)
    (hU : Uniform 4 F) (hN : NoSingleton F) (hP : P ∈ M.powersetCard 2) :
    (twoBlockCrossFamily F P).card ≤ 12 := by
  classical
  rcases mem_powersetCard.mp hP with ⟨hPM, hPc⟩
  obtain ⟨A, B, hAB, rfl⟩ := Finset.card_eq_two.mp hPc
  have hAM : A ∈ M := hPM (by simp)
  have hBM : B ∈ M := hPM (by simp)
  apply cross_family_card_le_twelve A B (twoBlockCrossFamily F {A, B})
    (hU A (hMF hAM)) (hU B (hMF hBM)) (hM hAM hBM hAB)
  · intro S hS
    have hh := (mem_filter.mp hS).2.1
    simpa [covered] using hh
  · intro S hS T hT
    exact hN S (mem_filter.mp hS).1 T (mem_filter.mp hT).1
  · intro S hS
    have hh := (mem_filter.mp hS).2.2
    exact ⟨hh A (by simp), hh B (by simp)⟩

/-- A perfect matching gives at most one internal member per block and at
most twelve cross members per unordered pair of blocks. -/
theorem perfectMatching_card_bound
    {F M : Finset (Finset α)} (hMF : M ⊆ F) (hM : Matching M)
    (hU : Uniform 4 F) (hN : NoSingleton F) (hS : Supported (covered M) F) :
    F.card ≤ M.card + 12 * M.card.choose 2 := by
  classical
  have hcover : F ⊆ M ∪ (M.powersetCard 2).biUnion (twoBlockCrossFamily F) := by
    intro S hSF
    by_cases hSM : S ∈ M
    · exact mem_union_left _ hSM
    obtain ⟨A, hAM, B, hBM, hAB, hSAB, haTwo, hbTwo⟩ :=
      exists_two_block_support_of_not_mem hMF hM hU hN hS hSF hSM
    apply mem_union_right
    apply mem_biUnion.mpr
    refine ⟨{A, B}, ?_, ?_⟩
    · apply mem_powersetCard.mpr
      exact ⟨by simpa using insert_subset hAM (singleton_subset_iff.mpr hBM), by simp [hAB]⟩
    · apply mem_filter.mpr
      refine ⟨hSF, ?_, ?_⟩
      · simpa [covered] using hSAB
      · intro C hC
        simp only [mem_insert, mem_singleton] at hC
        rcases hC with rfl | rfl
        · exact haTwo
        · exact hbTwo
  calc
    F.card ≤ (M ∪ (M.powersetCard 2).biUnion (twoBlockCrossFamily F)).card := card_le_card hcover
    _ ≤ M.card + ((M.powersetCard 2).biUnion (twoBlockCrossFamily F)).card := card_union_le _ _
    _ ≤ M.card + ∑ P ∈ M.powersetCard 2, (twoBlockCrossFamily F P).card :=
      Nat.add_le_add_left card_biUnion_le _
    _ ≤ M.card + ∑ _P ∈ M.powersetCard 2, 12 :=
      Nat.add_le_add_left (sum_le_sum (fun P hP =>
        twoBlockCrossFamily_card_le_twelve hMF hM hU hN hP)) _
    _ = M.card + 12 * M.card.choose 2 := by simp [Nat.mul_comm]

/-- A subtraction-free polynomial form of the perfect-matching bound. -/
theorem perfectMatching_card_bound_polynomial
    {F M : Finset (Finset α)} (hMF : M ⊆ F) (hM : Matching M)
    (hU : Uniform 4 F) (hN : NoSingleton F) (hS : Supported (covered M) F) :
    2 * F.card + 10 * M.card ≤ 12 * M.card ^ 2 := by
  have hb := perfectMatching_card_bound hMF hM hU hN hS
  have hc : 2 * M.card.choose 2 ≤ M.card * (M.card - 1) := by
    rw [Nat.choose_two_right]
    simpa [Nat.mul_comm] using Nat.div_mul_le_self (M.card * (M.card - 1)) 2
  by_cases hzero : M.card = 0
  · simp only [hzero, Nat.choose_zero_succ, mul_zero, add_zero] at hb
    simp [hzero, Nat.eq_zero_of_le_zero hb]
  · have hsub : M.card - 1 + 1 = M.card := by omega
    nlinarith

end JSP572Four
