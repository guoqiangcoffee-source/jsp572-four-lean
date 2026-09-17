import JSP572Four.MatchingCore

namespace JSP572Four

open Finset

variable {α : Type*} [DecidableEq α]

def blockResidualFamily (F : Finset (Finset α)) (Q B : Finset α) : Finset (Finset α) :=
  F.filter fun S => S ⊆ Q ∪ B

lemma MaximumMatching.not_two_replacements {F M : Finset (Finset α)}
    (hM : MaximumMatching F M) (hu : Uniform 4 F)
    {Q A C : Finset α} (hQ : Q ∈ M) (hA : A ∈ F) (hC : C ∈ F)
    (hAC : Disjoint A C)
    (hAR : ∀ R ∈ M, R ≠ Q → Disjoint A R)
    (hCR : ∀ R ∈ M, R ≠ Q → Disjoint C R) : False := by
  have hAne : A ≠ ∅ := by intro he; have := hu A hA; simp [he] at this
  have hCne : C ≠ ∅ := by intro he; have := hu C hC; simp [he] at this
  have hne : A ≠ C := by intro he; exact hAne (disjoint_self.mp (he ▸ hAC))
  have hAn : A ∉ M.erase Q := by
    intro h
    exact hAne (disjoint_self.mp (hAR A (mem_erase.mp h).2 (mem_erase.mp h).1))
  have hCn : C ∉ M.erase Q := by
    intro h
    exact hCne (disjoint_self.mp (hCR C (mem_erase.mp h).2 (mem_erase.mp h).1))
  have hmat : Matching (M.erase Q) := by
    intro R hR T hT hRT
    exact hM.2.1 (mem_of_mem_erase hR) (mem_of_mem_erase hT) hRT
  have hmatC : Matching (insert C (M.erase Q)) := by
    change (↑(insert C (M.erase Q)) : Set (Finset α)).PairwiseDisjoint id
    rw [coe_insert]
    apply hmat.insert
    intro R hR _
    exact hCR R (mem_erase.mp hR).2 (mem_erase.mp hR).1
  have hmatAC : Matching (insert A (insert C (M.erase Q))) := by
    change (↑(insert A (insert C (M.erase Q))) : Set (Finset α)).PairwiseDisjoint id
    rw [coe_insert]
    apply hmatC.insert
    intro R hR _
    rcases mem_insert.mp hR with rfl | hR
    · exact hAC
    · exact hAR R (mem_erase.mp hR).2 (mem_erase.mp hR).1
  have hsub : insert A (insert C (M.erase Q)) ⊆ F :=
    insert_subset hA (insert_subset hC ((erase_subset _ _).trans hM.1))
  have hcard := hM.2.2 _ hsub hmatAC
  rw [card_insert_of_notMem (by simp [hne, hAn]), card_insert_of_notMem hCn] at hcard
  have he := card_erase_add_one hQ
  omega

lemma disjoint_other_block {M : Finset (Finset α)} (hM : Matching M)
    {Q R B S : Finset α} (hQ : Q ∈ M) (hR : R ∈ M) (hRQ : R ≠ Q)
    (hB : Disjoint B (covered M)) (hS : S ⊆ Q ∪ B) : Disjoint S R := by
  apply Disjoint.mono_left hS
  apply disjoint_union_left.mpr
  exact ⟨hM hQ hR hRQ.symm, hB.mono_right (subset_covered hR)⟩

lemma blockResidualFamily_twoIntersecting {F M : Finset (Finset α)}
    {Q B : Finset α} (hM : MaximumMatching F M) (hu : Uniform 4 F)
    (hn : NoSingleton F) (hQ : Q ∈ M) (hB : Disjoint B (covered M)) :
    TwoIntersecting (blockResidualFamily F Q B) := by
  apply twoIntersecting_of_no_disjoint
  · intro A hA C hC
    exact hn A (mem_filter.mp hA).1 C (mem_filter.mp hC).1
  · intro A hA C hC hAC
    apply hM.not_two_replacements hu hQ (mem_filter.mp hA).1 (mem_filter.mp hC).1 hAC
    · intro R hR hRQ
      exact disjoint_other_block hM.2.1 hQ hR hRQ hB (mem_filter.mp hA).2
    · intro R hR hRQ
      exact disjoint_other_block hM.2.1 hQ hR hRQ hB (mem_filter.mp hC).2

lemma blockResidualFamily_uniform {F : Finset (Finset α)} {Q B : Finset α} {k : ℕ}
    (hu : Uniform k F) : Uniform k (blockResidualFamily F Q B) :=
  fun A hA => hu A (mem_filter.mp hA).1

lemma blockResidualFamily_supported (F : Finset (Finset α)) (Q B : Finset α) :
    Supported (Q ∪ B) (blockResidualFamily F Q B) :=
  fun _ h => (mem_filter.mp h).2

lemma block_inter_subset_residual_sdiff {M : Finset (Finset α)} {B S Q : Finset α}
    (hB : Disjoint B (covered M)) (hQ : Q ∈ M) : S ∩ Q ⊆ S \ B := by
  intro x hx
  rcases mem_inter.mp hx with ⟨hxS, hxQ⟩
  refine mem_sdiff.mpr ⟨hxS, ?_⟩
  intro hxB
  exact disjoint_left.mp hB hxB (subset_covered hQ hxQ)

lemma member_decomposition {S Q B : Finset α} (hsub : S ⊆ Q ∪ B) :
    S = (S ∩ Q) ∪ (S ∩ B) := by
  ext x
  simp only [mem_union, mem_inter]
  constructor
  · intro hx
    exact (mem_union.mp (hsub hx)).elim (fun hq => Or.inl ⟨hx, hq⟩)
      (fun hb => Or.inr ⟨hx, hb⟩)
  · exact fun h => h.elim And.left And.left

/-- A member touching the uncovered ground has exactly one matching-block anchor. -/
theorem residual_member_anchor {X S : Finset α} {F M : Finset (Finset α)}
    (hX : Supported X F) (hu : Uniform 4 F) (hn : NoSingleton F)
    (hM : MaximumMatching F M) (hS : S ∈ F)
    (hres : (S ∩ (X \ covered M)).Nonempty) :
    ∃ Q ∈ M, ((S ∩ Q).card = 2 ∨ (S ∩ Q).card = 3) ∧
      S ⊆ Q ∪ (X \ covered M) ∧
      (∀ R ∈ M, R ≠ Q → Disjoint S R) ∧
      (S ∩ Q).card + (S ∩ (X \ covered M)).card = 4 := by
  let B := X \ covered M
  have hB : Disjoint B (covered M) := by
    apply disjoint_left.mpr
    intro y hy hM
    exact (mem_sdiff.mp hy).2 hM
  have hSc : S.card = 4 := hu S hS
  have hpos : 0 < (S ∩ B).card := card_pos.mpr hres
  have hc3 : (S \ B).card ≤ 3 := by
    have h := card_sdiff_add_card_inter S B
    omega
  obtain ⟨x, hxS, hxM⟩ := not_disjoint_iff.mp (hM.every_member_meets hu hS)
  obtain ⟨Q, hQ, hxQ⟩ := mem_biUnion.mp hxM
  have hQpos : 0 < (S ∩ Q).card := card_pos.mpr ⟨x, mem_inter.mpr ⟨hxS, hxQ⟩⟩
  have hQne := hn S hS Q (hM.1 hQ)
  have hQle : (S ∩ Q).card ≤ 3 :=
    (card_le_card (block_inter_subset_residual_sdiff hB hQ)).trans hc3
  have hQcard : (S ∩ Q).card = 2 ∨ (S ∩ Q).card = 3 := by omega
  have hother : ∀ R ∈ M, R ≠ Q → Disjoint S R := by
    intro R hR hRQ
    by_contra hnd
    obtain ⟨y, hyS, hyR⟩ := not_disjoint_iff.mp hnd
    have hRpos : 0 < (S ∩ R).card := card_pos.mpr ⟨y, mem_inter.mpr ⟨hyS, hyR⟩⟩
    have hRne := hn S hS R (hM.1 hR)
    have hsub : (S ∩ Q) ∪ (S ∩ R) ⊆ S \ B :=
      union_subset (block_inter_subset_residual_sdiff hB hQ)
        (block_inter_subset_residual_sdiff hB hR)
    have hdis : Disjoint (S ∩ Q) (S ∩ R) :=
      (hM.2.1 hQ hR hRQ.symm).mono inter_subset_right inter_subset_right
    have hcard := (card_le_card hsub).trans hc3
    rw [card_union_of_disjoint hdis] at hcard
    omega
  have hSQB : S ⊆ Q ∪ B := by
    intro y hy
    by_cases hyB : y ∈ B
    · exact mem_union_right _ hyB
    have hyM : y ∈ covered M := by
      by_contra h
      exact hyB (mem_sdiff.mpr ⟨hX S hS hy, h⟩)
    obtain ⟨R, hR, hyR⟩ := mem_biUnion.mp hyM
    by_cases he : R = Q
    · subst R
      exact mem_union_left _ hyR
    · exact False.elim (disjoint_left.mp (hother R hR he) hy hyR)
  have hparts : (S ∩ Q) ∪ (S ∩ B) = S := by
    ext y
    simp only [mem_union, mem_inter]
    exact ⟨fun h => h.elim And.left And.left,
      fun h => (mem_union.mp (hSQB h)).elim (fun hq => Or.inl ⟨h, hq⟩)
        (fun hb => Or.inr ⟨h, hb⟩)⟩
  have hdis : Disjoint (S ∩ Q) (S ∩ B) :=
    (hB.mono_right (subset_covered hQ)).symm.mono inter_subset_right inter_subset_right
  have hsum : (S ∩ Q).card + (S ∩ B).card = 4 := by
    rw [← card_union_of_disjoint hdis, hparts, hSc]
  exact ⟨Q, hQ, hQcard, hSQB, hother, hsum⟩

theorem residual_member_anchor_unique {X S : Finset α} {F M : Finset (Finset α)}
    (hX : Supported X F) (hu : Uniform 4 F) (hn : NoSingleton F)
    (hM : MaximumMatching F M) (hS : S ∈ F)
    (hres : (S ∩ (X \ covered M)).Nonempty) :
    ∃! Q, Q ∈ M ∧ ¬ Disjoint S Q := by
  obtain ⟨Q, hQ, hqc, hsub, hother, hsum⟩ := residual_member_anchor hX hu hn hM hS hres
  have hnd : ¬ Disjoint S Q := by
    intro hd
    have he : S ∩ Q = ∅ := disjoint_iff_inter_eq_empty.mp hd
    simp [he] at hqc
  refine ⟨Q, ⟨hQ, hnd⟩, ?_⟩
  intro R hR
  by_contra hne
  exact hR.2 (hother R hR.1 hne)

theorem residual_member_anchor_counts {X S : Finset α} {F M : Finset (Finset α)}
    (hX : Supported X F) (hu : Uniform 4 F) (hn : NoSingleton F)
    (hM : MaximumMatching F M) (hS : S ∈ F)
    (hres : (S ∩ (X \ covered M)).Nonempty) :
    ∃ Q ∈ M, S ⊆ Q ∪ (X \ covered M) ∧
      (((S ∩ Q).card = 2 ∧ (S ∩ (X \ covered M)).card = 2) ∨
       ((S ∩ Q).card = 3 ∧ (S ∩ (X \ covered M)).card = 1)) := by
  obtain ⟨Q, hQ, hqc, hsub, hother, hsum⟩ := residual_member_anchor hX hu hn hM hS hres
  exact ⟨Q, hQ, hsub, by omega⟩

end JSP572Four
