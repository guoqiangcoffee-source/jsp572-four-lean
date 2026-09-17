import JSP572Four.ResidualPartition
import JSP572Four.MatchingStructure
import JSP572Four.Counting

namespace JSP572Four
open Finset
variable {α : Type*} [DecidableEq α]

theorem residualE_member_support {X S : Finset α} {F M : Finset (Finset α)} {x : α}
    (hX : Supported X F) (hu : Uniform 4 F) (hn : NoSingleton F)
    (hM : MaximumMatching F M) (hS : S ∈ F) (hxS : x ∈ S)
    (hxE : x ∈ residualE F M (X \ covered M)) :
    ∃ Q ∈ M, S ⊆ insert x Q := by
  let B := X \ covered M
  have hxB : x ∈ B := (mem_sdiff.mp hxE).1
  obtain ⟨Q, hQ, hsub, hcounts⟩ := residual_member_anchor_counts hX hu hn hM hS
    ⟨x, mem_inter.mpr ⟨hxS, hxB⟩⟩
  have hparts : (S ∩ Q) ∪ (S ∩ B) = S := by
    ext y
    simp only [mem_union, mem_inter]
    exact ⟨fun h => h.elim And.left And.left,
      fun h => (mem_union.mp (hsub h)).elim (fun hq => Or.inl ⟨h, hq⟩)
        (fun hb => Or.inr ⟨h, hb⟩)⟩
  have hres1 : (S ∩ B).card = 1 := by
    rcases hcounts with hc | hc
    · have hcol : S ∩ B ∈ colouredPairs F M B := by
        apply mem_colouredPairs.mpr
        refine ⟨mem_powersetCard.mpr ⟨inter_subset_right, hc.2⟩, Q, hQ, ?_⟩
        refine ⟨S ∩ Q, mem_powersetCard.mpr ⟨inter_subset_right, hc.1⟩, ?_⟩
        rwa [hparts]
      exact False.elim (disjoint_left.mp (residualE_disjoint_colouredPair hcol)
        hxE (mem_inter.mpr ⟨hxS, hxB⟩))
    · exact hc.2
  have hi := inter_eq_singleton_of_card_one hres1 hxS hxB
  refine ⟨Q, hQ, ?_⟩
  intro y hy
  rcases mem_union.mp (hsub hy) with hyQ | hyB
  · exact mem_insert_of_mem hyQ
  · have hey : y = x := by
      have hm : y ∈ S ∩ B := mem_inter.mpr ⟨hy, hyB⟩
      rwa [hi, mem_singleton] at hm
    exact mem_insert.mpr (Or.inl hey)

theorem same_point_support_anchor {S T Q R : Finset α} {F M : Finset (Finset α)} {x : α}
    (hn : NoSingleton F) (hM : Matching M) (hS : S ∈ F) (hT : T ∈ F)
    (hQ : Q ∈ M) (hR : R ∈ M) (hxS : x ∈ S) (hxT : x ∈ T)
    (hSQ : S ⊆ insert x Q) (hTR : T ⊆ insert x R) : Q = R := by
  by_contra hne
  have hd := hM hQ hR hne
  have hsub : S ∩ T ⊆ ({x} : Finset α) := by
    intro y hy
    rcases mem_inter.mp hy with ⟨hyS, hyT⟩
    rcases mem_insert.mp (hSQ hyS) with he | hyQ
    · exact mem_singleton.mpr he
    rcases mem_insert.mp (hTR hyT) with he | hyR
    · exact mem_singleton.mpr he
    exact False.elim (disjoint_left.mp hd hyQ hyR)
  have hback : ({x} : Finset α) ⊆ S ∩ T :=
    singleton_subset_iff.mpr (mem_inter.mpr ⟨hxS, hxT⟩)
  exact hn S hS T hT (by rw [Subset.antisymm hsub hback]; simp)

theorem residualE_point_count {X : Finset α} {F M : Finset (Finset α)} {x : α}
    (hX : Supported X F) (hu : Uniform 4 F) (hn : NoSingleton F)
    (hM : MaximumMatching F M) (hxE : x ∈ residualE F M (X \ covered M)) :
    (F.filter (fun S => x ∈ S)).card ≤ 4 := by
  classical
  by_cases he : (F.filter (fun S => x ∈ S)).Nonempty
  · obtain ⟨S, hS⟩ := he
    obtain ⟨hSF, hxS⟩ := mem_filter.mp hS
    obtain ⟨Q, hQ, hSQ⟩ := residualE_member_support hX hu hn hM hSF hxS hxE
    have hQ4 := hu Q (hM.1 hQ)
    have hxQ : x ∉ Q := by
      intro hx
      exact (mem_sdiff.mp (mem_sdiff.mp hxE).1).2 (subset_covered hQ hx)
    apply card_four_containing_point_le_four hQ4 hxQ
    · intro T hT
      obtain ⟨hTF, hxT⟩ := mem_filter.mp hT
      obtain ⟨R, hR, hTR⟩ := residualE_member_support hX hu hn hM hTF hxT hxE
      have heq := same_point_support_anchor hn hM.2.1 hSF hTF hQ hR hxS hxT hSQ hTR
      simpa [heq] using hTR
    · intro T hT
      exact hu T (mem_filter.mp hT).1
    · intro T hT
      exact (mem_filter.mp hT).2
  · simp [not_nonempty_iff_eq_empty.mp he]

theorem residualE_count {X : Finset α} {F M : Finset (Finset α)}
    (hX : Supported X F) (hu : Uniform 4 F) (hn : NoSingleton F)
    (hM : MaximumMatching F M) :
    (F.filter (fun S => ¬ Disjoint S (residualE F M (X \ covered M)))).card ≤
      4 * (residualE F M (X \ covered M)).card :=
  card_meeting_le_mul (fun _ hx => residualE_point_count hX hu hn hM hx)

end JSP572Four
