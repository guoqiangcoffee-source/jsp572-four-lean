import JSP572Four.ResidualPartition
import JSP572Four.TwoIntersectingBound
import JSP572Four.MatchingArithmetic
import JSP572Four.MatchingStructure

namespace JSP572Four
open Finset

variable {α : Type*} [DecidableEq α]

theorem sharpBound_cluster_sub_one (c : ℕ) (hc : c = 0 ∨ 3 ≤ c) :
    sharpBound (4 + c) - 1 = clusterExtraBound c := by
  by_cases h0 : c = 0
  · subst c; norm_num [sharpBound,clusterExtraBound]
  by_cases h3 : c = 3
  · subst c; norm_num [sharpBound,clusterExtraBound]
  by_cases h4 : c = 4
  · subst c; norm_num [sharpBound,clusterExtraBound]
  have hc5 : 5 ≤ c := by omega
  have h6 : ¬4 + c ≤ 6 := by omega
  have h7 : 4 + c ≠ 7 := by omega
  have h8 : 4 + c ≠ 8 := by omega
  have he : 4 + c - 2 = c + 2 := by omega
  simp [sharpBound,clusterExtraBound,h0,h3,h4,h6,h7,h8,he]

noncomputable def colourCluster (F M : Finset (Finset α)) (B Q : Finset α) :
    Finset (Finset α) := by
  classical
  exact F.filter fun S => S ⊆ Q ∪ colourSupport F M B Q

theorem colourSupport_disjoint_anchor {F M : Finset (Finset α)} {B Q : Finset α}
    (hB : Disjoint B (covered M)) (hQ : Q ∈ M) :
    Disjoint Q (colourSupport F M B Q) :=
  (hB.mono (colourSupport_subset F M B Q) (subset_covered hQ)).symm

theorem card_colourCluster_erase_le {F M : Finset (Finset α)} {B Q : Finset α}
    (hu : Uniform 4 F) (hf : NoSingleton F) (hMF : M ⊆ F) (hm : Matching M)
    (hB : Disjoint B (covered M)) (hQ : Q ∈ M)
    (ht : TwoIntersecting (colourCluster F M B Q)) :
    ((colourCluster F M B Q).erase Q).card ≤
      clusterExtraBound (colourSupport F M B Q).card := by
  classical
  have hQF := hMF hQ
  have hQmem : Q ∈ colourCluster F M B Q :=
    mem_filter.mpr ⟨hQF, subset_union_left⟩
  have huC : Uniform 4 (colourCluster F M B Q) := by
    intro A hA
    exact hu A (mem_filter.mp hA).1
  have hsC : Supported (Q ∪ colourSupport F M B Q) (colourCluster F M B Q) := by
    intro A hA
    exact (mem_filter.mp hA).2
  have hbound := twoIntersecting_bound hsC huC ht
  rw [card_union_of_disjoint (colourSupport_disjoint_anchor hB hQ), hu Q hQF] at hbound
  rw [card_erase_of_mem hQmem]
  calc
    (colourCluster F M B Q).card - 1 ≤
        sharpBound (4 + (colourSupport F M B Q).card) - 1 := Nat.sub_le_sub_right hbound 1
    _ = clusterExtraBound (colourSupport F M B Q).card :=
      sharpBound_cluster_sub_one _ (colourSupport_card_zero_or_three hf hm hB hQ)

theorem colourCluster_twoIntersecting {F M : Finset (Finset α)} {B Q : Finset α}
    (hu : Uniform 4 F) (hf : NoSingleton F) (hm : MaximumMatching F M)
    (hB : Disjoint B (covered M)) (hQ : Q ∈ M) :
    TwoIntersecting (colourCluster F M B Q) :=
  blockResidualFamily_twoIntersecting hm hu hf hQ
    (hB.mono_left (colourSupport_subset F M B Q))

theorem member_meeting_colourSupport_subset {X S Q : Finset α} {F M : Finset (Finset α)}
    (hX : Supported X F) (hu : Uniform 4 F) (hf : NoSingleton F)
    (hm : MaximumMatching F M) (hQ : Q ∈ M) (hS : S ∈ F)
    {x : α} (hxS : x ∈ S) (hxC : x ∈ colourSupport F M (X \ covered M) Q) :
    S ⊆ Q ∪ colourSupport F M (X \ covered M) Q := by
  classical
  let B := X \ covered M
  have hB : Disjoint B (covered M) := disjoint_sdiff_self_left
  have hxB : x ∈ B := colourSupport_subset F M B Q hxC
  obtain ⟨p,hp,hxp⟩ := mem_biUnion.mp hxC
  obtain ⟨hpcol,hpnot⟩ := mem_sdiff.mp (mem_filter.mp hp).1
  have hcp : ColouredBy F Q p := (mem_filter.mp hp).2
  have hpB := (mem_colouredPairs.mp hpcol).1
  obtain ⟨R,hR,hRc,hsub,hother,hsum⟩ := residual_member_anchor hX hu hf hm hS
    ⟨x,mem_inter.mpr ⟨hxS,hxB⟩⟩
  have hparts : (S ∩ R) ∪ (S ∩ B) = S := by
    rw [← inter_union_distrib_left, inter_eq_left.mpr hsub]
  change (S ∩ R).card + (S ∩ B).card = 4 at hsum
  have hcases : ((S ∩ R).card = 2 ∧ (S ∩ B).card = 2) ∨
      ((S ∩ R).card = 3 ∧ (S ∩ B).card = 1) := by omega
  have hxSB : x ∈ S ∩ B := mem_inter.mpr ⟨hxS,hxB⟩
  have hresSub : S ∩ B ⊆ colourSupport F M B Q := by
    rcases hcases with htwo | hthree
    · have hcR : ColouredBy F R (S ∩ B) :=
        ⟨S ∩ R, mem_powersetCard.mpr ⟨inter_subset_right, htwo.1⟩, hparts.symm ▸ hS⟩
      have hpSB : S ∩ B ∈ B.powersetCard 2 :=
        mem_powersetCard.mpr ⟨inter_subset_right,htwo.2⟩
      have hQR : Q = R := by
        by_contra hne
        rcases different_colours_eq_or_disjoint hf hm.2.1 hB hQ hR hne hpB hpSB hcp hcR with he | hd
        · have hcR' : ColouredBy F R p := he.symm ▸ hcR
          exact hpnot (multiple_colours_isolated hf hm.2.1 hB hpcol hQ hR hne hcp hcR')
        · exact disjoint_left.mp hd hxp hxSB
      subst R
      have hcSB : S ∩ B ∈ colouredPairs F M B :=
        mem_colouredPairs.mpr ⟨hpSB,Q,hQ,hcR⟩
      have hnSB : S ∩ B ∉ isolatedPairs F M B := by
        intro hiso
        exact disjoint_left.mp (colourSupport_disjoint_isolated F M B Q) hxC
          (subset_covered hiso hxSB)
      intro y hy
      exact mem_biUnion.mpr ⟨S ∩ B, mem_filter.mpr ⟨mem_sdiff.mpr ⟨hcSB,hnSB⟩,hcR⟩,hy⟩
    · have hQR : Q = R := by
        by_contra hne
        have hdSQ := hother Q hQ hne
        obtain ⟨a,ha,haF⟩ := hcp
        have hsubI : S ∩ (a ∪ p) ⊆ S ∩ B := by
          intro y hy
          obtain ⟨hyS,hyap⟩ := mem_inter.mp hy
          rcases mem_union.mp hyap with hya | hyp
          · exact False.elim (disjoint_left.mp hdSQ hyS ((mem_powersetCard.mp ha).1 hya))
          · exact mem_inter.mpr ⟨hyS,(mem_powersetCard.mp hpB).1 hyp⟩
        have hle := card_le_card hsubI
        have hpos : 0 < (S ∩ (a ∪ p)).card :=
          card_pos.mpr ⟨x,mem_inter.mpr ⟨hxS,mem_union_right _ hxp⟩⟩
        exact hf S hS (a ∪ p) haF (by omega)
      have hone : S ∩ B = {x} := by
        obtain ⟨y,hy⟩ := card_eq_one.mp hthree.2
        have hxy : x = y := by simpa [hy] using hxSB
        simpa [hxy] using hy
      intro y hy
      have hyx : y = x := by simpa [hone] using hy
      simpa [hyx] using hxC
  have hQR : Q = R := by
    by_contra hne
    have hdis := colourSupports_pairwiseDisjoint hf hm.2.1 hB hQ hR hne
    rcases hcases with htwo | hthree
    · have hcR : ColouredBy F R (S ∩ B) :=
        ⟨S ∩ R, mem_powersetCard.mpr ⟨inter_subset_right, htwo.1⟩, hparts.symm ▸ hS⟩
      rcases different_colours_eq_or_disjoint hf hm.2.1 hB hQ hR hne hpB
        (mem_powersetCard.mpr ⟨inter_subset_right,htwo.2⟩) hcp hcR with he | hd
      · exact hpnot (multiple_colours_isolated hf hm.2.1 hB hpcol hQ hR hne hcp (he.symm ▸ hcR))
      · exact disjoint_left.mp hd hxp hxSB
    · have hdSQ := hother Q hQ hne
      obtain ⟨a,ha,haF⟩ := hcp
      have hsubI : S ∩ (a ∪ p) ⊆ S ∩ B := by
        intro y hy
        obtain ⟨hyS,hyap⟩ := mem_inter.mp hy
        rcases mem_union.mp hyap with hya | hyp
        · exact False.elim (disjoint_left.mp hdSQ hyS ((mem_powersetCard.mp ha).1 hya))
        · exact mem_inter.mpr ⟨hyS,(mem_powersetCard.mp hpB).1 hyp⟩
      have hle := card_le_card hsubI
      have hpos : 0 < (S ∩ (a ∪ p)).card :=
        card_pos.mpr ⟨x,mem_inter.mpr ⟨hxS,mem_union_right _ hxp⟩⟩
      exact hf S hS (a ∪ p) haF (by omega)
  subst R
  intro y hy
  rcases mem_union.mp (hsub hy) with hyQ | hyB
  · exact mem_union_left _ hyQ
  · exact mem_union_right _ (hresSub (mem_inter.mpr ⟨hy,hyB⟩))

theorem residualC_count_le {X : Finset α} {F M : Finset (Finset α)}
    (hX : Supported X F) (hu : Uniform 4 F) (hf : NoSingleton F)
    (hm : MaximumMatching F M) :
    (F.filter (fun S => ¬ Disjoint S (residualC F M (X \ covered M)))).card ≤
      ∑ Q ∈ M, clusterExtraBound (colourSupport F M (X \ covered M) Q).card := by
  classical
  let B := X \ covered M
  have hB : Disjoint B (covered M) := disjoint_sdiff_self_left
  have hsub : (F.filter (fun S => ¬ Disjoint S (residualC F M B))) ⊆
      M.biUnion (fun Q => (colourCluster F M B Q).erase Q) := by
    intro S hS
    obtain ⟨hSF,hmeet⟩ := mem_filter.mp hS
    obtain ⟨x,hxS,hxC⟩ := not_disjoint_iff.mp hmeet
    obtain ⟨Q,hQ,hxQ⟩ := mem_biUnion.mp hxC
    have hSQ := member_meeting_colourSupport_subset hX hu hf hm hQ hSF hxS hxQ
    have hne : S ≠ Q := by
      intro he
      exact disjoint_left.mp (colourSupport_disjoint_anchor hB hQ) (he ▸ hxS) hxQ
    exact mem_biUnion.mpr ⟨Q,hQ,mem_erase.mpr ⟨hne,mem_filter.mpr ⟨hSF,hSQ⟩⟩⟩
  calc
    (F.filter (fun S => ¬ Disjoint S (residualC F M B))).card ≤
        (M.biUnion (fun Q => (colourCluster F M B Q).erase Q)).card := card_le_card hsub
    _ ≤ ∑ Q ∈ M, ((colourCluster F M B Q).erase Q).card := card_biUnion_le
    _ ≤ ∑ Q ∈ M, clusterExtraBound (colourSupport F M B Q).card := by
      apply sum_le_sum
      intro Q hQ
      exact card_colourCluster_erase_le hu hf hm.1 hm.2.1 hB hQ
        (colourCluster_twoIntersecting hu hf hm hB hQ)

end JSP572Four
