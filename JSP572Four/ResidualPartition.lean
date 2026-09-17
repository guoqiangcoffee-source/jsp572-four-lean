import JSP572Four.ResidualColours

namespace JSP572Four
open Finset
variable {α : Type*} [DecidableEq α]

noncomputable def residualC (F M : Finset (Finset α)) (B : Finset α) : Finset α :=
  M.biUnion (colourSupport F M B)

noncomputable def residualD (F M : Finset (Finset α)) (B : Finset α) : Finset α :=
  covered (isolatedPairs F M B)

noncomputable def residualE (F M : Finset (Finset α)) (B : Finset α) : Finset α :=
  B \ (residualC F M B ∪ residualD F M B)

theorem residualC_subset (F M : Finset (Finset α)) (B : Finset α) : residualC F M B ⊆ B := by
  intro x hx
  obtain ⟨Q, _, hxQ⟩ := mem_biUnion.mp hx
  exact colourSupport_subset F M B Q hxQ

theorem residualD_subset (F M : Finset (Finset α)) (B : Finset α) : residualD F M B ⊆ B := by
  classical
  intro x hx
  obtain ⟨p, hp, hxp⟩ := mem_biUnion.mp hx
  exact (mem_powersetCard.mp (mem_colouredPairs.mp (mem_filter.mp hp).1).1).1 hxp

theorem residualC_disjoint_D (F M : Finset (Finset α)) (B : Finset α) :
    Disjoint (residualC F M B) (residualD F M B) := by
  apply disjoint_left.mpr
  intro x hxC hxD
  obtain ⟨Q, _, hxQ⟩ := mem_biUnion.mp hxC
  exact disjoint_left.mp (colourSupport_disjoint_isolated F M B Q) hxQ hxD

theorem residual_partition_card (F M : Finset (Finset α)) (B : Finset α) :
    B.card = (residualC F M B).card + (residualD F M B).card + (residualE F M B).card := by
  have hsub := union_subset (residualC_subset F M B) (residualD_subset F M B)
  have hle := card_le_card hsub
  unfold residualE
  rw [card_sdiff_of_subset hsub, card_union_of_disjoint (residualC_disjoint_D F M B)] at *
  omega

theorem card_residualC {F M : Finset (Finset α)} {B : Finset α}
    (hF : NoSingleton F) (hM : Matching M) (hB : Disjoint B (covered M)) :
    (residualC F M B).card = ∑ Q ∈ M, (colourSupport F M B Q).card :=
  card_biUnion (colourSupports_pairwiseDisjoint hF hM hB)

theorem colouredPair_subset_CD {F M : Finset (Finset α)} {B p : Finset α}
    (hp : p ∈ colouredPairs F M B) : p ⊆ residualC F M B ∪ residualD F M B := by
  classical
  by_cases hi : p ∈ isolatedPairs F M B
  · exact (subset_covered hi).trans subset_union_right
  · obtain ⟨_, Q, hQ, hc⟩ := mem_colouredPairs.mp hp
    intro x hx
    apply mem_union_left
    exact mem_biUnion.mpr ⟨Q, hQ, mem_biUnion.mpr
      ⟨p, mem_filter.mpr ⟨mem_sdiff.mpr ⟨hp, hi⟩, hc⟩, hx⟩⟩

theorem residualE_disjoint_colouredPair {F M : Finset (Finset α)} {B p : Finset α}
    (hp : p ∈ colouredPairs F M B) : Disjoint (residualE F M B) p := by
  exact disjoint_sdiff_self_left.mono_right (colouredPair_subset_CD hp)

theorem ground_partition_card {X : Finset α} {F M : Finset (Finset α)}
    (hX : Supported X F) (hU : Uniform 4 F) (hM : MaximumMatching F M) :
    X.card = 4 * M.card + (residualC F M (X \ covered M)).card +
      (residualD F M (X \ covered M)).card + (residualE F M (X \ covered M)).card := by
  have hUm : Uniform 4 M := fun A hA => hU A (hM.1 hA)
  have hsub := covered_subset (fun A hA => hX A (hM.1 hA))
  have hsum := residual_partition_card F M (X \ covered M)
  rw [card_sdiff_of_subset hsub, card_covered hM.2.1 hUm] at hsum
  have hle := four_mul_matching_card_le hX hU hM
  omega

end JSP572Four
