import JSP572Four.MatchingCore
import Mathlib.Tactic

namespace JSP572Four
open Finset
variable {α : Type*} [DecidableEq α]

/-- A residual pair receives a colour from a matching block when their pairs form a member. -/
def ColouredBy (F : Finset (Finset α)) (Q p : Finset α) : Prop :=
  ∃ a ∈ Q.powersetCard 2, a ∪ p ∈ F

noncomputable def colouredPairs (F M : Finset (Finset α)) (B : Finset α) :
    Finset (Finset α) := by
  classical
  exact (B.powersetCard 2).filter (fun p => ∃ Q ∈ M, ColouredBy F Q p)

noncomputable def isolatedPairs (F M : Finset (Finset α)) (B : Finset α) :
    Finset (Finset α) := by
  classical
  exact (colouredPairs F M B).filter
    (fun p => ∀ q ∈ colouredPairs F M B, p ≠ q → Disjoint p q)

noncomputable def colourSupport (F M : Finset (Finset α)) (B Q : Finset α) :
    Finset α := by
  classical
  exact (((colouredPairs F M B) \ (isolatedPairs F M B)).filter
    (ColouredBy F Q)).biUnion id

theorem pair_inter_one_of_overlap {p q : Finset α}
    (hp : p.card = 2) (hq : q.card = 2) (hne : p ≠ q) (hd : ¬ Disjoint p q) :
    (p ∩ q).card = 1 := by
  have hpos : 0 < (p ∩ q).card := card_pos.mpr
    (nonempty_iff_ne_empty.mpr (fun he => hd (disjoint_iff_inter_eq_empty.mpr he)))
  have hle : (p ∩ q).card ≤ 2 := by simpa [hp] using card_le_card (inter_subset_left : p ∩ q ⊆ p)
  have hne2 : (p ∩ q).card ≠ 2 := by
    intro he
    have heq : p ∩ q = p := eq_of_subset_of_card_le inter_subset_left (by omega)
    have hpq : p ⊆ q := by rw [← heq]; exact inter_subset_right
    exact hne (eq_of_subset_of_card_le hpq (by omega))
  omega

theorem residual_witness_inter {M : Finset (Finset α)} {B Q R a b p q : Finset α}
    (hM : Matching M) (hQ : Q ∈ M) (hR : R ∈ M) (hQR : Q ≠ R)
    (hB : Disjoint B (covered M)) (ha : a ⊆ Q) (hb : b ⊆ R)
    (hp : p ⊆ B) (hq : q ⊆ B) : (a ∪ p) ∩ (b ∪ q) = p ∩ q := by
  have hab : Disjoint a b := (hM hQ hR hQR).mono ha hb
  have hap : Disjoint a q :=
    (hB.mono hq (ha.trans (subset_covered hQ))).symm
  have hpb : Disjoint p b := hB.mono hp (hb.trans (subset_covered hR))
  ext x
  simp only [mem_inter, mem_union]
  constructor
  · rintro ⟨hxa | hxp, hxb | hxq⟩
    · exact False.elim ((disjoint_left.mp hab) hxa hxb)
    · exact False.elim ((disjoint_left.mp hap) hxa hxq)
    · exact False.elim ((disjoint_left.mp hpb) hxp hxb)
    · exact ⟨hxp, hxq⟩
  · rintro ⟨hp', hq'⟩
    exact ⟨Or.inr hp', Or.inr hq'⟩

theorem different_colours_eq_or_disjoint {F M : Finset (Finset α)}
    {B Q R p q : Finset α} (hF : NoSingleton F) (hM : Matching M)
    (hB : Disjoint B (covered M)) (hQ : Q ∈ M) (hR : R ∈ M) (hQR : Q ≠ R)
    (hp : p ∈ B.powersetCard 2) (hq : q ∈ B.powersetCard 2)
    (hcp : ColouredBy F Q p) (hcq : ColouredBy F R q) :
    p = q ∨ Disjoint p q := by
  by_cases he : p = q
  · exact Or.inl he
  right
  by_contra hd
  obtain ⟨a, ha, haF⟩ := hcp
  obtain ⟨b, hb, hbF⟩ := hcq
  have hi := residual_witness_inter hM hQ hR hQR hB
    (mem_powersetCard.mp ha).1 (mem_powersetCard.mp hb).1
    (mem_powersetCard.mp hp).1 (mem_powersetCard.mp hq).1
  have h1 := pair_inter_one_of_overlap (mem_powersetCard.mp hp).2
    (mem_powersetCard.mp hq).2 he hd
  exact hF (a ∪ p) haF (b ∪ q) hbF (by rw [hi, h1])

theorem isolatedPairs_matching (F M : Finset (Finset α)) (B : Finset α) :
    Matching (isolatedPairs F M B) := by
  classical
  intro p hp q hq hne
  exact (mem_filter.mp hp).2 q (mem_filter.mp hq).1 hne

theorem isolatedPairs_uniform (F M : Finset (Finset α)) (B : Finset α) :
    Uniform 2 (isolatedPairs F M B) := by
  classical
  intro p hp
  exact (mem_powersetCard.mp (mem_filter.mp (mem_filter.mp hp).1).1).2

theorem isolated_union_card (F M : Finset (Finset α)) (B : Finset α) :
    (covered (isolatedPairs F M B)).card = 2 * (isolatedPairs F M B).card :=
  card_covered (isolatedPairs_matching F M B) (isolatedPairs_uniform F M B)

theorem isolated_union_card_zero_or_two (F M : Finset (Finset α)) (B : Finset α) :
    (covered (isolatedPairs F M B)).card = 0 ∨
      2 ≤ (covered (isolatedPairs F M B)).card := by
  rw [isolated_union_card]
  omega

theorem mem_colouredPairs {F M : Finset (Finset α)} {B p : Finset α} :
    p ∈ colouredPairs F M B ↔ p ∈ B.powersetCard 2 ∧ ∃ Q ∈ M, ColouredBy F Q p := by
  classical
  exact mem_filter

theorem multiple_colours_isolated {F M : Finset (Finset α)} {B Q R p : Finset α}
    (hF : NoSingleton F) (hM : Matching M) (hB : Disjoint B (covered M))
    (hp : p ∈ colouredPairs F M B) (hQ : Q ∈ M) (hR : R ∈ M) (hQR : Q ≠ R)
    (hcp : ColouredBy F Q p) (hcr : ColouredBy F R p) :
    p ∈ isolatedPairs F M B := by
  classical
  apply mem_filter.mpr
  refine ⟨hp, ?_⟩
  intro q hq hne
  obtain ⟨hqB, T, hT, hct⟩ := mem_colouredPairs.mp hq
  have hpB := (mem_colouredPairs.mp hp).1
  by_cases hQT : Q = T
  · have hRT : R ≠ T := by intro he; exact hQR (hQT.trans he.symm)
    exact (different_colours_eq_or_disjoint hF hM hB hR hT hRT hpB hqB hcr hct).resolve_left hne
  · exact (different_colours_eq_or_disjoint hF hM hB hQ hT hQT hpB hqB hcp hct).resolve_left hne

theorem colourSupports_pairwiseDisjoint {F M : Finset (Finset α)} {B : Finset α}
    (hF : NoSingleton F) (hM : Matching M) (hB : Disjoint B (covered M)) :
    (M : Set (Finset α)).PairwiseDisjoint (colourSupport F M B) := by
  classical
  intro Q hQ R hR hQR
  apply disjoint_left.mpr
  intro x hxQ hxR
  obtain ⟨p, hp, hxp⟩ := mem_biUnion.mp hxQ
  obtain ⟨q, hq, hxq⟩ := mem_biUnion.mp hxR
  obtain ⟨hpcol, hpnot⟩ := mem_sdiff.mp (mem_filter.mp hp).1
  obtain ⟨hqcol, hqnot⟩ := mem_sdiff.mp (mem_filter.mp hq).1
  have hcp := (mem_filter.mp hp).2
  have hcq := (mem_filter.mp hq).2
  rcases different_colours_eq_or_disjoint hF hM hB hQ hR hQR
    (mem_colouredPairs.mp hpcol).1 (mem_colouredPairs.mp hqcol).1 hcp hcq with he | hd
  · subst q
    exact hpnot (multiple_colours_isolated hF hM hB hpcol hQ hR hQR hcp hcq)
  · exact disjoint_left.mp hd hxp hxq

theorem colourSupport_disjoint_isolated (F M : Finset (Finset α)) (B Q : Finset α) :
    Disjoint (colourSupport F M B Q) (covered (isolatedPairs F M B)) := by
  classical
  apply disjoint_left.mpr
  intro x hxC hxD
  obtain ⟨p, hp, hxp⟩ := mem_biUnion.mp hxC
  obtain ⟨q, hq, hxq⟩ := mem_biUnion.mp hxD
  obtain ⟨hpcol, hpnot⟩ := mem_sdiff.mp (mem_filter.mp hp).1
  have hpq : q ≠ p := by intro he; exact hpnot (he ▸ hq)
  exact disjoint_left.mp ((mem_filter.mp hq).2 p hpcol hpq) hxq hxp

theorem colourSupport_subset (F M : Finset (Finset α)) (B Q : Finset α) :
    colourSupport F M B Q ⊆ B := by
  classical
  intro x hx
  obtain ⟨p, hp, hxp⟩ := mem_biUnion.mp hx
  have hpcol := (mem_sdiff.mp (mem_filter.mp hp).1).1
  exact (mem_powersetCard.mp (mem_colouredPairs.mp hpcol).1).1 hxp

theorem exists_overlapping_colouredPair {F M : Finset (Finset α)} {B p : Finset α}
    (hp : p ∈ colouredPairs F M B) (hn : p ∉ isolatedPairs F M B) :
    ∃ q ∈ colouredPairs F M B, p ≠ q ∧ ¬ Disjoint p q := by
  classical
  by_contra! h
  exact hn (mem_filter.mpr ⟨hp, h⟩)

theorem colourSupport_card_zero_or_three {F M : Finset (Finset α)} {B Q : Finset α}
    (hF : NoSingleton F) (hM : Matching M) (hB : Disjoint B (covered M)) (hQ : Q ∈ M) :
    (colourSupport F M B Q).card = 0 ∨ 3 ≤ (colourSupport F M B Q).card := by
  classical
  by_cases hz : (colourSupport F M B Q).card = 0
  · exact Or.inl hz
  right
  obtain ⟨x, hx⟩ := card_pos.mp (Nat.pos_of_ne_zero hz)
  obtain ⟨p, hp, hxp⟩ := mem_biUnion.mp hx
  obtain ⟨hpcol, hpnot⟩ := mem_sdiff.mp (mem_filter.mp hp).1
  have hcp := (mem_filter.mp hp).2
  obtain ⟨q, hqcol, hpq, hnd⟩ := exists_overlapping_colouredPair hpcol hpnot
  obtain ⟨hqB, R, hR, hcr⟩ := mem_colouredPairs.mp hqcol
  have hpB := (mem_colouredPairs.mp hpcol).1
  have hQR : Q = R := by
    by_contra hne
    exact hnd ((different_colours_eq_or_disjoint hF hM hB hQ hR hne hpB hqB hcp hcr).resolve_left hpq)
  subst R
  have hqn : q ∉ isolatedPairs F M B := by
    intro hi
    exact hnd (((mem_filter.mp hi).2 p hpcol hpq.symm).symm)
  have hqmem : q ∈ ((colouredPairs F M B \ isolatedPairs F M B).filter (ColouredBy F Q)) :=
    mem_filter.mpr ⟨mem_sdiff.mpr ⟨hqcol, hqn⟩, hcr⟩
  have hpSub : p ⊆ colourSupport F M B Q := fun y hy => mem_biUnion.mpr ⟨p, hp, hy⟩
  have hqSub : q ⊆ colourSupport F M B Q := fun y hy => mem_biUnion.mpr ⟨q, hqmem, hy⟩
  have hu := card_le_card (union_subset hpSub hqSub)
  have hi := pair_inter_one_of_overlap (mem_powersetCard.mp hpB).2
    (mem_powersetCard.mp hqB).2 hpq hnd
  have hs := card_union_add_card_inter p q
  have hp2 := (mem_powersetCard.mp hpB).2
  have hq2 := (mem_powersetCard.mp hqB).2
  omega

end JSP572Four
