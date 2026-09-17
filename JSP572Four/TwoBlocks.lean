import JSP572Four.Basic
import JSP572Four.TwoBlockLinks

/-!
The two-block case of Keevash--Mubayi--Wilson, Lemma 3.1.
No enumeration of families is needed: the proof factors through the six links
of one four-element block into the other.
-/

namespace JSP572Four

open Finset

variable {α : Type*} [DecidableEq α]

theorem decompose_over_two_blocks {X Y S : Finset α} (hS : S ⊆ X ∪ Y) :
    (S ∩ X) ∪ (S ∩ Y) = S := by
  rw [← Finset.inter_union_distrib_left]
  exact Finset.inter_eq_left.mpr hS

theorem separated_intersection_card {X Y A B C D : Finset α}
    (hXY : Disjoint X Y) (hAX : A ⊆ X) (hBY : B ⊆ Y)
    (hCX : C ⊆ X) (hDY : D ⊆ Y) :
    ((A ∪ B) ∩ (C ∪ D)).card = (A ∩ C).card + (B ∩ D).card := by
  have heq : (A ∪ B) ∩ (C ∪ D) = (A ∩ C) ∪ (B ∩ D) := by
    ext x
    simp only [mem_inter, mem_union]
    constructor
    · rintro ⟨ha | hb, hc | hd⟩
      · exact Or.inl ⟨ha, hc⟩
      · exact False.elim (Finset.disjoint_left.mp hXY (hAX ha) (hDY hd))
      · exact False.elim (Finset.disjoint_left.mp hXY (hCX hc) (hBY hb))
      · exact Or.inr ⟨hb, hd⟩
    · rintro (⟨ha, hc⟩ | ⟨hb, hd⟩)
      · exact ⟨Or.inl ha, Or.inl hc⟩
      · exact ⟨Or.inr hb, Or.inr hd⟩
  rw [heq]
  exact card_union_of_disjoint
    (hXY.mono (inter_subset_left.trans hAX) (inter_subset_left.trans hBY))

/-- At most twelve members can split two-plus-two across two disjoint
four-element blocks when singleton intersections are forbidden. -/
theorem cross_family_card_le_twelve (X Y : Finset α) (F : Finset (Finset α))
    (hX : X.card = 4) (hY : Y.card = 4) (hXY : Disjoint X Y)
    (hsupport : Supported (X ∪ Y) F) (havoid : NoSingleton F)
    (hsplit : ∀ S ∈ F, (S ∩ X).card = 2 ∧ (S ∩ Y).card = 2) :
    F.card ≤ 12 := by
  classical
  let R := ((X.powersetCard 2).product (Y.powersetCard 2)).filter
    (fun p => p.1 ∪ p.2 ∈ F)
  have hcompatible : ∀ A ∈ X.powersetCard 2, ∀ B ∈ Y.powersetCard 2,
      ∀ C ∈ X.powersetCard 2, ∀ D ∈ Y.powersetCard 2,
      (A, B) ∈ R → (C, D) ∈ R → (A ∩ C).card + (B ∩ D).card ≠ 1 := by
    intro A hA B hB C hC D hD hAB hCD
    have hh := havoid (A ∪ B) (mem_filter.mp hAB).2
      (C ∪ D) (mem_filter.mp hCD).2
    rw [separated_intersection_card hXY (mem_powersetCard.mp hA).1
      (mem_powersetCard.mp hB).1 (mem_powersetCard.mp hC).1
      (mem_powersetCard.mp hD).1] at hh
    exact hh
  have hcover : F ⊆ (X.powersetCard 2).biUnion
      (fun A => (pairLink Y R A).image (fun B => A ∪ B)) := by
    intro S hS
    have hSX : S ∩ X ∈ X.powersetCard 2 :=
      mem_powersetCard.mpr ⟨inter_subset_right, (hsplit S hS).1⟩
    have hSY : S ∩ Y ∈ Y.powersetCard 2 :=
      mem_powersetCard.mpr ⟨inter_subset_right, (hsplit S hS).2⟩
    have hdecomp := decompose_over_two_blocks (hsupport S hS)
    apply mem_biUnion.mpr
    refine ⟨S ∩ X, hSX, ?_⟩
    apply mem_image.mpr
    refine ⟨S ∩ Y, ?_, hdecomp⟩
    apply mem_filter.mpr
    refine ⟨hSY, ?_⟩
    apply mem_filter.mpr
    refine ⟨mem_product.mpr ⟨hSX, hSY⟩, ?_⟩
    change (S ∩ X) ∪ (S ∩ Y) ∈ F
    rw [hdecomp]
    exact hS
  calc
    F.card ≤ ((X.powersetCard 2).biUnion
        (fun A => (pairLink Y R A).image (fun B => A ∪ B))).card := card_le_card hcover
    _ ≤ ∑ A ∈ X.powersetCard 2, ((pairLink Y R A).image (fun B => A ∪ B)).card :=
      card_biUnion_le
    _ ≤ ∑ A ∈ X.powersetCard 2, (pairLink Y R A).card :=
      sum_le_sum (fun A _ => card_image_le)
    _ ≤ 12 := two_block_link_sum_le_twelve X Y R hX hY hcompatible

/-- The base case of the perfect-matching bound: a family supported on two
disjoint four-element members has cardinality at most fourteen. -/
theorem two_block_family_card_le_fourteen (X Y : Finset α) (F : Finset (Finset α))
    (hX : X.card = 4) (hY : Y.card = 4) (hXY : Disjoint X Y)
    (hXF : X ∈ F) (hYF : Y ∈ F) (huniform : Uniform 4 F)
    (hsupport : Supported (X ∪ Y) F) (havoid : NoSingleton F) :
    F.card ≤ 14 := by
  classical
  let G := (F.erase X).erase Y
  have hGF : G ⊆ F := (erase_subset _ _).trans (erase_subset _ _)
  have hsplit : ∀ S ∈ G, (S ∩ X).card = 2 ∧ (S ∩ Y).card = 2 := by
    intro S hS
    have hSF := hGF hS
    have hSc := huniform S hSF
    have hSX : S ≠ X := (mem_erase.mp (mem_erase.mp hS).2).1
    have hSY : S ≠ Y := (mem_erase.mp hS).1
    have hnotX : (S ∩ X).card ≠ 4 := by
      intro hh
      have hEqS : S ∩ X = S := eq_of_subset_of_card_le inter_subset_left (by omega)
      have hEqX : S ∩ X = X := eq_of_subset_of_card_le inter_subset_right (by omega)
      exact hSX (hEqS.symm.trans hEqX)
    have hnotY : (S ∩ Y).card ≠ 4 := by
      intro hh
      have hEqS : S ∩ Y = S := eq_of_subset_of_card_le inter_subset_left (by omega)
      have hEqY : S ∩ Y = Y := eq_of_subset_of_card_le inter_subset_right (by omega)
      exact hSY (hEqS.symm.trans hEqY)
    have hxone := havoid S hSF X hXF
    have hyone := havoid S hSF Y hYF
    have hdis : Disjoint (S ∩ X) (S ∩ Y) :=
      hXY.mono inter_subset_right inter_subset_right
    have hsum := card_union_of_disjoint hdis
    rw [decompose_over_two_blocks (hsupport S hSF), hSc] at hsum
    omega
  have hGbound := cross_family_card_le_twelve X Y G hX hY hXY
    (fun S hS => hsupport S (hGF hS))
    (fun S hS T hT => havoid S (hGF hS) T (hGF hT)) hsplit
  have hfirst := pred_card_le_card_erase (s := F) (a := X)
  have hsecond := pred_card_le_card_erase (s := F.erase X) (a := Y)
  change ((F.erase X).erase Y).card ≤ 12 at hGbound
  omega

end JSP572Four
