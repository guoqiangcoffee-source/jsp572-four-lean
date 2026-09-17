import JSP572Four.ResidualPartition
import JSP572Four.PerfectMatchingBound

namespace JSP572Four

open Finset

variable {α : Type*} [DecidableEq α]

/-- Every member lies inside the matching ground or meets one of the three
parts of the uncovered ground. The counts may overlap, which only helps. -/
theorem global_card_cover {X : Finset α} {F M : Finset (Finset α)}
    (hX : Supported X F) :
    F.card ≤ (F.filter (fun S => S ⊆ covered M)).card +
      (F.filter (fun S => ¬ Disjoint S (residualC F M (X \ covered M)))).card +
      (F.filter (fun S => ¬ Disjoint S (residualD F M (X \ covered M)))).card +
      (F.filter (fun S => ¬ Disjoint S (residualE F M (X \ covered M)))).card := by
  classical
  let I := F.filter (fun S => S ⊆ covered M)
  let C := F.filter (fun S => ¬ Disjoint S (residualC F M (X \ covered M)))
  let D := F.filter (fun S => ¬ Disjoint S (residualD F M (X \ covered M)))
  let E := F.filter (fun S => ¬ Disjoint S (residualE F M (X \ covered M)))
  have hcover : F ⊆ I ∪ C ∪ D ∪ E := by
    intro S hS
    by_cases hI : S ⊆ covered M
    · exact mem_union_left _ (mem_union_left _ (mem_union_left _ (mem_filter.mpr ⟨hS, hI⟩)))
    obtain ⟨x, hxS, hxn⟩ := Finset.not_subset.mp hI
    have hxB : x ∈ X \ covered M := mem_sdiff.mpr ⟨hX S hS hxS, hxn⟩
    by_cases hxC : x ∈ residualC F M (X \ covered M)
    · have hm : S ∈ C := mem_filter.mpr ⟨hS, not_disjoint_iff.mpr ⟨x, hxS, hxC⟩⟩
      exact mem_union_left _ (mem_union_left _ (mem_union_right _ hm))
    by_cases hxD : x ∈ residualD F M (X \ covered M)
    · have hm : S ∈ D := mem_filter.mpr ⟨hS, not_disjoint_iff.mpr ⟨x, hxS, hxD⟩⟩
      exact mem_union_left _ (mem_union_right _ hm)
    have hxE : x ∈ residualE F M (X \ covered M) :=
      mem_sdiff.mpr ⟨hxB, by simpa only [mem_union, not_or] using And.intro hxC hxD⟩
    exact mem_union_right _ (mem_filter.mpr ⟨hS, not_disjoint_iff.mpr ⟨x, hxS, hxE⟩⟩)
  change F.card ≤ I.card + C.card + D.card + E.card
  calc
    F.card ≤ (I ∪ C ∪ D ∪ E).card := card_le_card hcover
    _ ≤ (I ∪ C ∪ D).card + E.card := card_union_le _ _
    _ ≤ (I ∪ C).card + D.card + E.card := by
      exact Nat.add_le_add_right (card_union_le _ _) _
    _ ≤ I.card + C.card + D.card + E.card := by
      exact Nat.add_le_add_right (Nat.add_le_add_right (card_union_le _ _) _) _

theorem internal_matching_card_bound {F M : Finset (Finset α)}
    (hu : Uniform 4 F) (hn : NoSingleton F) (hM : MaximumMatching F M) :
    2 * (F.filter (fun S => S ⊆ covered M)).card + 10 * M.card ≤
      12 * M.card ^ 2 := by
  apply perfectMatching_card_bound_polynomial (M := M)
  · intro Q hQ
    exact mem_filter.mpr ⟨hM.1 hQ, subset_covered hQ⟩
  · exact hM.2.1
  · intro S hS
    exact hu S (mem_filter.mp hS).1
  · intro S hS T hT
    exact hn S (mem_filter.mp hS).1 T (mem_filter.mp hT).1
  · intro S hS
    exact (mem_filter.mp hS).2

theorem maximumMatching_card_ge_two {F M : Finset (Finset α)}
    (hu : Uniform 4 F) (hM : MaximumMatching F M)
    (hd : ∃ A ∈ F, ∃ B ∈ F, Disjoint A B) : 2 ≤ M.card := by
  obtain ⟨A, hA, B, hB, hAB⟩ := hd
  have hne : A ≠ B := by
    intro he
    have he0 : A = ∅ := disjoint_self.mp (he ▸ hAB)
    have hc := hu A hA
    simp [he0] at hc
  have hsub : ({A, B} : Finset (Finset α)) ⊆ F :=
    insert_subset hA (singleton_subset_iff.mpr hB)
  have hmat : Matching ({A, B} : Finset (Finset α)) := by
    intro S hS T hT hST
    simp only [mem_coe, mem_insert, mem_singleton] at hS hT
    rcases hS with rfl | rfl <;> rcases hT with rfl | rfl
    · exact False.elim (hST rfl)
    · exact hAB
    · exact hAB.symm
    · exact False.elim (hST rfl)
  have h := hM.2.2 _ hsub hmat
  simpa [hne] using h

end JSP572Four
