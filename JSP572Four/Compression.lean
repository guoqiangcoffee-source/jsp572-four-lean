import JSP572Four.Basic
import Mathlib.Combinatorics.SetFamily.Compression.UV
import Mathlib.Combinatorics.SetFamily.KruskalKatona
import Mathlib.Tactic

namespace JSP572Four

open Finset

variable {n : ℕ}

/-- Closure under replacing one member by a smaller unused member. -/
def Shifted (F : Finset (Finset (Fin n))) : Prop :=
  ∀ (i j : Fin n), i < j → ∀ A ∈ F, j ∈ A → i ∉ A →
    insert i (A.erase j) ∈ F

def shiftSet (i j : Fin n) (A : Finset (Fin n)) : Finset (Fin n) :=
  UV.compress {i} {j} A

def shiftFamily (i j : Fin n) (F : Finset (Finset (Fin n))) :=
  UV.compression {i} {j} F

def flipSet (i j : Fin n) (A : Finset (Fin n)) : Finset (Fin n) :=
  A.image (Equiv.swap i j)

lemma mem_flipSet (i j x : Fin n) (A : Finset (Fin n)) :
    x ∈ flipSet i j A ↔ Equiv.swap i j x ∈ A := by
  simp only [flipSet, mem_image]
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa using hy
  · intro hx
    exact ⟨Equiv.swap i j x, hx, by simp⟩

lemma flipSet_inter (i j : Fin n) (A B : Finset (Fin n)) :
    flipSet i j (A ∩ B) = flipSet i j A ∩ flipSet i j B := by
  ext x
  simp only [mem_flipSet, mem_inter]

lemma card_flipSet (i j : Fin n) (A : Finset (Fin n)) :
    (flipSet i j A).card = A.card :=
  card_image_of_injective _ (Equiv.swap i j).injective

lemma card_flipSet_inter (i j : Fin n) (A B : Finset (Fin n)) :
    (flipSet i j A ∩ flipSet i j B).card = (A ∩ B).card := by
  rw [← flipSet_inter, card_flipSet]

lemma flipSet_eq_self (i j : Fin n) (A : Finset (Fin n))
    (h : i ∈ A ↔ j ∈ A) : flipSet i j A = A := by
  ext x
  rw [mem_flipSet]
  by_cases hxi : x = i
  · subst x
    simpa using h.symm
  by_cases hxj : x = j
  · subst x
    simpa using h
  simp [Equiv.swap_apply_of_ne_of_ne hxi hxj]

lemma shiftSet_eq (i j : Fin n) (A : Finset (Fin n)) :
    shiftSet i j A = if i ∉ A ∧ j ∈ A then insert i (A.erase j) else A := by
  simp only [shiftSet, UV.compress, disjoint_singleton_left, singleton_subset_iff,
    sup_eq_union]
  split_ifs with h
  · ext x
    simp only [mem_sdiff, mem_union, mem_singleton, mem_insert, mem_erase]
    have hij : i ≠ j := by rintro rfl; exact h.1 h.2
    grind
  · rfl

lemma shiftSet_eq_flipSet (i j : Fin n) (A : Finset (Fin n))
    (hi : i ∉ A) (hj : j ∈ A) : shiftSet i j A = flipSet i j A := by
  rw [shiftSet_eq, ite_eq_left ⟨hi, hj⟩]
  have hij : i ≠ j := by rintro rfl; exact hi hj
  ext x
  rw [mem_flipSet]
  by_cases hxi : x = i
  · subst x
    simp [hj]
  by_cases hxj : x = j
  · subst x
    simp [hi, hij.symm]
  simp [hxi, hxj, Equiv.swap_apply_of_ne_of_ne hxi hxj]

lemma card_shiftFamily (i j : Fin n) (F : Finset (Finset (Fin n))) :
    (shiftFamily i j F).card = F.card := UV.card_compression _ _ _

lemma uniform_shiftFamily {k : ℕ} (i j : Fin n)
    {F : Finset (Finset (Fin n))} (hF : Uniform k F) :
    Uniform k (shiftFamily i j F) := by
  exact Set.Sized.uvCompression (by simp) hF

lemma new_shiftFamily_properties (i j : Fin n)
    {F : Finset (Finset (Fin n))} {A : Finset (Fin n)}
    (hA : A ∈ shiftFamily i j F) (hnew : A ∉ F) :
    i ∈ A ∧ j ∉ A ∧ flipSet i j A ∈ F := by
  have hi : i ∈ A := by
    simpa using UV.le_of_mem_compression_of_notMem hA hnew
  have hj : j ∉ A := by
    simpa using UV.disjoint_of_mem_compression_of_notMem hA hnew
  have hback := UV.sup_sdiff_mem_of_mem_compression_of_notMem hA hnew
  refine ⟨hi, hj, ?_⟩
  have heq : (A ∪ {j}) \ {i} = flipSet i j A := by
    have hij : i ≠ j := by rintro rfl; exact hj hi
    ext x
    rw [mem_flipSet]
    by_cases hxi : x = i
    · subst x
      simp [hj]
    by_cases hxj : x = j
    · subst x
      simp [hi, hij.symm]
    simp [hxi, hxj, Equiv.swap_apply_of_ne_of_ne hxi hxj]
  simpa only [sup_eq_union, heq] using hback

lemma flipSet_mem_of_shiftFamily_mem_of_mem (i j : Fin n)
    {F : Finset (Finset (Fin n))} {B : Finset (Fin n)}
    (hB : B ∈ shiftFamily i j F) (hj : j ∈ B) :
    flipSet i j B ∈ F := by
  by_cases hi : i ∈ B
  · have hold : B ∈ F := by
      by_contra hn
      exact (new_shiftFamily_properties i j hB hn).2.1 hj
    rwa [flipSet_eq_self i j B (by simp [hi, hj])]
  · have hc : shiftSet i j B ∈ F := by
      obtain h | h := UV.mem_compression.mp hB
      · exact h.2
      · exact False.elim ((new_shiftFamily_properties i j hB h.1).2.1 hj)
    rwa [shiftSet_eq_flipSet i j B hi hj] at hc

lemma flipSet_inter_subset (i j : Fin n) (A B : Finset (Fin n))
    (hi : i ∈ A) (hjA : j ∉ A) (hjB : j ∉ B) :
    flipSet i j A ∩ B ⊆ A ∩ B := by
  intro x hx
  rcases mem_inter.mp hx with ⟨hxA, hxB⟩
  rw [mem_flipSet] at hxA
  refine mem_inter.mpr ⟨?_, hxB⟩
  by_cases hxi : x = i
  · simpa [hxi] using hi
  have hxj : x ≠ j := by rintro rfl; exact hjB hxB
  simpa [Equiv.swap_apply_of_ne_of_ne hxi hxj] using hxA

lemma twoIntersecting_shiftFamily (i j : Fin n)
    {F : Finset (Finset (Fin n))} (hF : TwoIntersecting F) :
    TwoIntersecting (shiftFamily i j F) := by
  intro A hA B hB
  by_cases ha : A ∈ F
  · by_cases hb : B ∈ F
    · exact hF A ha B hb
    · obtain ⟨hiB, hjB, hfB⟩ := new_shiftFamily_properties i j hB hb
      by_cases hjA : j ∈ A
      · have hfA := flipSet_mem_of_shiftFamily_mem_of_mem i j hA hjA
        simpa only [card_flipSet_inter] using hF _ hfA _ hfB
      · have h := (hF _ hfB _ ha).trans
          (card_le_card (flipSet_inter_subset i j B A hiB hjB hjA))
        simpa only [inter_comm] using h
  · obtain ⟨hiA, hjA, hfA⟩ := new_shiftFamily_properties i j hA ha
    by_cases hb : B ∈ F
    · by_cases hjB : j ∈ B
      · have hfB := flipSet_mem_of_shiftFamily_mem_of_mem i j hB hjB
        simpa only [card_flipSet_inter] using hF _ hfA _ hfB
      · exact (hF _ hfA _ hb).trans
          (card_le_card (flipSet_inter_subset i j A B hiA hjA hjB))
    · have hfB := (new_shiftFamily_properties i j hB hb).2.2
      simpa only [card_flipSet_inter] using hF _ hfA _ hfB

/-- A natural-valued measure which strictly decreases at each nontrivial shift. -/
def familyWeight (F : Finset (Finset (Fin n))) : ℕ :=
  ∑ A ∈ F, ∑ a ∈ A, 2 ^ (a : ℕ)

-- This termination estimate specializes the family-measure argument in Mathlib's
-- Kruskal--Katona proof (Bhavik Mehta and Yaël Dillies, Apache-2.0).
lemma familyWeight_shift_lt (i j : Fin n) (hij : i < j)
    {F : Finset (Finset (Fin n))} (hne : shiftFamily i j F ≠ F) :
    familyWeight (shiftFamily i j F) < familyWeight F := by
  classical
  unfold shiftFamily UV.compression at hne ⊢
  have q : ∀ Q ∈ {A ∈ F | UV.compress {i} {j} A ∉ F},
      UV.compress {i} {j} Q ≠ Q := by grind
  have hu : {A ∈ F | UV.compress {i} {j} A ∈ F} ∪
      {A ∈ F | UV.compress {i} {j} A ∉ F} = F :=
    filter_union_filter_not_eq _ _
  have hnonempty : {A ∈ F | UV.compress {i} {j} A ∉ F}.Nonempty := by
    contrapose! hne
    rw [filter_image, hne, image_empty, union_empty]
    rwa [hne, union_empty] at hu
  rw [familyWeight, familyWeight, sum_union UV.compress_disjoint]
  conv_rhs => rw [← hu]
  rw [sum_union (disjoint_filter_filter_not _ _ _), add_lt_add_iff_left, filter_image,
    sum_image UV.compress_injOn]
  refine sum_lt_sum_of_nonempty hnonempty fun A hA ↦ ?_
  simp_rw [← sum_image Fin.val_injective.injOn]
  rw [Finset.geomSum_lt_geomSum_iff_toColex_lt_toColex le_rfl,
    Finset.Colex.toColex_image_lt_toColex_image Fin.val_strictMono]
  apply Finset.UV.toColex_compress_lt_toColex (hU := singleton_nonempty i)
    (hV := singleton_nonempty j) _ (q _ hA)
  simpa using hij

/-- Every uniform two-intersecting family has a shifted representative of equal size. -/
theorem exists_shifted {k : ℕ} (F : Finset (Finset (Fin n)))
    (hu : Uniform k F) (ht : TwoIntersecting F) :
    ∃ G : Finset (Finset (Fin n)), G.card = F.card ∧ Uniform k G ∧
      TwoIntersecting G ∧ Shifted G := by
  classical
  by_cases hs : Shifted F
  · exact ⟨F, rfl, hu, ht, hs⟩
  · simp only [Shifted, not_forall] at hs
    obtain ⟨i, j, hij, A, hA, hjA, hiA, hmissing⟩ := hs
    have hne : shiftFamily i j F ≠ F := by
      intro heq
      have hmem : shiftSet i j A ∈ shiftFamily i j F :=
        UV.compress_mem_compression hA
      rw [heq, shiftSet_eq, ite_eq_left ⟨hiA, hjA⟩] at hmem
      exact hmissing hmem
    obtain ⟨G, hcard, huni, hinter, hshift⟩ :=
      exists_shifted (shiftFamily i j F) (uniform_shiftFamily i j hu)
        (twoIntersecting_shiftFamily i j ht)
    exact ⟨G, hcard.trans (card_shiftFamily i j F), huni, hinter, hshift⟩
termination_by familyWeight F
decreasing_by exact familyWeight_shift_lt i j hij hne

end JSP572Four
