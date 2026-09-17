import JSP572Four.ShiftedBound
import JSP572Four.Constructions
import Mathlib.Data.Finset.Sort

namespace JSP572Four

open Finset

lemma triple_representation {n : ℕ} {A : Finset (Fin n)} (hA : A.card = 3) :
    ∃ x y z : Fin n, x < y ∧ y < z ∧ A = {x,y,z} := by
  let e := A.orderEmbOfFin hA
  refine ⟨e 0, e 1, e 2, e.strictMono (by decide), e.strictMono (by decide), ?_⟩
  have he := A.image_orderEmbOfFin_univ hA
  have hfin : (univ : Finset (Fin 3)) = {0,1,2} := by decide
  rw [hfin] at he
  simpa [e] using he.symm

/-- The shifted triple-family bound needed for the inductive four-set theorem. -/
theorem shifted_triple_bound {n : ℕ} (hn : 6 ≤ n) {F : Finset (Finset (Fin n))}
    (hu : Uniform 3 F) (hi : TwoIntersecting F) (hc : LeftClosed F) : F.card ≤ n - 2 := by
  let p0 : Fin n := ⟨0, by omega⟩
  let p1 : Fin n := ⟨1, by omega⟩
  let p2 : Fin n := ⟨2, by omega⟩
  let p3 : Fin n := ⟨3, by omega⟩
  let p4 : Fin n := ⟨4, by omega⟩
  have h01 : p0 < p1 := by change (0 : ℕ) < 1; decide
  have h12 : p1 < p2 := by change (1 : ℕ) < 2; decide
  have h23 : p2 < p3 := by change (2 : ℕ) < 3; decide
  have h14 : p1 < p4 := by change (1 : ℕ) < 4; decide
  by_cases ht : ({p0,p2,p3} : Finset (Fin n)) ∈ F
  · have hforbid : ({p0,p1,p4} : Finset (Fin n)) ∉ F := by
      intro hh
      have h := hi _ ht _ hh
      have he : (({p0,p2,p3} : Finset (Fin n)) ∩ {p0,p1,p4}).card = 1 := by
        simp [p0,p1,p2,p3,p4]
      omega
    have hs : Supported ({p0,p1,p2,p3} : Finset (Fin n)) F := by
      intro A hA a ha
      obtain ⟨x,y,z,hxy,hyz,rfl⟩ := triple_representation (hu A hA)
      have hz : z.val < 4 := by
        by_contra! hz
        apply hforbid
        apply leftClosed_triple hc h01 h14 hxy hyz
        · change 0 ≤ x.val; omega
        · change 1 ≤ y.val; have := x.isLt; omega
        · exact hz
        · exact hA
      simp only [mem_insert, mem_singleton] at ha ⊢
      simp only [Fin.ext_iff, p0, p1, p2, p3]
      have hxyv : x.val < y.val := hxy
      have hyzv : y.val < z.val := hyz
      rcases ha with rfl | rfl | rfl <;> omega
    have hcard : ({p0,p1,p2,p3} : Finset (Fin n)).card = 4 := by simp [p0,p1,p2,p3]
    have hbound := card_le_choose hs hu
    rw [hcard] at hbound
    have hc4 : (4 : ℕ).choose 3 = 4 := by decide
    omega
  · let P : Finset (Fin n) := {p0,p1}
    have hs : ∀ A ∈ F, P ⊆ A := by
      intro A hA
      obtain ⟨x,y,z,hxy,hyz,rfl⟩ := triple_representation (hu A hA)
      by_cases hy : y.val < 2
      · have hx0 : x = p0 := by apply Fin.ext; dsimp [p0]; have hv : x.val < y.val := hxy; omega
        have hy1 : y = p1 := by apply Fin.ext; dsimp [p1]; have hv : x.val < y.val := hxy; omega
        simp [P,hx0,hy1]
      · exfalso
        apply ht
        apply leftClosed_triple hc (h01.trans h12) h23 hxy hyz
        · change 0 ≤ x.val; omega
        · change 2 ≤ y.val; omega
        · change 3 ≤ z.val; have hv : y.val < z.val := hyz; omega
        · exact hA
    have hP : P.card = 2 := by simp [P,p0,p1]
    have hsub : F ⊆ ((univ : Finset (Fin n)).powersetCard 3).filter (P ⊆ ·) := by
      intro A hA
      exact mem_filter.mpr ⟨mem_powersetCard.mpr ⟨subset_univ _, hu A hA⟩, hs A hA⟩
    have hbound := card_le_card hsub
    rw [card_filter_powersetCard_subset P univ 3 (subset_univ P) (by omega)] at hbound
    simpa [hP] using hbound

end JSP572Four
