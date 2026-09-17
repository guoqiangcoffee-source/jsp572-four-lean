import JSP572Four.TripleBound
import JSP572Four.ShiftedLink
import Mathlib.Data.Fintype.EquivFin

namespace JSP572Four

open Finset

theorem shifted_four_large_bound : ∀ n, 9 ≤ n → ∀ F : Finset (Finset (Fin n)),
    Uniform 4 F → TwoIntersecting F → LeftClosed F → F.card ≤ (n - 2).choose 2 := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base =>
      intro F hu hi hc
      change F.card ≤ 21
      exact shifted_nine hu hi hc
  | succ n hn ih =>
      intro F hu hi hc
      have hs : Shifted F := hc
      have hd := ih (deleteMax F) (uniform_deleteMax hu) (twoIntersecting_deleteMax hi)
        (shifted_deleteMax hs)
      have hl := shifted_triple_bound (by omega : 6 ≤ n) (uniform_linkMax hu)
        (twoIntersecting_linkMax (by omega) hu hi hs) (shifted_linkMax hs)
      calc
        F.card = (deleteMax F).card + (linkMax F).card :=
          (card_deleteMax_add_card_linkMax F).symm
        _ ≤ (n - 2).choose 2 + (n - 2) := Nat.add_le_add hd hl
        _ = (n + 1 - 2).choose 2 := by
          have he : n + 1 - 2 = (n - 2) + 1 := by omega
          rw [he, Nat.choose_succ_succ]
          simp [Nat.add_comm]

theorem shifted_four_bound {n : ℕ} {F : Finset (Finset (Fin n))}
    (hu : Uniform 4 F) (hi : TwoIntersecting F) (hc : LeftClosed F) :
    F.card ≤ sharpBound n := by
  by_cases hn : n ≤ 6
  · simpa [sharpBound, hn] using card_le_choose (X := univ)
      (fun A _ => subset_univ A) hu
  · by_cases h7 : n = 7
    · subst n
      simpa [sharpBound] using shifted_seven hu hi hc
    · by_cases h8 : n = 8
      · subst n
        simpa [sharpBound] using shifted_eight hu hi hc
      · simpa [sharpBound, hn, h7, h8] using shifted_four_large_bound n (by omega) F hu hi hc

/-- The sharp numerical bound for every two-intersecting four-uniform family. -/
theorem twoIntersecting_bound_fin {n : ℕ} {F : Finset (Finset (Fin n))}
    (hu : Uniform 4 F) (hi : TwoIntersecting F) : F.card ≤ sharpBound n := by
  obtain ⟨G, hcard, huG, hiG, hsG⟩ := exists_shifted F hu hi
  have h := shifted_four_bound huG hiG hsG
  simpa [hcard] using h

/-- Relabeling the finite ground set gives the bound on an arbitrary ambient type. -/
theorem twoIntersecting_bound {α : Type*} [DecidableEq α]
    {X : Finset α} {F : Finset (Finset α)}
    (hX : Supported X F) (hu : Uniform 4 F) (hi : TwoIntersecting F) :
    F.card ≤ sharpBound X.card := by
  classical
  let e : X ≃ Fin X.card := X.equivFinOfCardEq rfl
  let f : Finset α → Finset (Fin X.card) := fun A => (A.subtype (· ∈ X)).map e.toEmbedding
  have hfcard {A : Finset α} (hA : A ⊆ X) : (f A).card = A.card := by
    simp [f, filter_eq_self.mpr hA]
  have hfinj : Set.InjOn f ↑F := by
    intro A hA B hB heq
    ext x
    by_cases hx : x ∈ X
    · let q : X := ⟨x, hx⟩
      have hmem := congrArg (fun S => e q ∈ S) heq
      simpa [f,q] using hmem
    · have ha : x ∉ A := fun h => hx (hX A hA h)
      have hb : x ∉ B := fun h => hx (hX B hB h)
      simp [ha,hb]
  have hfinter (A B : Finset α) : f (A ∩ B) = f A ∩ f B := by
    dsimp [f]
    rw [← map_inter]
    congr 1
    ext x
    simp
  have hu' : Uniform 4 (F.image f) := by
    intro A hA
    obtain ⟨B,hB,rfl⟩ := mem_image.mp hA
    rw [hfcard (hX B hB)]
    exact hu B hB
  have hi' : TwoIntersecting (F.image f) := by
    intro A hA B hB
    obtain ⟨A0,ha0,rfl⟩ := mem_image.mp hA
    obtain ⟨B0,hb0,rfl⟩ := mem_image.mp hB
    rw [← hfinter, hfcard (fun x hx => hX A0 ha0 (mem_inter.mp hx).1)]
    exact hi A0 ha0 B0 hb0
  have hbound := twoIntersecting_bound_fin hu' hi'
  rwa [card_image_of_injOn hfinj] at hbound

end JSP572Four
