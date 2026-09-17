import JSP572Four.Basic
import Mathlib.Tactic

namespace JSP572Four
open Finset
variable {α : Type*} [DecidableEq α]

def Matching (M : Finset (Finset α)) : Prop :=
  (M : Set (Finset α)).PairwiseDisjoint id

def MaximumMatching (F M : Finset (Finset α)) : Prop :=
  M ⊆ F ∧ Matching M ∧ ∀ N ⊆ F, Matching N → N.card ≤ M.card

def covered (M : Finset (Finset α)) : Finset α := M.biUnion id

omit [DecidableEq α] in
theorem exists_maximumMatching (F : Finset (Finset α)) :
    ∃ M, MaximumMatching F M := by
  classical
  let candidates := F.powerset.filter Matching
  have he : ∅ ∈ candidates := by simp [candidates, Matching]
  obtain ⟨M, hM, hmax⟩ := candidates.exists_max_image Finset.card ⟨∅, he⟩
  refine ⟨M, (mem_powerset.mp (mem_filter.mp hM).1), (mem_filter.mp hM).2, ?_⟩
  intro N hN hmat
  exact hmax N (mem_filter.mpr ⟨mem_powerset.mpr hN, hmat⟩)

theorem card_covered {M : Finset (Finset α)} {k : ℕ}
    (hM : Matching M) (hU : Uniform k M) : (covered M).card = k * M.card := by
  unfold covered
  rw [card_biUnion hM]
  calc
    ∑ A ∈ M, (id A).card = ∑ _A ∈ M, k := sum_congr rfl (fun A hA => hU A hA)
    _ = k * M.card := by simp [Nat.mul_comm]

theorem subset_covered {M : Finset (Finset α)} {A : Finset α} (hA : A ∈ M) :
    A ⊆ covered M := by
  intro x hx
  exact mem_biUnion.mpr ⟨A, hA, hx⟩

theorem covered_subset {X : Finset α} {M : Finset (Finset α)} (hM : Supported X M) :
    covered M ⊆ X := by
  intro x hx
  obtain ⟨A, hA, hxA⟩ := mem_biUnion.mp hx
  exact hM A hA hxA

theorem MaximumMatching.every_member_meets {F M : Finset (Finset α)}
    (hM : MaximumMatching F M) (hU : Uniform 4 F) {S : Finset α} (hS : S ∈ F) :
    ¬ Disjoint S (covered M) := by
  intro hd
  have hnot : S ∉ M := by
    intro hSm
    have hh : Disjoint S S := hd.mono_right (subset_covered hSm)
    have he : S = ∅ := disjoint_self.mp hh
    have hc := hU S hS
    simp [he] at hc
  have hins : Matching (insert S M) := by
    change (↑(insert S M) : Set (Finset α)).PairwiseDisjoint id
    rw [coe_insert]
    apply hM.2.1.insert
    intro B hB _
    exact hd.mono_right (subset_covered hB)
  have hc := hM.2.2 (insert S M) (insert_subset hS hM.1) hins
  rw [card_insert_of_notMem hnot] at hc
  omega

theorem twoIntersecting_of_no_disjoint {F : Finset (Finset α)}
    (hF : NoSingleton F) (hn : ∀ A ∈ F, ∀ B ∈ F, ¬ Disjoint A B) :
    TwoIntersecting F := by
  intro A hA B hB
  have hpos : 0 < (A ∩ B).card := by
    apply card_pos.mpr
    apply nonempty_iff_ne_empty.mpr
    intro he
    exact hn A hA B hB (disjoint_iff_inter_eq_empty.mpr he)
  have hne := hF A hA B hB
  omega

theorem nonintersecting_ground_large {X A B : Finset α}
    (hA : A ⊆ X) (hB : B ⊆ X) (hAc : A.card = 4) (hBc : B.card = 4)
    (hd : Disjoint A B) : 8 ≤ X.card := by
  have hu := card_le_card (union_subset hA hB)
  rw [card_union_of_disjoint hd, hAc, hBc] at hu
  exact hu

theorem four_mul_matching_card_le {X : Finset α} {F M : Finset (Finset α)}
    (hX : Supported X F) (hU : Uniform 4 F) (hM : MaximumMatching F M) :
    4 * M.card ≤ X.card := by
  have hUm : Uniform 4 M := fun A hA => hU A (hM.1 hA)
  have hXm : Supported X M := fun A hA => hX A (hM.1 hA)
  rw [← card_covered hM.2.1 hUm]
  exact card_le_card (covered_subset hXm)

end JSP572Four
