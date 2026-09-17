import JSP572Four.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Tactic

/-!
Finite certificates for the 2-intersecting four-uniform base cases n = 7, 8, 9.
The certificates are checked by the Lean kernel using `decide`; they neither
enumerate all families nor assume the Complete Intersection Theorem.
-/

namespace JSP572Four

open Finset

variable {n : ℕ}

/-- Singleton left-shift closure; this agrees with the compression API. -/
def LeftClosed (F : Finset (Finset (Fin n))) : Prop :=
  ∀ (i j : Fin n), i < j → ∀ A ∈ F, j ∈ A → i ∉ A → insert i (A.erase j) ∈ F

lemma leftClosed_replace {F : Finset (Finset (Fin n))} (hF : LeftClosed F)
    {i j : Fin n} {S : Finset (Fin n)} (hij : i ≤ j) (hi : i ∉ S) (hj : j ∉ S)
    (hS : insert j S ∈ F) : insert i S ∈ F := by
  by_cases heq : i = j
  · simpa [heq] using hS
  · have hlt : i < j := lt_of_le_of_ne hij heq
    have := hF i j hlt (insert j S) hS (by simp) (by simp [hi, heq])
    simpa [hj] using this

/-- Lowering the three ordered coordinates requires only three ordinary shifts. -/
lemma leftClosed_triple {F : Finset (Finset (Fin n))} (hF : LeftClosed F)
    {a b c x y z : Fin n} (hab : a < b) (hbc : b < c) (hxy : x < y) (hyz : y < z)
    (hax : a ≤ x) (hby : b ≤ y) (hcz : c ≤ z) (hA : ({x,y,z} : Finset (Fin n)) ∈ F) :
    ({a,b,c} : Finset (Fin n)) ∈ F := by
  have h1 : ({a,y,z} : Finset (Fin n)) ∈ F := by
    apply leftClosed_replace hF hax
    · simp only [mem_insert, mem_singleton]; omega
    · simp only [mem_insert, mem_singleton]; omega
    · exact hA
  have h2 : ({b,a,z} : Finset (Fin n)) ∈ F := by
    apply leftClosed_replace hF hby
    · simp only [mem_insert, mem_singleton]; omega
    · simp only [mem_insert, mem_singleton]; omega
    · simpa [insert_comm] using h1
  have h3 : ({c,a,b} : Finset (Fin n)) ∈ F := by
    apply leftClosed_replace hF hcz
    · simp only [mem_insert, mem_singleton]; omega
    · simp only [mem_insert, mem_singleton]; omega
    · convert h2 using 1
      ext q
      simp [or_comm, or_left_comm]
  convert h3 using 1
  ext q
  simp [or_comm, or_left_comm]

/-- One attempted move toward a specified target, pairing the largest mismatches. -/
def lowerStep (A B : Finset (Fin n)) : Finset (Fin n) :=
  if ha : (A \ B).Nonempty then
    if hb : (B \ A).Nonempty then
      let j := (A \ B).max' ha
      let i := (B \ A).max' hb
      if i < j then insert i (A.erase j) else A
    else A
  else A

def lowerTo : ℕ → Finset (Fin n) → Finset (Fin n) → Finset (Fin n)
  | 0, A, _ => A
  | k + 1, A, B => lowerTo k (lowerStep A B) B

lemma lowerStep_mem {F : Finset (Finset (Fin n))} (hF : LeftClosed F)
    {A : Finset (Fin n)} (hA : A ∈ F) (B : Finset (Fin n)) : lowerStep A B ∈ F := by
  unfold lowerStep
  split
  next ha =>
    split
    next hb =>
      dsimp only
      split
      next hij =>
        exact hF _ _ hij A hA (mem_sdiff.mp (max'_mem _ ha)).1
          (mem_sdiff.mp (max'_mem _ hb)).2
      next => exact hA
    next => exact hA
  next => exact hA

lemma lowerTo_mem {F : Finset (Finset (Fin n))} (hF : LeftClosed F)
    (k : ℕ) {A : Finset (Fin n)} (hA : A ∈ F) (B : Finset (Fin n)) :
    lowerTo k A B ∈ F := by
  induction k generalizing A with
  | zero => exact hA
  | succ k ih => exact ih (lowerStep_mem hF hA B)

/-- The ten small sets used in the six-branch classification, numbered from zero. -/
def testSet (n : ℕ) [NeZero n] : Fin 10 → Finset (Fin n)
  | 0 => {0, 2, 3, 4} -- 1345
  | 1 => {0, 1, 4, 5} -- 1256
  | 2 => {0, 1, 2, 6} -- 1237
  | 3 => {0, 1, 5, 6} -- 1267
  | 4 => {0, 2, 3, 6} -- 1347
  | 5 => {0, 3, 4, 5} -- 1456
  | 6 => {0, 2, 3, 5} -- 1346
  | 7 => {0, 1, 4, 6} -- 1257
  | 8 => {0, 2, 4, 5} -- 1356
  | 9 => {0, 1, 3, 6} -- 1247

def forbiddenIndices : Fin 6 → Finset (Fin 10)
  | 0 => {0}
  | 1 => {1}
  | 2 => {2}
  | 3 => {3, 6}
  | 4 => {7, 4, 8}
  | 5 => {9, 5}

lemma six_cases {α : Type*} [DecidableEq α] (F : Finset (Finset α))
    (T : Fin 10 → Finset α) (hF : TwoIntersecting F)
    (h03 : (T 0 ∩ T 3).card = 1) (h14 : (T 1 ∩ T 4).card = 1)
    (h25 : (T 2 ∩ T 5).card = 1) (h67 : (T 6 ∩ T 7).card = 1)
    (h89 : (T 8 ∩ T 9).card = 1) :
    ∃ j : Fin 6, ∀ i ∈ forbiddenIndices j, T i ∉ F := by
  have incompat {i j : Fin 10} (h : (T i ∩ T j).card = 1) (hi : T i ∈ F) :
      T j ∉ F := by
    intro hj
    have := hF _ hi _ hj
    omega
  by_cases h0 : T 0 ∈ F
  · by_cases h1 : T 1 ∈ F
    · by_cases h2 : T 2 ∈ F
      · have h3 := incompat h03 h0
        have h4 := incompat h14 h1
        have h5 := incompat h25 h2
        by_cases h6 : T 6 ∈ F
        · have h7 := incompat h67 h6
          by_cases h8 : T 8 ∈ F
          · have h9 := incompat h89 h8
            exact ⟨5, by simpa [forbiddenIndices] using And.intro h9 h5⟩
          · exact ⟨4, by simpa [forbiddenIndices] using And.intro h7 (And.intro h4 h8)⟩
        · exact ⟨3, by simpa [forbiddenIndices] using And.intro h3 h6⟩
      · exact ⟨2, by simpa [forbiddenIndices] using h2⟩
    · exact ⟨1, by simpa [forbiddenIndices] using h1⟩
  · exact ⟨0, by simpa [forbiddenIndices] using h0⟩

/-- A finite container described by absence of the listed lower sets. -/
def certificateContainer (n : ℕ) [NeZero n] (j : Fin 6) : Finset (Finset (Fin n)) :=
  ((univ : Finset (Fin n)).powersetCard 4).filter fun A =>
    ∀ i ∈ forbiddenIndices j, lowerTo 4 A (testSet n i) ≠ testSet n i

lemma subset_certificateContainer [NeZero n] {F : Finset (Finset (Fin n))}
    (hu : Uniform 4 F) (hc : LeftClosed F) {j : Fin 6}
    (hj : ∀ i ∈ forbiddenIndices j, testSet n i ∉ F) :
    F ⊆ certificateContainer n j := by
  intro A hA
  apply mem_filter.mpr
  refine ⟨mem_powersetCard.mpr ⟨subset_univ _, hu A hA⟩, ?_⟩
  intro i hi heq
  apply hj i hi
  exact heq ▸ lowerTo_mem hc 4 hA (testSet n i)

lemma finite_shifted_bound [NeZero n] (b : ℕ)
    (h03 : (testSet n 0 ∩ testSet n 3).card = 1)
    (h14 : (testSet n 1 ∩ testSet n 4).card = 1)
    (h25 : (testSet n 2 ∩ testSet n 5).card = 1)
    (h67 : (testSet n 6 ∩ testSet n 7).card = 1)
    (h89 : (testSet n 8 ∩ testSet n 9).card = 1)
    (hb : ∀ j : Fin 6, (certificateContainer n j).card ≤ b)
    {F : Finset (Finset (Fin n))} (hu : Uniform 4 F)
    (hi : TwoIntersecting F) (hc : LeftClosed F) : F.card ≤ b := by
  obtain ⟨j, hj⟩ := six_cases F (testSet n) hi h03 h14 h25 h67 h89
  exact (card_le_card (subset_certificateContainer hu hc hj)).trans (hb j)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem shifted_seven {F : Finset (Finset (Fin 7))}
    (hu : Uniform 4 F) (hi : TwoIntersecting F) (hc : LeftClosed F) : F.card ≤ 15 := by
  exact finite_shifted_bound 15 (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) hu hi hc

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem shifted_eight {F : Finset (Finset (Fin 8))}
    (hu : Uniform 4 F) (hi : TwoIntersecting F) (hc : LeftClosed F) : F.card ≤ 17 := by
  exact finite_shifted_bound 17 (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) hu hi hc

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem shifted_nine {F : Finset (Finset (Fin 9))}
    (hu : Uniform 4 F) (hi : TwoIntersecting F) (hc : LeftClosed F) : F.card ≤ 21 := by
  exact finite_shifted_bound 21 (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) hu hi hc

end JSP572Four
