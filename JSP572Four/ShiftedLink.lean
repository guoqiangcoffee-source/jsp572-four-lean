import JSP572Four.Compression

namespace JSP572Four

open Finset

variable {n : ℕ}

def liftMax (A : Finset (Fin n)) : Finset (Fin (n + 1)) := A.image Fin.castSucc

def dropMax (A : Finset (Fin (n + 1))) : Finset (Fin n) :=
  univ.filter fun x => x.castSucc ∈ A

def deleteMax (F : Finset (Finset (Fin (n + 1)))) : Finset (Finset (Fin n)) :=
  univ.filter fun A => liftMax A ∈ F

def linkMax (F : Finset (Finset (Fin (n + 1)))) : Finset (Finset (Fin n)) :=
  univ.filter fun A => insert (Fin.last n) (liftMax A) ∈ F

@[simp] lemma mem_liftMax (A : Finset (Fin n)) (x : Fin n) :
    x.castSucc ∈ liftMax A ↔ x ∈ A := by simp [liftMax]

@[simp] lemma last_notMem_liftMax (A : Finset (Fin n)) :
    Fin.last n ∉ liftMax A := by simp [liftMax]

@[simp] lemma mem_dropMax (A : Finset (Fin (n + 1))) (x : Fin n) :
    x ∈ dropMax A ↔ x.castSucc ∈ A := by simp [dropMax]

@[simp] lemma mem_deleteMax {F : Finset (Finset (Fin (n + 1)))}
    {A : Finset (Fin n)} : A ∈ deleteMax F ↔ liftMax A ∈ F := by simp [deleteMax]

@[simp] lemma mem_linkMax {F : Finset (Finset (Fin (n + 1)))}
    {A : Finset (Fin n)} :
    A ∈ linkMax F ↔ insert (Fin.last n) (liftMax A) ∈ F := by simp [linkMax]

@[simp] lemma card_liftMax (A : Finset (Fin n)) : (liftMax A).card = A.card :=
  card_image_of_injective _ (Fin.castSucc_injective n)

lemma liftMax_injective : Function.Injective (@liftMax n) := by
  intro A B h
  ext x
  have := congrArg (fun S => x.castSucc ∈ S) h
  simpa using this

lemma insert_last_liftMax_injective :
    Function.Injective (fun A : Finset (Fin n) => insert (Fin.last n) (liftMax A)) := by
  intro A B h
  ext x
  have := congrArg (fun S => x.castSucc ∈ S) h
  simpa using this

lemma liftMax_dropMax (A : Finset (Fin (n + 1))) :
    liftMax (dropMax A) = A.erase (Fin.last n) := by
  ext x
  refine Fin.lastCases ?_ (fun i => ?_) x
  · simp
  · simp

lemma liftMax_inter (A B : Finset (Fin n)) :
    liftMax (A ∩ B) = liftMax A ∩ liftMax B :=
  image_inter _ _ (Fin.castSucc_injective n)

lemma liftMax_insert (A : Finset (Fin n)) (i : Fin n) :
    liftMax (insert i A) = insert i.castSucc (liftMax A) := by simp [liftMax]

lemma liftMax_erase (A : Finset (Fin n)) (i : Fin n) :
    liftMax (A.erase i) = (liftMax A).erase i.castSucc :=
  image_erase (Fin.castSucc_injective n) _ _

lemma card_insert_last_liftMax (A : Finset (Fin n)) :
    (insert (Fin.last n) (liftMax A)).card = A.card + 1 := by simp

lemma insert_last_liftMax_inter (A B : Finset (Fin n)) :
    insert (Fin.last n) (liftMax A) ∩ insert (Fin.last n) (liftMax B) =
      insert (Fin.last n) (liftMax (A ∩ B)) := by
  ext x
  refine Fin.lastCases ?_ (fun i => ?_) x
  · simp
  · simp

lemma image_deleteMax (F : Finset (Finset (Fin (n + 1)))) :
    (deleteMax F).image liftMax = F.filter (fun A => Fin.last n ∉ A) := by
  ext A
  constructor
  · rintro h
    obtain ⟨B, hB, rfl⟩ := mem_image.mp h
    exact mem_filter.mpr ⟨mem_deleteMax.mp hB, last_notMem_liftMax B⟩
  · intro h
    rcases mem_filter.mp h with ⟨hF, hn⟩
    have heq : liftMax (dropMax A) = A := by rw [liftMax_dropMax, erase_eq_of_notMem hn]
    exact mem_image.mpr ⟨dropMax A, mem_deleteMax.mpr (heq.symm ▸ hF), heq⟩

lemma image_linkMax (F : Finset (Finset (Fin (n + 1)))) :
    (linkMax F).image (fun A => insert (Fin.last n) (liftMax A)) =
      F.filter (fun A => Fin.last n ∈ A) := by
  ext A
  constructor
  · rintro h
    obtain ⟨B, hB, rfl⟩ := mem_image.mp h
    exact mem_filter.mpr ⟨mem_linkMax.mp hB, mem_insert_self _ _⟩
  · intro h
    rcases mem_filter.mp h with ⟨hF, hn⟩
    have heq : insert (Fin.last n) (liftMax (dropMax A)) = A := by
      rw [liftMax_dropMax, insert_erase hn]
    exact mem_image.mpr ⟨dropMax A, mem_linkMax.mpr (heq.symm ▸ hF), heq⟩

lemma card_deleteMax_add_card_linkMax (F : Finset (Finset (Fin (n + 1)))) :
    (deleteMax F).card + (linkMax F).card = F.card := by
  rw [← card_image_of_injective (deleteMax F) liftMax_injective,
    ← card_image_of_injective (linkMax F) insert_last_liftMax_injective,
    image_deleteMax, image_linkMax, add_comm]
  exact card_filter_add_card_filter_not _

lemma uniform_deleteMax {k : ℕ} {F : Finset (Finset (Fin (n + 1)))}
    (hF : Uniform k F) : Uniform k (deleteMax F) := by
  intro A hA
  simpa using hF _ (mem_deleteMax.mp hA)

lemma uniform_linkMax {k : ℕ} {F : Finset (Finset (Fin (n + 1)))}
    (hF : Uniform (k + 1) F) : Uniform k (linkMax F) := by
  intro A hA
  have h := hF _ (mem_linkMax.mp hA)
  simpa using h

lemma twoIntersecting_deleteMax {F : Finset (Finset (Fin (n + 1)))}
    (hF : TwoIntersecting F) : TwoIntersecting (deleteMax F) := by
  intro A hA B hB
  have h := hF _ (mem_deleteMax.mp hA) _ (mem_deleteMax.mp hB)
  rwa [← liftMax_inter, card_liftMax] at h

lemma shifted_deleteMax {F : Finset (Finset (Fin (n + 1)))}
    (hF : Shifted F) : Shifted (deleteMax F) := by
  intro i j hij A hA hj hi
  apply mem_deleteMax.mpr
  rw [liftMax_insert, liftMax_erase]
  apply hF i.castSucc j.castSucc hij (liftMax A) (mem_deleteMax.mp hA)
  · simpa using hj
  · simpa using hi

lemma shifted_linkMax {F : Finset (Finset (Fin (n + 1)))}
    (hF : Shifted F) : Shifted (linkMax F) := by
  intro i j hij A hA hj hi
  apply mem_linkMax.mpr
  have h := hF i.castSucc j.castSucc hij _ (mem_linkMax.mp hA)
    (by simp [hj]) (by simp [hi])
  convert h using 1
  ext x
  refine Fin.lastCases ?_ (fun a => ?_) x
  · simp [Ne.symm (Fin.castSucc_ne_last i), Ne.symm (Fin.castSucc_ne_last j)]
  · simp [liftMax_insert, liftMax_erase]

/-- Deleting the largest point from a shifted four-uniform family preserves
two-intersection once there are at least seven points. -/
lemma twoIntersecting_linkMax {F : Finset (Finset (Fin (n + 1)))}
    (hn : 6 ≤ n) (hu : Uniform 4 F) (ht : TwoIntersecting F) (hs : Shifted F) :
    TwoIntersecting (linkMax F) := by
  intro A hA B hB
  have huL : Uniform 3 (linkMax F) := uniform_linkMax hu
  have ha := huL A hA
  have hb := huL B hB
  have hbase := ht _ (mem_linkMax.mp hA) _ (mem_linkMax.mp hB)
  rw [insert_last_liftMax_inter, card_insert_last_liftMax] at hbase
  by_contra hbad
  have hinter : (A ∩ B).card = 1 := by omega
  have hsum := card_union_add_card_inter A B
  have hout : ∃ i : Fin n, i ∉ A ∪ B := by
    by_contra! h
    have heq : A ∪ B = univ := eq_univ_iff_forall.mpr h
    rw [heq, card_univ, Fintype.card_fin] at hsum
    omega
  obtain ⟨i, hi⟩ := hout
  have hiA : i ∉ A := fun h => hi (mem_union_left _ h)
  have hiB : i ∉ B := fun h => hi (mem_union_right _ h)
  have hshift : insert i.castSucc (liftMax A) ∈ F := by
    have h := hs i.castSucc (Fin.last n) (Fin.castSucc_lt_last i)
      _ (mem_linkMax.mp hA) (mem_insert_self _ _) (by simp [hiA])
    simpa using h
  have hfinal := ht _ hshift _ (mem_linkMax.mp hB)
  have heq : insert i.castSucc (liftMax A) ∩ insert (Fin.last n) (liftMax B) =
      liftMax (A ∩ B) := by
    ext x
    refine Fin.lastCases ?_ (fun a => ?_) x
    · simp [Ne.symm (Fin.castSucc_ne_last i)]
    · simp only [mem_inter, mem_insert, Fin.castSucc_inj, Fin.castSucc_ne_last,
        false_or, mem_liftMax]
      constructor
      · rintro ⟨hai | haA, haB⟩
        · subst a
          exact False.elim (hiB haB)
        · exact ⟨haA, haB⟩
      · rintro ⟨haA, haB⟩
        exact ⟨Or.inr haA, haB⟩
  rw [heq, card_liftMax, hinter] at hfinal
  omega

end JSP572Four
