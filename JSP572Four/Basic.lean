import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Card

/-!
Definitions for the numerical, four-uniform part of Keevash--Mubayi--Wilson,
Set Systems with No Singleton Intersection (2006), Theorem 1.1.
The complete numerical theorem is exported by JSP572Four.Main.
No award or priority claim is made here.
-/

namespace JSP572Four

open Finset

variable {α : Type*} [DecidableEq α]

def Uniform (k : ℕ) (F : Finset (Finset α)) : Prop :=
  ∀ A ∈ F, A.card = k

def NoSingleton (F : Finset (Finset α)) : Prop :=
  ∀ A ∈ F, ∀ B ∈ F, (A ∩ B).card ≠ 1

def TwoIntersecting (F : Finset (Finset α)) : Prop :=
  ∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card

def Supported (X : Finset α) (F : Finset (Finset α)) : Prop :=
  ∀ A ∈ F, A ⊆ X

def sharpBound (n : ℕ) : ℕ :=
  if n ≤ 6 then n.choose 4
  else if n = 7 then 15
  else if n = 8 then 17
  else (n - 2).choose 2

end JSP572Four
