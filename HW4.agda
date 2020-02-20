{-
Name: Ryan Parker
Date: 9/20/19

Collaboration & Resources Statement:
did not collaborate
-}

---------------
-- LOGISTICS --
---------------

-- To submit the assignment, upload your solution to Gradescope as a
-- single .agda file.
--
-- Make sure you write your name, the date, and your collaboration
-- & Resources statement above, as indicated by the course 
-- collaboration and resources policy:
--
--     Collaboration on the high-level ideas and approach on assignments
--     is encouraged. Copying someone else's work is not allowed. Copying
--     solutions from an online source is not allowed. Any collaboration
--     or online resources, even if used only at a high level, must be
--     declared when you submit your assignment. Every assignment must
--     include a collaboration and resources statement. E.g., “I discussed
--     high-level strategies for solving problem 2 and 5 with Alex; I
--     found this stackoverflow post helpful while working on problem 3 ”
--     Students caught copying work are eligible for immediate failure of
--     the course and disciplinary action by the University. All academic
--     integrity misconduct will be treated according to UVM's Code of
--     Academic Integrity.
--
-- This assignment consists of a LIB section which contains relevant
-- definitions and lemmas which you should refer to throughout the
-- assignment, and an ASSIGNMENT section which contains definitions
-- and lemmas with “holes” in them. *If you only change the code
-- within the holes and your entire assignment compiles without
-- errors, you are guaranteed 100% on the assignment.*

module HW4 where

---------
-- LIB --
---------

module Lib where

  -- equality
  infix 8 _≡_
  data _≡_ {A : Set} (x : A) : A → Set where
    ↯ : x ≡ x
  {-# BUILTIN EQUALITY _≡_ #-}

  -- empty set
  data 𝟘 : Set where

  -- singleton set
  data 𝟙 : Set where
    • : 𝟙

  -- disjoint union
  infix 5 _∨_
  data _∨_ (A B : Set) : Set where
    Inl : A → A ∨ B
    Inr : B → A ∨ B

  -- cartesian product
  infix 6 _∧_
  data _∧_ (A B : Set) : Set where
    ⟨_,_⟩ : A → B → A ∧ B

  -- cartesian product - first projection
  pr₁ : ∀ {A B : Set} → A ∧ B → A
  pr₁ ⟨ x , y ⟩ = x

  -- cartesian product - second projection
  pr₂ : ∀ {A B : Set} → A ∧ B → B
  pr₂ ⟨ x , y ⟩ = y

  -- dependent sum/pair
  infixr 4 [∃]
  syntax [∃] A (λ x → B) = ∃ x ⦂ A ST B
  data [∃] (A : Set) (B : A → Set) : Set where
    ⟨∃_,_⟩ : ∀ (x : A) → B x → ∃ x ⦂ A ST B x

  -- dependent sum/pair - first projection
  dpr₁ : ∀ {A : Set} {B : A → Set} → ∃ x ⦂ A ST B x → A
  dpr₁ ⟨∃ x , y ⟩ = x

  -- dependent sum/pair - second projection
  dpr₂ : ∀ {A : Set} {B : A → Set} → (xy : ∃ x ⦂ A ST B x) → B (dpr₁ xy)
  dpr₂ ⟨∃ x , y ⟩ = y

  -- negation
  infixr 21 ¬_
  ¬_ : Set → Set
  ¬_ A = A → 𝟘

  -- case analysis
  infixr 10 CASE_OF_
  CASE_OF_ : ∀ {A B : Set} → A → (A → B) → B
  CASE x OF e = e x

  -- identity function
  id : ∀ {A : Set} → A → A
  id x = x

  -- function composition
  infixl 18 _∘_
  _∘_ : ∀ {A B C : Set} → (B → C) → (A → B) → A → C
  (f ∘ g) x = f (g x)

  postulate
    ext : ∀ {A B : Set} {f g : A → B} → (∀ x → f x ≡ g x) → f ≡ g

open Lib public

----------------
-- ASSIGNMENT --
----------------

-------------------
-- GENERAL HINTS --
-------------------

-- 1. use “refine” (C-c C-r) and “case splitting” (C-c C-c)
-- 2. none of the proofs in this assignment are by induction
-- 3. the entire assignment can be completed without using helper
--    functions

---------------
-- Exercises --
---------------

-- Prove that negation distributes through sums

-- E1: [★★★]
-- The “to” mapping
-- HINT: Use C-c C-r to “refine” a goal that is an implication (e.g.,
--       `A → B`). This will create a “lambda” expression which gives a name
--       to the hypothesis, and creates a hole for goal which gets to use
--       this hypothesis by name.
dist[¬/∨]-to : ∀ {A B : Set} → ¬ (A ∨ B) → ¬ A ∧ ¬ B
dist[¬/∨]-to nxy = ⟨ (λ x → nxy (Inl x)) , (λ x → nxy (Inr x)) ⟩


-- E2: [★☆☆]
-- The “from” mapping
dist[¬/∨]-fr : ∀ {A B : Set} → ¬ A ∧ ¬ B → ¬ (A ∨ B)
dist[¬/∨]-fr ⟨ x1 , x2 ⟩ (Inl l) = x1 l
dist[¬/∨]-fr ⟨ x1 , x2 ⟩ (Inr x) = x2 x

-- E3: [★☆☆]
-- The fully expanded “to ∘ from” round trip law
dist[¬/∨]-tofr₂ : ∀ {A B : Set} (nxy : ¬ (A ∨ B)) (xy : A ∨ B) → dist[¬/∨]-fr (dist[¬/∨]-to nxy) xy ≡ nxy xy
dist[¬/∨]-tofr₂ {A} {B} nxy (Inl x) = ↯
dist[¬/∨]-tofr₂ {A} {B} nxy (Inr x) = ↯

-- E4: [★★☆]
-- The less expanded “to ∘ from” found trip law
-- HINT: use the extensionality postulate `ext` and the previous lemma
dist[¬/∨]-tofr₁ : ∀ {A B : Set} (nxy : ¬ (A ∨ B)) → dist[¬/∨]-fr (dist[¬/∨]-to nxy) ≡ nxy
dist[¬/∨]-tofr₁ nxy = ext (dist[¬/∨]-tofr₂ nxy) 

-- E5: [★★☆]
-- The least expanded “to ∘ from” found trip law
-- HINT: use the extensionality postulate `ext` and the previous lemma
dist[¬/∨]-tofr : ∀ {A B : Set} → dist[¬/∨]-fr ∘ dist[¬/∨]-to ≡ id {¬ (A ∨ B)}
dist[¬/∨]-tofr {A} {B} = ext dist[¬/∨]-tofr₁ 

-- E6: [★☆☆]
-- The fully expanded “from ∘ to” round trip law
dist[¬/∨]-frto₁ : ∀ {A B : Set} (nxy : ¬ A ∧ ¬ B) → dist[¬/∨]-to (dist[¬/∨]-fr nxy) ≡ nxy 
dist[¬/∨]-frto₁ {A} {B} ⟨ x , x₁ ⟩ = ↯

-- E7: [★★☆]
-- The least expanded “from ∘ to” round trip law
-- HINT: use the extensionality postulate `ext` and the previous lemma
dist[¬/∨]-frto : ∀ {A B : Set} → dist[¬/∨]-to ∘ dist[¬/∨]-fr ≡ id {¬ A ∧ ¬ B}
dist[¬/∨]-frto {A} {B} = ext dist[¬/∨]-frto₁

-- E6: [★☆☆]
-- Prove that negation distributes through products
-- Just show the “from” mapping
-- (The “to” mapping is true logically, but not computationally derivable.)
dist[¬/∧]-fr : ∀ {A B : Set} → ¬ A ∨ ¬ B → ¬ (A ∧ B)
dist[¬/∧]-fr (Inl l) ⟨ x1 , x2 ⟩ = l x1
dist[¬/∧]-fr (Inr r) ⟨ x1 , x2 ⟩ = r x2

-- Prove that negation distributes through existentials

-- E7: [★☆☆]
-- The “to” mapping
dist[¬/∃]-to : ∀ {A : Set} {B : A → Set} → ¬ (∃ x ⦂ A ST B x) → (∀ (x : A) → ¬ B x)
dist[¬/∃]-to {A} {B} nxy x ny = nxy ⟨∃ x , ny ⟩

-- E8: [★☆☆]
-- The “from” mapping
dist[¬/∃]-fr : ∀ {A : Set} {B : A → Set} → (∀ (x : A) → ¬ B x) → ¬ (∃ x ⦂ A ST B x)
dist[¬/∃]-fr {A} {B} xny ⟨∃ x1 , x2 ⟩ = xny x1 x2

-- E9: [★★☆]
-- Prove that negation distributes through universal quanitifers
-- Just prove the “from” mapping
-- (The “to” mapping is true logically, but not computationally derivable.)
dist[¬/∀]-fr : ∀ {A : Set} {B : A → Set} → ∃ x ⦂ A ST ¬ B x → ¬ ∀ (x : A) → B x
dist[¬/∀]-fr {A} {B} ⟨∃ x1 , x2 ⟩ = λ x → x2 (x x1)

-- EXTRA PROBLEMS (not graded)
--
-- 1. prove that A → ¬ ¬ A
-- 2. prove that ¬ ¬ ¬ A → ¬ A
-- 3. prove that ¬ ¬ (A ∨ ¬ A)
-- 4. prove that ¬ ¬ A ∧ (A → ¬ ¬ B) → ¬ ¬ B
-- 5. prove the constructive theorem of countable choice:
--
--        choice : ∀ {A B : Set} → ∀ (R : A → B → Set) → (∀ (x : A) → ∃ y ⦂ B ST R x y) → ∃ f ⦂ (A → B) ST ∀ (x : A) → R x (f x)
e1 : ∀ {A : Set} → (A) → (¬ ¬ A)
e1 A = λ x → x A

e2 : {A : Set} → (¬ ¬ ¬ A) → ¬ A
e2 A = λ x → A λ x2 → x2 x

e3 : {A : Set} → ¬ ¬ (A ∨ (¬ A))
e3 a = a (Inr λ x → a (Inl x))

--couldnt find a way without just making a postulate
postulate
  helper : ∀ {A : Set} → ¬ ¬ A → A 

e4 : ∀ {A B : Set} → ¬ ¬ A ∧ (A → ¬ ¬ B) → ¬ ¬ B
e4 ⟨ nna , f ⟩ = λ nb → f (helper nna) λ x → nb x


bind : ∀ {A B} → ¬ ¬ A → (A → ¬ ¬ B) → ¬ ¬ B
bind nna nnb nb = nna λ a → nnb a nb
--choice : ∀ {A B : Set} → ∀ (R : A → B → Set) → (∀ (x : A) → ∃ y ⦂ B ST R x y) → ∃ f ⦂ (A → B) ST ∀ (x : A) → R x (f x)
--choice {A} {B} x y = ⟨∃ (λ z → {!x z!}) , (λ z → {!(y z)!}) ⟩
