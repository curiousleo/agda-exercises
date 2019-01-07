{-# OPTIONS --without-K #-}

module MGS2018L1 where

-- Lecture 1
------------

-- Definitions
data ⊥ : Set where

¬_ : Set → Set
¬ A = A → ⊥

data ⊤ : Set where
  tt : ⊤

data Σ {A : Set} (P : A → Set) : Set where
  _,,_ : (a : A) (pa : P a) → Σ P

-- Exercise: Define elimination rule for ⊥
rec-⊥ : {C : Set} → ⊥ → C
rec-⊥ ()

-- Exercise: Define elimination rule for ⊤
rec-⊤ : {C : Set} → C → ⊤ → C
rec-⊤ c tt = c

-- Exercise: Define the type of boolean values, with two elements
data Bool : Set where
  true : Bool
  false : Bool

-- Exercise: Define elimination rule for Bool
rec-Bool : {C : Bool → Set} → C true → C false → (b : Bool) → C b
rec-Bool c-true c-false true  = c-true
rec-Bool c-true c-false false = c-false

-- Exercise: Define a function of type ⊥ → Bool
⊥-to-Bool-pat : ⊥ → Bool
⊥-to-Bool-pat ()

⊥-to-Bool-rec : ⊥ → Bool
⊥-to-Bool-rec = rec-⊥

-- Definitions
data Nat : Set where
  zero : Nat
  suc : Nat → Nat

rec-Nat : {C : Set} → C → (C → C) → Nat → C
rec-Nat c₀ cₛ zero    = c₀
rec-Nat c₀ cₛ (suc n) = cₛ (rec-Nat c₀ cₛ n)

-- Exercise: Define a function isZero? : Nat → Bool
isZero? : Nat → Bool
isZero? zero    = true
isZero? (suc n) = false

isZero?-rec : Nat → Bool
isZero?-rec = rec-Nat true (λ _ → false)

-- Definitions
data _×_ (A B : Set) : Set where
  _,_ : A → B → A × B

×-rec : {A B C : Set} → (A → B → C) → A × B → C
×-rec f (a , b) = f a b

-- Exercise: Define fst and snd
fst : {A B : Set} → A × B → A
fst (a , _) = a

fst-rec : {A B : Set} → A × B → A
fst-rec = ×-rec (λ a _ → a)

snd : {A B : Set} → A × B → B
snd (_ , b) = b

snd-rec : {A B : Set} → A × B → B
snd-rec = ×-rec (λ _ b → b)

-- Exercise: Define swap
swap : {A B : Set} → A × B → B × A
swap (a , b) = (b , a)

swap-fst-snd : {A B : Set} → A × B → B × A
swap-fst-snd p = snd p , fst p

swap-rec : {A B : Set} → A × B → B × A
swap-rec = ×-rec (λ a b → (b , a))

-- Exercise: Define assoc
assoc : {A B C : Set} → (A × B) × C → A × (B × C)
assoc ((a , b) , c) = a , (b , c)

assoc-fst-snd : {A B C : Set} → (A × B) × C → A × (B × C)
assoc-fst-snd abc = fst (fst abc) , (snd (fst abc) , snd abc)

assoc-rec : {A B C : Set} → (A × B) × C → A × (B × C)
assoc-rec = ×-rec (λ ab c → fst ab , (snd ab , c))

-- Definitions
data Id {A : Set} : A → A → Set where
  refl : (a : A) → Id a a

-- Exercise: Write term of type Id (snd (tt , false) , false)
id-term : Id (snd (tt , false)) false
id-term = refl false

-- Definition
sym : {A : Set} {a b : A} → Id a b → Id b a
sym (refl a) = refl a

-- Exercise: Define trans
trans : {A : Set} {a b : A} → Id a b → {c : A} → Id b c → Id a c
trans (refl a) id-b-c = id-b-c

-- Exercise: Define transport
transport : {A : Set} {a b : A} → Id a b → {B : A → Set} → B a → B b
transport (refl a) ba = ba

-- Exercise: swap is involutive
swap-inv : {A B : Set} (t : A × B) → Id (swap (swap t)) t
swap-inv (a , b) = refl (a , b)

-- Why this works: swap (swap (a , b)) ≡ (a , b) (definitionally equal)
-- whereas swap (swap t) ≢ t

-- Definition
data _+_ (A B : Set) : Set where
  inl : A → A + B
  inr : B → A + B

-- Exercise: Write down eliminator
rec-+ : {A B C : Set} → (A → C) → (B → C) → A + B → C
rec-+ f g (inl a) = f a
rec-+ f g (inr b) = g b

-- The pattern matching principle is to give separate terms for the two cases
-- (inl a) and (inr b)

-- Exercise: Construct a term of type A → ¬ ¬ A
negate-twice : {A : Set} → A → ¬ ¬ A -- ¬ ¬ A ≡ (A → ⊥) → ⊥
negate-twice a ¬a = rec-⊥ (¬a a) -- or just (¬a a)

-- Exercise: Try to construct a term of type ¬ ¬ A → A
-- double-negation : {A : Set} → ¬ ¬ A → A
-- double-negation = ? -- won't work

-- Exercise: Construct a term of type ¬ Id true false
¬-id-true-false : ¬ Id true false
¬-id-true-false ()

¬-id-true-false-transport : ¬ Id true false
¬-id-true-false-transport id-true-false = transport id-true-false {B} tt
  where
    B : Bool → Set
    B true  = ⊤
    B false = ⊥

-- Exercise: Define addition of natural numbers using pattern matching and eliminator
add : Nat → Nat → Nat
add zero    n = n
add (suc m) n = suc (add m n)

add-rec : Nat → Nat → Nat
add-rec m n = rec-Nat n suc m

-- Extra: Show that add and add-rec are pointwise equal
add-equiv : (m n : Nat) → Id (add m n) (add-rec m n)
add-equiv zero    n = refl n
add-equiv (suc m) n = id-suc
  where
    B : Nat → Nat → Set
    B m n = Id (suc m) (suc n)

    id-suc : Id (suc (add m n)) (suc (add-rec m n))
    id-suc = transport (add-equiv m n) {B (add m n)} (refl _)

-- Exercise: Prove that 2 + 2 equals 4
2+2=4 : Id (add (suc (suc zero)) (suc (suc zero))) (suc (suc (suc (suc zero))))
2+2=4 = refl _
-- This works because add (suc (suc zero)) (suc (suc zero) ≡ (suc (suc (suc (suc zero))))
-- i.e. the two are definitionally equivalent, the former is reduced to the latter

-- Exercise: Define maps between A × (B + C) and A × B + A × C and show that they are
-- pointwise inverses
unpack : {A B C : Set} → A × (B + C) → (A × B) + (A × C)
unpack (a , inl b) = inl (a , b)
unpack (a , inr c) = inr (a , c)

pack : {A B C : Set} → (A × B) + (A × C) → A × (B + C)
pack (inl (a , b)) = a , inl b
pack (inr (a , c)) = a , inr c

unpack∘pack-id : {A B C : Set} (x : (A × B) + (A × C)) → Id (unpack (pack x)) x
unpack∘pack-id (inl (a , b)) = refl (inl (a , b))
unpack∘pack-id (inr (a , c)) = refl (inr (a , c))

pack∘unpack-id : {A B C : Set} (x : A × (B + C)) → Id (pack (unpack x)) x
pack∘unpack-id (a , inl b) = refl (a , inl b)
pack∘unpack-id (a , inr c) = refl (a , inr c)

-- Exercise: For A, B and P : A → Set, give maps between Σ (x : A) (B × P x) and B × Σ (x : A) (P x); show that they are pointwise inverses
unpack' : {A B : Set} {P : A → Set}
        → Σ (λ a → B × (P a))
        → B × Σ (λ a → P a)
unpack' (a ,, (b , pa)) = b , (a ,, pa)

pack' : {A B : Set} {P : A → Set}
      → B × Σ (λ a → P a)
      → Σ (λ a → B × (P a))
pack' (b , (a ,, pa)) = a ,, (b , pa)

unpack'∘pack'-id : {A B : Set} {P : A → Set}
                 → (x : B × Σ (λ a → P a))
                 → Id (unpack' (pack' x)) x
unpack'∘pack'-id (b , (a ,, pa)) = refl (b , (a ,, pa))

pack'∘unpack'-id : {A B : Set} {P : A → Set}
                 → (x : Σ (λ a → B × (P a)))
                 → Id (pack' (unpack' x)) x
pack'∘unpack'-id (a ,, (b , pa)) = refl (a ,, (b , pa))
