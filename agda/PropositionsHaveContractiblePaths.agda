{-# OPTIONS --without-K #-}

module PropositionsHaveContractiblePaths where

--------------------------------------------------------------------------------
-- Auxiliary definitions and lemmas
--------------------------------------------------------------------------------

-- Dependent pair
record Σ {A : Set} (P : A → Set) : Set where
  constructor _,_
  field
    pr₁ : A
    pr₂ : P pr₁

-- Identity
data Id {A : Set} : A → A → Set where
  refl : (a : A) → Id a a

sym : {A : Set} {a b : A} → Id a b → Id b a
sym (refl a) = refl a

trans : {A : Set} {a b : A} → Id a b → {c : A} → Id b c → Id a c
trans (refl a) id-b-c = id-b-c

-- Paths
infixl 20 _∙_
_∙_ : {A : Set} {a b c : A} → Id b c → Id a b → Id a c
refl a ∙ refl .a = refl a

infix 30 _⁻¹
_⁻¹ : {A : Set} {a b : A} → Id a b → Id b a
refl a ⁻¹ = refl a

id-left-inv : {A : Set} {a b : A} (p : Id a b)
            → Id (p ∙ p ⁻¹) (refl b)
id-left-inv (refl a) = refl (refl a)

transport : {A : Set} {a b : A} → Id a b → {B : A → Set} → B a → B b
transport (refl a) ba = ba

-- Propositions, contractible types and sets
is-prop : Set → Set
is-prop A = (a b : A) → Id a b

is-contr : Set → Set
is-contr A = Σ {A} (λ a → (b : A) → Id a b)

is-set : Set → Set
is-set A = {a b : A} (p q : Id a b) → Id p q

--------------------------------------------------------------------------------
-- Proof
--------------------------------------------------------------------------------

-- Lemma: every mere proposition is a set.
prop-is-set : {A : Set} → is-prop A → is-set A
prop-is-set {A} A-is-prop {a} = λ p q → trans (sym (h p)) (h q)
  where
    g : (b : A) → Id a b
    g = A-is-prop a

    h : {b c : A} (p : Id b c) → Id (g c ∙ (g b) ⁻¹) p
    h (refl b) = id-left-inv (g b)

-- Proof: If the paths between any two elements of A are contractible, then A is
-- a proposition.
proof₁ : {A : Set}
       → ((a b : A) → is-contr (Id a b))
       → ((a b : A) → Id a b)
proof₁ A-paths-are-contr a b = Σ.pr₁ (A-paths-are-contr a b)

-- Proof: If A is a proposition, then the paths between any two elements of A
-- are contractible.
proof₂ : {A : Set}
       → ((a b : A) → Id a b)
       → ((a b : A) → is-contr (Id a b))
proof₂ {A} A-is-prop a b = p , prop-is-set A-is-prop p
  where
    p : Id a b
    p = A-is-prop a b
