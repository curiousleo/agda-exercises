{-# OPTIONS --without-K #-}

module MGS2018L2 where

open import MGS2018L1

-- Lecture 2
------------

-- Exercise: Give f : A → B, construct a term of type (a b : A) → Id a b → Id (f a) (f b)
subst : {A B : Set} (a b : A) (f : A → B) → Id a b → Id (f a) (f b)
subst a .a f (refl .a) = refl (f a)

-- Extra: Laws satisfied by path concatenation
_∙_ : {A : Set} {a b c : A} → Id b c → Id a b → Id a c
refl a ∙ refl .a = refl a

infix 30 _⁻¹
_⁻¹ : {A : Set} {a b : A} → Id a b → Id b a
refl a ⁻¹ = refl a

id-assoc : {A : Set} {a b c d : A}
           (p : Id c d) (q : Id b c) (r : Id a b)
         → Id ((p ∙ q) ∙ r) (p ∙ (q ∙ r))
id-assoc (refl a) (refl .a) (refl .a) = refl (refl a)

id-right-unit : {A : Set} {a b : A}
                (p : Id a b)
              → Id (p ∙ refl a) p
id-right-unit (refl a) = refl (refl a)

id-left-unit : {A : Set} {a b : A}
               (p : Id a b)
             → Id (refl b ∙ p) p
id-left-unit (refl a) = refl (refl a)

id-right-inv : {A : Set} {a b : A}
               (p : Id a b)
             → Id (p ⁻¹ ∙ p) (refl a)
id-right-inv (refl a) = refl (refl a)

id-left-inv : {A : Set} {a b : A}
              (p : Id a b)
            → Id (p ∙ p ⁻¹) (refl b)
id-left-inv (refl a) = refl (refl a)

-- Definition
is-contr : Set → Set
is-contr A = Σ {A} (λ a → (b : A) → Id b a)

-- Extra: There is a path between any two points of a contractible type
any-path : {A : Set}
         → is-contr A
         → (a b : A) → Id a b
any-path (x ,, id-x) a b = (id-x b) ⁻¹ ∙ id-x a

-- Definition
is-equiv : {A B : Set} → (A → B) → Set
is-equiv {A} {B} f = (b : B) → is-contr (Σ λ a → Id (f a) b)

_≅_ : (A B : Set) → Set
A ≅ B = Σ λ f → is-equiv {A} {B} f


J : {A : Set}
  → (P : (a b : A) → Id a b → Set)
  → ((a : A) → P a a (refl a))
  → (a b : A) (p : Id a b) → P a b p
J P f _ _ (refl a) = f a

-- Exercise
Σ-pr₁ : {A : Set} {P : A → Set} → Σ {A} P → A
Σ-pr₁ (a ,, _) = a

Σ-pr₂ : {A : Set} {P : A → Set} → (s : Σ {A} P) → P (Σ-pr₁ s)
Σ-pr₂ (_ ,, pa) = pa

record Σ' {A : Set} (P : A → Set) : Set where
  constructor _,,'_
  field
    pr₁ : A
    pr₂ : P pr₁

is-contr' : Set → Set
is-contr' A = Σ' λ a → (b : A) → Id b a

is-equiv' : {A B : Set} → (A → B) → Set
is-equiv' {A} {B} f = (b : B) → is-contr' (Σ' λ a → Id (f a) b)

_≅'_ : (A B : Set) → Set
A ≅' B = Σ' {A → B} λ f → is-equiv' f

cone-contract : {A : Set} {a b : A} (id : Id a b)
              → Id (b ,,' id) (a ,,' refl a)
cone-contract (refl a) = refl (a ,,' refl a)

{- -- Wild experiments
from-inverses : {A B : Set} (f : A → B) (f⁻¹ : B → A)
              → ((a : A) → Id (f⁻¹ (f a)) a)
              → ((b : B) → Id (f (f⁻¹ b)) b)
              → A ≅' B
from-inverses {A} {B} f f⁻¹ left-inv right-inv = f ,,' f-is-equiv
  where
    id₁ : {a : A} {b : B} → Id (f a) b → Id (f⁻¹ b) a
    id₁ (refl ._) = left-inv _
    
    id₂ : {a : A} {b : B} (id-f⁻¹b-a : Id (f⁻¹ b) a) → Id (a ,,' id-f⁻¹b-a) (f⁻¹ b ,,' refl (f⁻¹ b))
    id₂ = cone-contract
    
    id₃ : {a : A} {b : B} (id-fa-b : Id (f a) b) → Id (b ,,' id-fa-b) (f a ,,' refl (f a))
    id₃ = cone-contract
    
    id₄ : {a : A} {b : B} (id-fa-b : Id (f a) b) → Id (a ,,' refl (f a)) (f⁻¹ (f a) ,,' right-inv (f a))
    id₄ = {!!}
    
--    id₄ : {a : A} {b : B} (id-fa-b : Id (f a) b) → Id (a ,,' id-fa-b) (f⁻¹ b ,,' refl (f a))
--    id₄ = cone-contract

    h : (b : B) (g : Σ' λ a → Id (f a) b) → Id g (f⁻¹ b ,,' right-inv b)
    h b (a ,,' id-fa-b) with id-fa-b
    h ._ (a ,,' id-fa-b) | refl ._ = {!!}

    f-is-equiv' : is-equiv' f
    f-is-equiv' b = (f⁻¹ b ,,' right-inv b) ,,' h b
--    f-is-equiv' b with f (f⁻¹ b) | right-inv b
--    ...              | .b        | refl .b = (f⁻¹ b ,,' right-inv b) ,,' h
      where
--        h (a ,,' id-fa-b) with id₁ id-fa-b
--        h (._ ,,' id-fa-b) | refl ._ = {!!} -- refl (f⁻¹ b ,,' refl (f (f⁻¹ b)))
        -- with f⁻¹ (f a) | left-inv a
--        h (a ,,' id-fa-b) | .a | refl .a = {!id-fa-b!}
--        ...                  | .a        | refl .a = {!cone-contract {A} {f⁻¹ b} {a} (id₁ id-fa-b)!}

    f-is-equiv : is-equiv' f
    f-is-equiv b = (f⁻¹ b ,,' right-inv b) ,,' {!!}
      where
        h' : (g : Σ' λ a → Id (f a) b) → Id g (f⁻¹ b ,,' right-inv b)
        h' (a' ,,' id-fa'-b) = {!!}
--        h (a' ,,' id-fa'-b) = {!transport (id₁ id-fa'-b) {λ a → Id (a ,,' id-fa'-b) (f⁻¹ b ,,' right-inv b)}!}
--        h (a' ,,' id-fa'-b) = {!cone-contract {A} {f⁻¹ b} {a'} (id₁ id-fa'-b)!}
-}

equiv-inv' : {A B : Set} (f : A ≅' B) → B → A
equiv-inv' (_ ,,' f-is-equiv) b = Σ'.pr₁ (Σ'.pr₁ (f-is-equiv b))

1+1=2 : (⊤ + ⊤) ≅' Bool
1+1=2 = f ,,' f-is-equiv
  where
    f : ⊤ + ⊤ → Bool
    f (inl tt) = true
    f (inr tt) = false

    f-is-equiv-false : (b : Σ' λ a → Id (f a) false) → Id b (inr tt ,,' refl false)
    f-is-equiv-false (inl tt ,,' ())
    f-is-equiv-false (inr tt ,,' refl _) = refl _

    f-is-equiv-true : (b : Σ' λ a → Id (f a) true) → Id b (inl tt ,,' refl true)
    f-is-equiv-true (inl tt ,,' refl _) = refl _
    f-is-equiv-true (inr tt ,,' ())

    f-is-equiv : is-equiv' f
    f-is-equiv true  = (inl tt ,,' refl true)  ,,' f-is-equiv-true
    f-is-equiv false = (inr tt ,,' refl false) ,,' f-is-equiv-false

2=1+1 : Bool ≅' (⊤ + ⊤)
2=1+1 = f ,,' f-is-equiv
  where
    f : Bool → ⊤ + ⊤
    f true  = inl tt
    f false = inr tt

    f⁻¹ : ⊤ + ⊤ → Bool
    f⁻¹ (inl tt) = true
    f⁻¹ (inr tt) = false

    ff⁻¹ : (x : ⊤ + ⊤) → Id (f (f⁻¹ x)) x
    ff⁻¹ (inl tt) = refl (inl tt)
    ff⁻¹ (inr tt) = refl (inr tt)

    f-is-equiv : is-equiv' f
    f-is-equiv (inl tt) = (true ,,' refl _) ,,' (λ { (true ,,' refl _) → refl _ ; (false ,,' ()) })
    f-is-equiv (inr tt) = (false ,,' refl _) ,,' (λ { (true ,,' ()) ; (false ,,' refl _) → refl _ })

{- Wild experiments
equiv-inv'' : {A B : Set} (f : A ≅' B) → B ≅' A
equiv-inv'' {A} {B} (f ,,' f-is-equiv) = f⁻¹ ,,' f⁻¹-is-equiv
  where
    f⁻¹ : B → A
    f⁻¹ b = Σ'.pr₁ (Σ'.pr₁ (f-is-equiv b))

    f⁻¹-is-equiv : is-equiv' f⁻¹
    f⁻¹-is-equiv a = (f a ,,' {!f-is-equiv (f a)!}) ,,' {!!}

equiv-inv : {A B : Set} (f : A ≅ B) → B → A
equiv-inv (f ,, f-is-equiv) b = Σ-pr₁ (Σ-pr₁ (f-is-equiv b))

f-left-inverse : {A B : Set} (f : A ≅' B) (b : B)
               → Id ((Σ'.pr₁ f) ((equiv-inv' f) b)) b
f-left-inverse {A} {B} (f ,,' f-is-equiv) b = h (f-is-equiv b)
  where
    f⁻¹ : B → A
    f⁻¹ = equiv-inv' (f ,,' f-is-equiv)

    h : is-contr' (Σ' λ a → Id (f a) b)
      → Id (f (f⁻¹ b)) b
    h ((a ,,' id-fa-b) ,,' g) = {!g (a ,,' ?)!}
--    h ((a ,,' id-fa-b) ,,' pr₃) = id-fa-b ∙ subst _ _ f id-f⁻¹b-a
--    h ((a ,,' id-fa-b) ,,' pr₃) = trans (f (f⁻¹ b)) (f a) (sym (f a) (f (f⁻¹ b)) {!!}) b {!!}
      where
        id-3 : Id (f⁻¹ b ,,' {!!}) (a ,,' id-fa-b)
        id-3 = g (f⁻¹ b ,,' {!!})

        id-f⁻¹b-a : Id (f⁻¹ b) a
        id-f⁻¹b-a = {!transport !}

≅'-inj : {A B : Set} (f : A ≅' B) (a a' : A) → Id (Σ'.pr₁ f a) (Σ'.pr₁ f a') → Id a a'
≅'-inj (f ,,' f-is-equiv) a a' id-fa-fa' = {!f-is-equiv (f a)!}
  where
    k : is-contr' (Σ' λ a'' → Id (f a'') (f a))
    k = f-is-equiv (f a)

    k' : is-contr' (Σ' λ a'' → Id (f a'') (f a'))
    k' = f-is-equiv (f a')

f-right-inverse' : {A B : Set} (f : A ≅' B) (a : A)
                 → Id ((equiv-inv' f) ((Σ'.pr₁ f) a)) a
f-right-inverse' {A} {B} (f ,,' f-is-equiv) a with (f-is-equiv (f a))
...                                              | (a' ,,' id-fa'-fa) ,,' h = ≅'-inj (f ,,' f-is-equiv) a' a id-fa'-fa
{-
  where
    f⁻¹ : B → A
    f⁻¹ = equiv-inv' (f ,,' f-is-equiv)

    h : Id (f⁻¹ (f a)) a
    h = {!!}
-}

f-left-inverse' : {A B : Set} (f : A ≅' B) (b : B)
                → Id ((Σ'.pr₁ f) ((equiv-inv' f) b)) b
f-left-inverse' {A} {B} (f ,,' f-is-equiv) b = j (f-is-equiv b) (f-is-equiv (f (f⁻¹ b))) -- h (f-is-equiv (f (f⁻¹ b)))
  where
    f⁻¹ : B → A
    f⁻¹ = equiv-inv' (f ,,' f-is-equiv)

    f-inj : (a a' : A) → Id (f a) (f a') → Id a a'
    f-inj a a' id-fa-fa' = {!!}

    j' : is-contr' (Σ' λ a → Id (f a) (f (f⁻¹ b)))
       → Id (f (f⁻¹ b)) b
    j' ((a ,,' id-fa-ff⁻¹b) ,,' h) = {!f-inj a (f⁻¹ b) id-fa-ff⁻¹b!}

    j : is-contr' (Σ' λ a → Id (f a) b)
      → is-contr' (Σ' λ a → Id (f a) (f (f⁻¹ b)))
      → Id (f (f⁻¹ b)) b
    j ((a ,,' id-fa-b) ,,' g) ((a' ,,' id-fa'-ff⁻¹b) ,,' h) = id-fa-b ∙ (sym (subst _ _ f id-a-a') ∙ (sym id-fa'-ff⁻¹b))
      where
        k : is-contr' (Σ' λ a'' → Id (f a'') (f a))
        k = f-is-equiv (f a)

        k' : is-contr' (Σ' λ a'' → Id (f a'') (f a'))
        k' = f-is-equiv (f a')

        x : is-contr' (Σ' λ a'' → Id (f a'') (f a))
          → is-contr' (Σ' λ a'' → Id (f a'') (f a'))
          → Id (a' ,,' {!!}) (a ,,' id-fa-b)
        x ((pr₁ ,,' pr₂) ,,' pr₃) r = {!!} -- {! g (a' ,,' {!k'!}) !}

        id-fa-ff⁻¹b : Id (f a) (f (f⁻¹ b))
        id-fa-ff⁻¹b = subst _ _ f (sym (subst _ _ Σ'.pr₁ (g (f⁻¹ b ,,' sym {!!}))))

        id-a-a' : Id a a'
        id-a-a' = subst _ _ Σ'.pr₁ (h (a ,,' id-fa-ff⁻¹b))
-}


is-set : Set → Set
is-set A = (x y : A) (p q : Id x y) → Id p q

is-prop : Set → Set
is-prop A = (x y : A) → Id x y

ap : {A B : Set} (f : A → B) {x y : A} (p : Id x y) → Id (f x) (f y)
ap f (refl a) = refl (f a)

_⋆ : {A : Set} {P : A → Set} {x y : A} (p : Id x y)
   → P x → P y
_⋆ {A} {P} {x} {y} p = transport {A} p {P}

apd : {A : Set} {B : A → Set} (f : (x : A) → B x) {x y : A} (p : Id x y)
    → Id ((p ⋆) (f x)) (f y)
apd f (refl a) = refl (f a)

-- 2.11.3

tr : {A B : Set} (f g : A → B) {a b : A} (p : Id a b) (q : Id (f a) (g a))
   → Id (transport p q) ((ap g p ∙ q) ∙ (ap f p) ⁻¹)
tr f g (refl a) q = sym (trans (id-right-unit _) (id-left-unit _))

-- 3.3.4
prop-is-set : {A : Set} → is-prop A → is-set A
prop-is-set {A} A-is-prop x = λ y p q → trans (h p) (sym (h q))
  where
    g : (y : A) → Id x y
    g = A-is-prop x

    h : {y z : A} (p : Id y z) → Id p (g z ∙ (g y) ⁻¹)
    h (refl y) = sym (id-left-inv (g y))

prop-to-prop : {A : Set}
             → ((x y : A) → Id x y)
             → ((x y : A) → is-contr (Id x y))
prop-to-prop {A} A-is-prop x y = p ,, λ q → h q p
  where
    p : Id x y
    p = A-is-prop x y

    h : {x y : A} → is-prop (Id x y)
    h {x} {y} = prop-is-set A-is-prop x y
