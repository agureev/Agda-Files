{-# OPTIONS --without-K #-} 
 

open import Agda.Primitive public using (Level; lzero; lsuc; _⊔_; Setω) 


data ℕ : Set where
  zero : ℕ 
  succ : ℕ → ℕ 



data Bool : Set where
  true : Bool
  false : Bool

data Empty : Set where
data _+_ {ℓ1 ℓ2}(A : Set ℓ1) (B : Set ℓ2) : Set (ℓ1 ⊔ ℓ2) where

    inl : A → A + B
    inr : B → A + B

rec+ : ∀  {A : Set} {B : Set } {C : Set } →
    (A → C) → (B → C) → (A + B → C)
rec+ f g (inl x) = f x
rec+ f g (inr x) = g x



ind+ : ∀  {A : Set } {B : Set } {C : A + B → Set } → 
        ( ∀ (a : A) → C (inl a)) → ( ∀ (b : B) → (C (inr b)) ) → ( ∀ (c : A + B) → (C c))
ind+ f g (inl x) = f x
ind+ f g (inr x) = g x


data _×_ (A : Set) (B : Set) : Set where
  pair : A → B → A × B

rec× : ∀ {A : Set} {B : Set} {C : Set} → 
   (A → B → C) → (A × B → C)
rec× f (pair x x₁) = f x x₁

ind× : ∀ {A : Set} {B : Set} {C : A × B → Set} → 
  (∀ (a : A) → ∀ (b : B) → C(pair a b)) → (∀ (x : A × B) → C(x))
ind× f (pair x x₁) = f x x₁

data Σ (A : Set) (B : A → Set) : Set where
  deppair : ∀ (x : A) → B x → Σ A B

Σ-recursion : ∀ {A : Set} {B : A → Set} {C : Set} → 
                                                 (∀ (a : A) → B a → C) → (Σ A B → C)
Σ-recursion f (deppair x x₁) = f x x₁


Σ-induction : ∀ {A : Set} {B : A → Set} {C : (Σ A B) → Set} → 
                                   (∀ (a : A) → ∀ (b : B a) → (C (deppair a b))) → (∀ (x : Σ A B) → C x)
Σ-induction f (deppair x x₁) = f x x₁

data Con : Set
data Ty : Con → Set 

data Con where
 ⊥ : Con
 _,_ : (Γ : Con) → Ty Γ → Con 

data Ty where 
 U : ∀ {Γ} → Ty Γ
 Π : ∀ {Γ} (A : Ty Γ) (B : Ty (Γ , A)) → Ty Γ



