{-# OPTIONS --without-K #-} 
 

open import Agda.Primitive public using (Level; lzero; lsuc; _⊔_; Setω) 


data ℕ : Set where
  zero : ℕ 
  succ : ℕ → ℕ


ℕ-induction : ∀ {C : ℕ → Set} → (C (zero)) → (∀ (n : ℕ) → (C n → (C (succ n)))) → (∀ (n : ℕ) → C n)
ℕ-induction p f zero = p 
ℕ-induction p f (succ n) = f n (ℕ-induction p f n) 

data Bool : Set where
  true : Bool
  false : Bool

Bool-induction : ∀ {C : Bool → Set} → (C true) → (C false) → (∀ (c : Bool) → C c)
Bool-induction p q true = p
Bool-induction p q false = q

data Empty : Set where

Empty-induction : ∀ {C : Empty → Set} → (∀ (x : Empty) → C x)
Empty-induction ()

𝟘 : Set
𝟘 = Empty

data 𝟙 : Set where
  pt : 𝟙

𝟙-induction : ∀ {C : 𝟙 → Set} → (C pt) → (∀ (x : 𝟙) → C x)
𝟙-induction H pt = H

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



data _≡_   {A : Set} : A → A → Set  where
  refl : ∀ (a : A) →  a ≡ a

Id-induction : ∀ {A : Set } {C : forall (x y : A) ->  (x ≡ y) -> Set } → ( ∀ (x : A) → (C x x (refl x)) ) → (forall  ( a b : A)  (p : a ≡ b) → (C a b p) )
Id-induction {A} {C} f a .a (refl .a) = f a

Id-recursion : ∀ {A : Set } {C : Set } → ( ∀ (x : A) → C ) → (forall  ( a b : A)  (p : a ≡ b) → C )
Id-recursion x a .a (refl .a) = x a

inv-path : ∀ {A : Set} {a b : A} (p : a ≡ b)  →  b ≡ a
inv-path (refl _) = refl _

concat : ∀  {A : Set} {x y z : A} →  x ≡ y → y ≡ z → x ≡ z
concat (refl _) q = q

add-ℕ :  ℕ  →  ℕ  →  ℕ 
add-ℕ zero m = m
add-ℕ (succ n) m = succ (add-ℕ n m)

mult-ℕ : ℕ → ℕ → ℕ
mult-ℕ zero m = zero
mult-ℕ (succ n) m = add-ℕ (mult-ℕ n m) m

max-ℕ : ℕ → ℕ → ℕ
max-ℕ zero m = m
max-ℕ (succ n) zero = succ n
max-ℕ (succ n) (succ m) = succ (max-ℕ n m) 

min-ℕ : ℕ → ℕ → ℕ
min-ℕ zero m = zero
min-ℕ (succ n) zero = zero
min-ℕ (succ n) (succ m) = succ (min-ℕ n m)

pred : ℕ → ℕ
pred zero = zero
pred (succ n) = n

¬_ : Set → Set
¬ A = A → Empty

neg-Bool : Bool → Bool
neg-Bool true = false
neg-Bool false = true

_∧_ : Bool → Bool → Bool
false ∧ b2 = false
true ∧ true = true
true ∧ false = false

_∨_ : Bool → Bool → Bool
true ∨ b2 = true
false ∨ true = true
false ∨ false = false

_↔_ : Set → Set → Set
A ↔ B = (A → B) × (B → A)

data list (A : Set) :  (Set)  where
  nil :  list A
  cons : A → (list A) → (list A)


fold-list : ∀ {A B : Set} → B →  (A → B → B) → (list A → B)
fold-list b μ nil = b
fold-list b μ (cons x l) = μ x (fold-list b μ l)

map-list : ∀ {A B : Set} → (A → B) → (list A → list B)
map-list f nil = nil
map-list f (cons x l) = cons (f x) (map-list f l)

concat-list : ∀ {A : Set} → list A → list A → list A
concat-list nil l2 = l2
concat-list (cons x l1) l2 = cons x (concat-list l1 l2)

flatten-list : ∀ {A : Set} → list (list A) → list A
flatten-list nil = nil
flatten-list (cons nil l₁) = flatten-list l₁
flatten-list (cons (cons x l) l₁) = cons x (flatten-list (cons l l₁))

_·_ : ∀ {A : Set}  {x y z : A} →  (x ≡ y) → (y ≡ z) → (x ≡ z)
p · q = concat p q

concat-assoc : ∀ {A : Set} {x y z w : A} (p : x ≡ y) (q : y ≡ z) (t : z ≡ w) →  (( (p · q ) · t ) ≡  ( p · (q · t)))
concat-assoc (refl _) (refl _) t = refl t

refl-l : ∀ {A : Set} {x y  : A } (p : x  ≡ y) →  ((refl x) · p) ≡ p
refl-l (refl _) = refl _

refl-r : ∀ {A : Set} {x y : A} (p : x ≡ y) → (p · (refl y)) ≡ p
refl-r (refl _) = refl _

left-inv : ∀ {A : Set} {x y : A} (p : x ≡ y) → ((inv-path p) ·  p) ≡ (refl _)
left-inv (refl _) = refl _

right-inv :  ∀ {A : Set} {x y : A} (p : x ≡ y) → (p · (inv-path p)) ≡ (refl _)
right-inv (refl _) = refl _

fun-ap : ∀ {A B : Set} {x y : A} (f : A → B) (p : x ≡ y) → (f x) ≡ (f y)
fun-ap f (refl _) = refl _

_∘_ : ∀ {A B C : Set} → (B → C) → (A → B) → (A → C)
(g ∘ f) x = g (f x)

id : ∀ (A : Set) → A → A
id A x = x

ap-id : ∀ {A : Set} {x y : A} (p : x ≡ y) → p ≡ (fun-ap (id A ) p)
ap-id (refl x) = refl _

ap-comp : ∀ {A B C : Set} {x y : A} (p : x ≡ y) (f : A → B) (g : B → C) → (fun-ap g (fun-ap f p)) ≡ (fun-ap (g ∘ f) p)
ap-comp (refl x) f g = refl _


ap-refl : ∀ {A B : Set} {x : A} (f : A → B) → (fun-ap f (refl x)) ≡ (refl (f x))
ap-refl f = refl _

ap-inv : ∀ {A B : Set} {x y : A} (p : x ≡ y) (f : A → B) → (fun-ap f (inv-path p)) ≡ (inv-path (fun-ap f p))
ap-inv (refl _) f = refl _

ap-concat : ∀ {A B : Set} {x y z : A} (p : x ≡ y) (q : y ≡ z) (f : A → B)  → (fun-ap f (p · q)) ≡ ( (fun-ap f p) · (fun-ap f q))
ap-concat (refl _) q f = refl _

transp : ∀ {A : Set} (B : A → Set)  {x y : A}  →  (x ≡ y) → B x → B y
transp B (refl x) z = z

fun-ap-dep : ∀ {A : Set} {B : A → Set} (f : ∀ (x : A) → B x) {x y : A}  (p : x ≡ y) →  (transp B p (f x)) ≡ (f y)
fun-ap-dep f (refl _) = refl _

id-Σ-type-endpoint : ∀ {A : Set} (a : A) (y : Σ A (λ x → a ≡ x))   →  (deppair a (refl a)) ≡ y
id-Σ-type-endpoint a (deppair .a (refl .a)) = refl _

_+ℕ_ : ℕ → ℕ → ℕ
n +ℕ m = add-ℕ n m

infixl 1 _≡_

left-unit-law-add-ℕ : ∀ (n : ℕ) → ((zero +ℕ n) ≡ n)
left-unit-law-add-ℕ n = refl _ 


right-unit-law-add-ℕ : ∀ ( n : ℕ) → (n +ℕ zero ≡ n)
right-unit-law-add-ℕ zero = refl _
right-unit-law-add-ℕ (succ n) = fun-ap succ (right-unit-law-add-ℕ n)

left-succ-law-add-ℕ : ∀ (m n : ℕ) → ((succ m) +ℕ n ≡ succ (m +ℕ n))
left-succ-law-add-ℕ m n = refl _

right-succ-law-add-ℕ : ∀ (m n : ℕ) → (m +ℕ (succ n) ≡ succ (m +ℕ n))
right-succ-law-add-ℕ zero n =  fun-ap succ (inv-path (left-unit-law-add-ℕ n)) 
right-succ-law-add-ℕ (succ m) n = fun-ap succ (right-succ-law-add-ℕ m n)

assoc-add-ℕ : ∀ (m n k : ℕ) → (m +ℕ n) +ℕ k ≡ m +ℕ (n +ℕ k)
assoc-add-ℕ zero n k = refl _
assoc-add-ℕ (succ m) n k = fun-ap succ (assoc-add-ℕ m n k)


commutative-add-ℕ : ∀ (m n : ℕ) → m +ℕ n ≡ n +ℕ m
commutative-add-ℕ zero n = inv-path (right-unit-law-add-ℕ n)
commutative-add-ℕ (succ m) n = concat (fun-ap succ (commutative-add-ℕ m n))  (inv-path (right-succ-law-add-ℕ n m))

distributive-inv-concat : ∀ {A : Set} {x y z : A} (p : x ≡ y) (q : y ≡ z) → inv-path (p · q) ≡ (inv-path q) · (inv-path p)
distributive-inv-concat (refl _) q = concat (refl-l (inv-path (q))) (concat (refl _) (inv-path  (refl-r (inv-path q))))

inv-con : ∀ {A : Set} {x y z : A} (p : x ≡ y) (q : y ≡ z) (r : x ≡ z) → (p · q ≡ r) → (q ≡ (inv-path p) · r)
inv-con (refl x) q r t = concat t (refl r)

path-uniq-inv : ∀ {A : Set} {x y : A} (p : x ≡ y) (q : y ≡ x) → (p · q ≡ (refl _)) → (q ≡ inv-path p)
path-uniq-inv (refl _) q r = concat r (refl _)


con-inv :  ∀ {A : Set} (x y z : A) (p : x ≡ y) (q : y ≡ z) (r : x ≡ z) → (p · q ≡ r) → (p ≡ r · (inv-path q))
con-inv x y z (refl x) q r t = concat (inv-path (right-inv q)) (fun-ap (λ l → (l · (inv-path q))) t)


