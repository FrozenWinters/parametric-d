{-# OPTIONS --without-K --rewriting #-}

module lists where

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_) public
open import Relation.Binary.PropositionalEquality
  renaming (trans to infixl 20 _∙_) hiding (trans-assoc) public
open ≡-Reasoning public
open import Function public
open import Data.Nat hiding (_⊔_) public

{-# BUILTIN REWRITE _≡_ #-}

private
  variable
    ℓ ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level

data Subset : (n m : ℕ) → Set where
  done : Subset 0 0
  yes : {n m : ℕ} → Subset n m → Subset (suc n) (suc m)
  no : {n m : ℕ} → Subset n m → Subset (suc n) m

trans : {n m k : ℕ} → Subset n m → Subset m k → Subset n k
trans done done = done
trans (yes X) (yes Y) = yes (trans X Y)
trans (yes X) (no Y) = no (trans X Y)
trans (no X) Y = no (trans X Y)

trans-assoc : {n k l m : ℕ}
  (X : Subset n k) (Y : Subset k l) (Z : Subset l m) →
  trans X (trans Y Z) ≡ trans (trans X Y) Z
trans-assoc done done done = refl
trans-assoc (yes X) (yes Y) (yes Z) = cong yes (trans-assoc X Y Z)
trans-assoc (yes X) (yes Y) (no Z) = cong no (trans-assoc X Y Z)
trans-assoc (yes X) (no Y) Z = cong no (trans-assoc X Y Z)
trans-assoc (no X) Y Z = cong no (trans-assoc X Y Z)

all-yes : {n : ℕ} → Subset n n
all-yes {zero} = done
all-yes {suc n} = yes all-yes

all-yes-L : {n m : ℕ} (X : Subset n m) → trans all-yes X ≡ X
all-yes-L done = refl
all-yes-L (yes X) = cong yes (all-yes-L X)
all-yes-L (no X) = cong no (all-yes-L X)

all-yes-R : {n m : ℕ} (X : Subset n m) → trans X all-yes ≡ X
all-yes-R done = refl
all-yes-R (yes X) = cong yes (all-yes-R X)
all-yes-R (no X) = cong no (all-yes-R X)

all-no : {n : ℕ} → Subset n 0
all-no {zero} = done
all-no {suc n} = no all-no

all-no-R : {n m : ℕ} (X : Subset n m) → trans X all-no ≡ all-no
all-no-R done = refl
all-no-R (yes X) = cong no (all-no-R X)
all-no-R (no X) = cong no (all-no-R X)

all-no-lem : {n : ℕ} (X : Subset n 0) →
  X ≡ all-no
all-no-lem done = refl
all-no-lem (no X) = cong no (all-no-lem X)

{-# REWRITE all-yes-L all-yes-R all-no-R #-}

infixl 20 _⊕_
data Vec (A : Set ℓ) : ℕ → Set ℓ where
  ! : Vec A 0
  _⊕_ : {n : ℕ} → Vec A n → A → Vec A (suc n)

𝑧Vec : {A : Set ℓ} {n : ℕ} → Vec A (suc n) → A
𝑧Vec (σ ⊕ t) = t

πVec : {A : Set ℓ} {n : ℕ} → Vec A (suc n) → Vec A n
πVec (σ ⊕ t) = σ

derive : {A : Set ℓ} {n m : ℕ} → Vec A n → Subset n m → Vec A m
derive σ done = !
derive σ (yes X) = derive (πVec σ) X ⊕ 𝑧Vec σ 
derive σ (no X) = derive (πVec σ) X

derive² : {A : Set ℓ} {n m k : ℕ} (σ : Vec A n)
  (X : Subset n m) (Y : Subset m k) →
  derive (derive σ X) Y ≡ derive σ (trans X Y)
derive² σ done done = refl
derive² σ (yes X) (yes Y) = cong (_⊕ 𝑧Vec σ) (derive² (πVec σ) X Y)
derive² σ (yes X) (no Y) = derive² (πVec σ) X Y
derive² σ (no X) Y = derive² (πVec σ) X Y

deriveId : {A : Set ℓ} {n : ℕ} (σ : Vec A n) →
  derive σ all-yes ≡ σ
deriveId ! = refl
deriveId (σ ⊕ t) = cong (_⊕ t) (deriveId σ)

mapVec : {A : Set ℓ₁} {B : Set ℓ₂} {n : ℕ}
  (f : A → B) → Vec A n → Vec B n
mapVec {n = zero} f σ = !
mapVec {n = suc n} f σ = mapVec f (πVec σ) ⊕ f (𝑧Vec σ)

mapId : {A : Set ℓ} {n : ℕ} (σ : Vec A n) →
  mapVec (λ x → x) σ ≡ σ
mapId ! = refl
mapId (σ ⊕ v) = cong (_⊕ v) (mapId σ)

mapVec² : {A : Set ℓ₁} {B : Set ℓ₂} {C : Set ℓ₃} {n : ℕ}
  (g : B → C) (f : A → B) (σ : Vec A n) →
  mapVec g (mapVec f σ) ≡ mapVec (g ∘ f) σ
mapVec² {n = zero} g f σ = refl
mapVec² {n = suc n} g f σ = cong (_⊕ g (f (𝑧Vec σ))) (mapVec² g f (πVec σ))

deriveMap : {A : Set ℓ₁} {B : Set ℓ₂} {n m : ℕ}
  (f : A → B) (σ : Vec A n) (X : Subset n m) →
  derive (mapVec f σ) X ≡ mapVec f (derive σ X)
deriveMap f σ done = refl
deriveMap f σ (yes X) = cong (_⊕ f (𝑧Vec σ)) (deriveMap f (πVec σ) X)
deriveMap f σ (no X) = deriveMap f (πVec σ) X

{-# REWRITE derive² deriveId mapId mapVec² deriveMap #-}

record 𝐶𝑡𝑥Alg ℓ₁ ℓ₂ : Set (lsuc ℓ₁ ⊔ lsuc ℓ₂) where
  constructor
    𝒞Alg
  field
    X : Set ℓ₁
    ty : X → Set ℓ₂
    Z : X
    S : {α : X} → ty α → X

open 𝐶𝑡𝑥Alg

data 𝐶𝑡𝑥 (𝒞 : 𝐶𝑡𝑥Alg ℓ₁ ℓ₂) : X 𝒞 → Set (ℓ₁ ⊔ ℓ₂) where
  ∅ : 𝐶𝑡𝑥 𝒞 (Z 𝒞)
  _⊹_ : {α : X 𝒞} (Γ : 𝐶𝑡𝑥 𝒞 α) (A : ty 𝒞 α) → 𝐶𝑡𝑥 𝒞 (S 𝒞 A)

record 𝑅𝑒𝑛Alg (𝒞 : 𝐶𝑡𝑥Alg ℓ₁ ℓ₂) ℓ₃ : Set (ℓ₁ ⊔ ℓ₂ ⊔ lsuc ℓ₃) where
  constructor
    ℛAlg
  field
    Y : X 𝒞 → X 𝒞 → Set ℓ₃
    weaken : {α β : X 𝒞} → Y α β → ty 𝒞 β → ty 𝒞 α
    null :  Y (Z 𝒞) (Z 𝒞)
    keep : {α β : X 𝒞} (A : ty 𝒞 β)
      (𝑓 : Y α β) → Y (S 𝒞 (weaken 𝑓 A)) (S 𝒞 A)
    drop : {α β : X 𝒞} (A : ty 𝒞 α) → Y α β → Y (S 𝒞 A) β

open 𝑅𝑒𝑛Alg

data 𝑅𝑒𝑛 {𝒞 : 𝐶𝑡𝑥Alg ℓ₁ ℓ₂} (ℛ : 𝑅𝑒𝑛Alg 𝒞 ℓ₃)
  : {α β : X 𝒞} → 𝐶𝑡𝑥 𝒞 α → 𝐶𝑡𝑥 𝒞 β → Y ℛ α β → Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃) where
  done : 𝑅𝑒𝑛 ℛ ∅ ∅ (null ℛ)
  yes : {α β : X 𝒞} {Γ : 𝐶𝑡𝑥 𝒞 α} {Δ : 𝐶𝑡𝑥 𝒞 β} {𝑓 : Y ℛ α β} (A : ty 𝒞 β)
    → 𝑅𝑒𝑛 ℛ Γ Δ 𝑓 → 𝑅𝑒𝑛 ℛ (Γ ⊹ weaken ℛ 𝑓 A) (Δ ⊹ A) (keep ℛ A 𝑓)
  no : {α β : X 𝒞} {Γ : 𝐶𝑡𝑥 𝒞 α} {Δ : 𝐶𝑡𝑥 𝒞 β} {𝑓 : Y ℛ α β} (A : ty 𝒞 α)
    → 𝑅𝑒𝑛 ℛ Γ Δ 𝑓 → 𝑅𝑒𝑛 ℛ (Γ ⊹ A) Δ (drop ℛ A 𝑓)
