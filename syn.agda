{-# OPTIONS --without-K --rewriting #-}

module syn where

open import lists

data Tm : ℕ → Set where
  V : {n : ℕ} → Subset n 1 → Tm n
  Lam : {n : ℕ} → Tm (suc n) → Tm n
  App : {n : ℕ} → Tm n → Tm n → Tm n

data Ty : ℕ → Set where
  𝒰 : {n : ℕ} → Ty n
  El : {n : ℕ} → Tm n → Ty n
  Π : {n : ℕ} → Ty n → Ty (suc n) → Ty n

weakenTm : {n m : ℕ} → Subset n m → Tm m → Tm n
weakenTm X (V v) = V (trans X v)
weakenTm X (Lam E) = Lam (weakenTm (yes X) E)
weakenTm X (App E F) = App (weakenTm X E) (weakenTm X F)

weakenTy : {n m : ℕ} → Subset n m → Ty m → Ty n
weakenTy X 𝒰 = 𝒰
weakenTy X (El E) = El (weakenTm X E)
weakenTy X (Π T S) = Π (weakenTy X T) (weakenTy (yes X) S)

WTm : {n : ℕ} → Tm n → Tm (suc n)
WTm E = weakenTm (no all-yes) E

WTy : {n : ℕ} → Ty n → Ty (suc n)
WTy T = weakenTy (no all-yes) T

weakenTm² : {n m k : ℕ} (X : Subset n m) (Y : Subset m k) (E : Tm k) →
  weakenTm X (weakenTm Y E) ≡ weakenTm (trans X Y) E
weakenTm² X Y (V v) = cong V (trans-assoc X Y v)
weakenTm² X Y (Lam E) = cong Lam (weakenTm² (yes X) (yes Y) E)
weakenTm² X Y (App E F) = cong₂ App (weakenTm² X Y E) (weakenTm² X Y F)

weakenTy² : {n m k : ℕ} (X : Subset n m) (Y : Subset m k) (T : Ty k) →
  weakenTy X (weakenTy Y T) ≡ weakenTy (trans X Y) T
weakenTy² X Y 𝒰 = refl
weakenTy² X Y (El E) = cong El (weakenTm² X Y E)
weakenTy² X Y (Π T S) =
  cong₂ Π (weakenTy² X Y T) (weakenTy² (yes X) (yes Y) S)

WTmLem₁ : {n m : ℕ} (X : Subset n m) (E : Tm m) →
  WTm (weakenTm X E) ≡ weakenTm (no X) E
WTmLem₁ X E = weakenTm² (no all-yes) X E

WTyLem₁ : {n m : ℕ} (X : Subset n m) (T : Ty m) →
  weakenTy (no all-yes) (weakenTy X T) ≡ weakenTy (no X) T
WTyLem₁ X T =
  weakenTy² (no all-yes) X T
    ∙ cong (λ Y → weakenTy (no Y) T) (all-yes-L X)

{-# REWRITE WTyLem₁ #-}

WTmLem₂ : {n m : ℕ} (X : Subset n m) (E : Tm m) →
  weakenTm (yes X) (WTm E) ≡ weakenTm (no X) E
WTmLem₂ X E = weakenTm² (yes X) (no all-yes) E

WTyLem₂ : {n m : ℕ} (X : Subset n m) (T : Ty m) →
  weakenTy (yes X) (WTy T) ≡ weakenTy (no X) T
WTyLem₂ X T =
  weakenTy² (yes X) (no all-yes) T
    ∙ cong (λ X → weakenTy (no X) T) (all-yes-R X)

{-# REWRITE WTyLem₂ #-}

Tms : ℕ → ℕ → Set
Tms n m = Vec (Tm n) m

W₁Tms : {n m : ℕ} → Tms n m → Tms (suc n) m
W₁Tms σ = mapVec WTm σ

W₂Tms : {n m : ℕ} → Tms n m → Tms (suc n) (suc m)
W₂Tms σ = W₁Tms σ ⊕ V (yes all-no)

idTms : {n : ℕ} → Tms n n
idTms {zero} = !
idTms {suc n} = W₂Tms idTms

_ᵣ∘_ : {n m k : ℕ} → Subset m k → Tms n m → Tms n k
X ᵣ∘ σ = derive σ X

_∘ᵣ_ : {n m k : ℕ} → Tms m k → Subset n m → Tms n k
σ ∘ᵣ X = mapVec (weakenTm X) σ

W₁ᵣ∘ : {n m k : ℕ} (X : Subset m k) (σ : Tms n m) →
  W₁Tms (X ᵣ∘ σ) ≡ X ᵣ∘ W₁Tms σ
W₁ᵣ∘ done σ = refl
W₁ᵣ∘ (yes X) σ = cong (_⊕ WTm (𝑧Vec σ)) (W₁ᵣ∘ X (πVec σ))
W₁ᵣ∘ (no X) σ = W₁ᵣ∘ X (πVec σ)

W₂ᵣ∘ : {n m k : ℕ} (X : Subset m k) (σ : Tms n m) →
  W₂Tms (X ᵣ∘ σ) ≡ yes X ᵣ∘ W₂Tms σ
W₂ᵣ∘ X σ = cong (_⊕ V (yes all-no)) (W₁ᵣ∘ X σ)

W₁∘ᵣ : {n m k : ℕ} (σ : Tms m k) (X : Subset n m) →
  W₁Tms (σ ∘ᵣ X) ≡ σ ∘ᵣ no X
W₁∘ᵣ ! X = refl
W₁∘ᵣ (σ ⊕ E) X = cong₂ _⊕_ (W₁∘ᵣ σ X) (WTmLem₁ X E)

W₁∘ᵣ' : {n m k : ℕ} (σ : Tms m k) (X : Subset n m) →
  W₁Tms σ ∘ᵣ yes X ≡ σ ∘ᵣ no X
W₁∘ᵣ' ! X = refl
W₁∘ᵣ' (σ ⊕ E) X = cong₂ _⊕_ (W₁∘ᵣ' σ X) (WTmLem₂ X E)

W₂∘ᵣ : {n m k : ℕ} (σ : Tms m k) (X : Subset n m) →
  W₂Tms (σ ∘ᵣ X) ≡ W₂Tms σ ∘ᵣ yes X
W₂∘ᵣ σ X = cong (_⊕ V (yes all-no)) (W₁∘ᵣ σ X ∙ sym (W₁∘ᵣ' σ X))

_[_]Tm : {n m : ℕ} → Tm m → Tms n m → Tm n
V v [ σ ]Tm = 𝑧Vec (derive σ v)
Lam E [ σ ]Tm = Lam (E [ W₂Tms σ ]Tm)
App E F [ σ ]Tm = App (E [ σ ]Tm) (F [ σ ]Tm)

_[_]Ty : {n m : ℕ} → Ty m → Tms n m → Ty n
𝒰 [ σ ]Ty = 𝒰
El E [ σ ]Ty = El (E [ σ ]Tm)
Π T S [ σ ]Ty = Π (T [ σ ]Ty) (S [ W₂Tms σ ]Ty)

weaken[]Tm : {n m k : ℕ} (E : Tm k) (X : Subset m k) (σ : Tms n m) →
  weakenTm X E [ σ ]Tm ≡ E [ X ᵣ∘ σ ]Tm
weaken[]Tm (V v) X σ = cong 𝑧Vec (sym (derive² σ X v))
weaken[]Tm (Lam E) X σ =
  cong Lam
    (weaken[]Tm E (yes X) (W₂Tms σ)
      ∙ cong (E [_]Tm) (sym (W₂ᵣ∘ X σ)))
weaken[]Tm (App E F) X σ =
  cong₂ App (weaken[]Tm E X σ) (weaken[]Tm F X σ)

weaken[]Ty : {n m k : ℕ} (T : Ty k) (X : Subset m k) (σ : Tms n m) →
  weakenTy X T [ σ ]Ty ≡ T [ X ᵣ∘ σ ]Ty
weaken[]Ty 𝒰 X σ = refl
weaken[]Ty (El E) X σ = cong El (weaken[]Tm E X σ)
weaken[]Ty (Π T S) X σ =
  cong₂ Π
    (weaken[]Ty T X σ)
    (weaken[]Ty S (yes X) (W₂Tms σ)
      ∙ cong (S [_]Ty) (sym (W₂ᵣ∘ X σ)))

[]weakenTm : {n m k : ℕ} (E : Tm k) (σ : Tms m k) (X : Subset n m) →
  weakenTm X (E [ σ ]Tm) ≡ E [ σ ∘ᵣ X ]Tm
[]weakenTm (V v) σ X = cong 𝑧Vec (sym (deriveMap (weakenTm X) σ v))
[]weakenTm (Lam E) σ X =
  cong Lam
    ([]weakenTm E (W₂Tms σ) (yes X)
      ∙ cong (E [_]Tm) (sym (W₂∘ᵣ σ X)))
[]weakenTm (App E F) σ X =
  cong₂ App ([]weakenTm E σ X) ([]weakenTm F σ X)

[]weakenTy : {n m k : ℕ} (T : Ty k) (σ : Tms m k) (X : Subset n m) →
  weakenTy X (T [ σ ]Ty) ≡ T [ σ ∘ᵣ X ]Ty
[]weakenTy 𝒰 σ X = refl
[]weakenTy (El E) σ X = cong El ([]weakenTm E σ X)
[]weakenTy (Π T S) σ X =
  cong₂ Π
    ([]weakenTy T σ X)
    ([]weakenTy S (W₂Tms σ) (yes X)
      ∙ cong (S [_]Ty) (sym (W₂∘ᵣ σ X)))

idLem₁ : {n m : ℕ} (X : Subset n m) → X ᵣ∘ idTms ≡ idTms ∘ᵣ X
idLem₁ done = refl
idLem₁ (yes X) =
  sym (W₂ᵣ∘ X idTms) ∙ cong W₂Tms (idLem₁ X) ∙ W₂∘ᵣ idTms X
idLem₁ (no X) =
  sym (W₁ᵣ∘ X idTms) ∙ cong W₁Tms (idLem₁ X) ∙ W₁∘ᵣ idTms X

switchLem₁ : {n m : ℕ} (X : Subset n m) (T : Ty (suc m)) (E : Tm m) →
  weakenTy (yes X) T [ idTms ⊕ weakenTm X E ]Ty
    ≡ weakenTy X (T [ idTms ⊕ E ]Ty)
switchLem₁ X T E =
  weaken[]Ty T (yes X) (idTms ⊕ weakenTm X E)
    ∙ cong (λ σ → T [ σ ⊕ weakenTm X E ]Ty) (idLem₁ X)
    ∙ sym ([]weakenTy T (idTms ⊕ E) X)

{-# REWRITE switchLem₁ #-}
