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

weakenTmId : {n : ℕ} (E : Tm n) → weakenTm all-yes E ≡ E
weakenTmId (V v) = refl
weakenTmId (Lam E) = cong Lam (weakenTmId E)
weakenTmId (App E F) = cong₂ App (weakenTmId E) (weakenTmId F)

weakenTyId : {n : ℕ} (T : Ty n) → weakenTy all-yes T ≡ T
weakenTyId 𝒰 = refl
weakenTyId (El E) = cong El (weakenTmId E)
weakenTyId (Π T S) = cong₂ Π (weakenTyId T) (weakenTyId S)

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

{-# REWRITE weakenTmId weakenTyId weakenTm² weakenTy² #-}

Tms : ℕ → ℕ → Set
Tms n m = Vec (Tm n) m

W₁Tms : {n m : ℕ} → Tms n m → Tms (suc n) m
W₁Tms σ = mapVec WTm σ

W₂Tms : {n m : ℕ} → Tms n m → Tms (suc n) (suc m)
W₂Tms σ = W₁Tms σ ⊕ V (yes all-no)

idTms : {n : ℕ} → Tms n n
idTms {zero} = !
idTms {suc n} = W₂Tms idTms

_[_]Tm : {n m : ℕ} → Tm m → Tms n m → Tm n
V v [ σ ]Tm = 𝑧Vec (derive σ v)
Lam E [ σ ]Tm = Lam (E [ W₂Tms σ ]Tm)
App E F [ σ ]Tm = App (E [ σ ]Tm) (F [ σ ]Tm)

_[_]Ty : {n m : ℕ} → Ty m → Tms n m → Ty n
𝒰 [ σ ]Ty = 𝒰
El E [ σ ]Ty = El (E [ σ ]Tm)
Π T S [ σ ]Ty = Π (T [ σ ]Ty) (S [ W₂Tms σ ]Ty)

weaken[]Tm : {n m k : ℕ} (E : Tm k) (X : Subset m k) (σ : Tms n m) →
  weakenTm X E [ σ ]Tm ≡ E [ derive σ X ]Tm
weaken[]Tm (V v) X σ = refl
weaken[]Tm (Lam E) X σ =
  cong Lam (weaken[]Tm E (yes X) (W₂Tms σ))
weaken[]Tm (App E F) X σ =
  cong₂ App (weaken[]Tm E X σ) (weaken[]Tm F X σ)

weaken[]Ty : {n m k : ℕ} (T : Ty k) (X : Subset m k) (σ : Tms n m) →
  weakenTy X T [ σ ]Ty ≡ T [ derive σ X ]Ty
weaken[]Ty 𝒰 X σ = refl
weaken[]Ty (El E) X σ = cong El (weaken[]Tm E X σ)
weaken[]Ty (Π T S) X σ =
  cong₂ Π (weaken[]Ty T X σ) (weaken[]Ty S (yes X) (W₂Tms σ))

[]weakenTm : {n m k : ℕ} (E : Tm k) (σ : Tms m k) (X : Subset n m) →
  weakenTm X (E [ σ ]Tm) ≡ E [ mapVec (weakenTm X) σ ]Tm
[]weakenTm (V v) σ X = refl
[]weakenTm (Lam E) σ X =
  cong Lam
    ([]weakenTm E (W₂Tms σ) (yes X))
[]weakenTm (App E F) σ X =
  cong₂ App ([]weakenTm E σ X) ([]weakenTm F σ X)

[]weakenTy : {n m k : ℕ} (T : Ty k) (σ : Tms m k) (X : Subset n m) →
  weakenTy X (T [ σ ]Ty) ≡ T [ mapVec (weakenTm X) σ ]Ty
[]weakenTy 𝒰 σ X = refl
[]weakenTy (El E) σ X = cong El ([]weakenTm E σ X)
[]weakenTy (Π T S) σ X =
  cong₂ Π
    ([]weakenTy T σ X)
    ([]weakenTy S (W₂Tms σ) (yes X))

{-# REWRITE weaken[]Tm weaken[]Ty []weakenTm []weakenTy #-}

_∘Tm_ : {n m k : ℕ} → Tms m k → Tms n m → Tms n k
σ ∘Tm τ = mapVec _[ τ ]Tm σ

[][]Tm : {n m k : ℕ} (E : Tm k) (σ : Tms m k) (τ : Tms n m) →
  E [ σ ]Tm [ τ ]Tm ≡ E [ σ ∘Tm τ ]Tm
[][]Tm (V v) σ τ = refl
[][]Tm (Lam E) σ τ = cong Lam ([][]Tm E (W₂Tms σ) (W₂Tms τ))
[][]Tm (App E F) σ τ = cong₂ App ([][]Tm E σ τ) ([][]Tm F σ τ)

[][]Ty : {n m k : ℕ} (T : Ty k) (σ : Tms m k) (τ : Tms n m) →
  T [ σ ]Ty [ τ ]Ty ≡ T [ σ ∘Tm τ ]Ty
[][]Ty 𝒰 σ τ = refl
[][]Ty (El E) σ τ = cong El ([][]Tm E σ τ)
[][]Ty (Π T S) σ τ = cong₂ Π ([][]Ty T σ τ) ([][]Ty S (W₂Tms σ) (W₂Tms τ))

{-# REWRITE [][]Tm [][]Ty #-}

idLem₁ : {n m : ℕ} (X : Subset n m) →
  derive idTms X ≡ mapVec (weakenTm X) idTms
idLem₁ done = refl
idLem₁ (yes X) = cong (_⊕ V (yes all-no)) (idLem₁ (no X))
idLem₁ (no X) = cong W₁Tms (idLem₁ X)

{-# REWRITE idLem₁ #-}

idLem₂ : {n m : ℕ} (σ : Tms n m) →
  mapVec _[ σ ]Tm idTms ≡ σ
idLem₂ ! = refl
idLem₂ (σ ⊕ E) = cong (_⊕ E) (idLem₂ σ)

idLem₃Var : {n : ℕ} (v : Subset n 1) →
  V v [ idTms ]Tm ≡ V v
idLem₃Var (yes X) = cong (V ∘ yes) (sym (all-no-lem X))
idLem₃Var (no v) = cong (V ∘ no) (all-yes-R v)

idLem₃ : {n : ℕ} (E : Tm n) →
  E [ idTms ]Tm ≡ E
idLem₃ (V v) = idLem₃Var v
idLem₃ (Lam E) = cong Lam (idLem₃ E)
idLem₃ (App E F) = cong₂ App (idLem₃ E) (idLem₃ F)

idLem₄ : {n m : ℕ} (σ : Tms n m) →
  mapVec _[ idTms ]Tm σ ≡ σ
idLem₄ ! = refl
idLem₄ (σ ⊕ E) = cong₂ _⊕_ (idLem₄ σ) (idLem₃ E)

{-idLem₅ : {n m : ℕ} (X : Subset n m) →
  mapVec (weakenTm X) idTms ≡ {!!}-}

{-# REWRITE idLem₂ idLem₃ idLem₄ #-}
