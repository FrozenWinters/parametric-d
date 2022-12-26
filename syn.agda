{-# OPTIONS --without-K #-}

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

Tms : ℕ → ℕ → Set
Tms n m = Vec (Tm n) m

WTm : {n : ℕ} → Tm n → Tm (suc n)
WTm E = weakenTm (no all-yes) E

WTy : {n : ℕ} → Ty n → Ty (suc n)
WTy T = weakenTy (no all-yes) T

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
