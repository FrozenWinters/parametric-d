{-# OPTIONS --without-K --rewriting #-}

module parametric where

open import lists
open import syn
open import types

double : ℕ → ℕ
double zero = zero
double (suc n) = suc (suc (double n))

evens : {n : ℕ} → Subset (double n) n
evens {zero} = done
evens {suc n} = no (yes evens)

doubleSubset₁ : {n m : ℕ} → Subset n m → Subset (double n) m
doubleSubset₁ done = done
doubleSubset₁ (yes X) = no (yes (doubleSubset₁ X))
doubleSubset₁ (no X) = no (no (doubleSubset₁ X))

doubleSubset₂ : {n m : ℕ} → Subset n m → Subset (double n) m
doubleSubset₂ done = done
doubleSubset₂ (yes X) = yes (no (doubleSubset₂ X))
doubleSubset₂ (no X) = no (no (doubleSubset₂ X))

doubleSubset₃ : {n m : ℕ} → Subset n m → Subset (double n) (double m)
doubleSubset₃ done = done
doubleSubset₃ (yes X) = yes (yes (doubleSubset₃ X))
doubleSubset₃ (no X) = no (no (doubleSubset₃ X))

double-no₁ : {n : ℕ} → doubleSubset₁ (all-no {n}) ≡ all-no
double-no₁ = all-no-lem (doubleSubset₁ all-no)

double-no₂ : {n : ℕ} → doubleSubset₂ (all-no {n}) ≡ all-no
double-no₂ = all-no-lem (doubleSubset₂ all-no)

double-no₃ : {n : ℕ} → doubleSubset₃ (all-no {n}) ≡ all-no
double-no₃ = all-no-lem (doubleSubset₃ all-no)

double-yes : {n : ℕ} → doubleSubset₃ (all-yes {n}) ≡ all-yes
double-yes {zero} = refl
double-yes {suc n} = cong yes (cong yes double-yes)

evens-comm : {n m : ℕ} (X : Subset n m) →
  trans evens X ≡ trans (doubleSubset₃ X) evens
evens-comm done = refl
evens-comm (yes X) = cong no (cong yes (evens-comm X))
evens-comm (no X) = cong no (cong no (evens-comm X))

trans-distr : {n m k : ℕ} (X : Subset n m) (Y : Subset m k) →
  doubleSubset₂ (trans X Y) ≡ trans (doubleSubset₃ X) (doubleSubset₂ Y)
trans-distr done done = refl
trans-distr (yes X) (yes Y) = cong yes (cong no (trans-distr X Y))
trans-distr (yes X) (no Y) = cong no (cong no (trans-distr X Y))
trans-distr (no X) Y = cong no (cong no (trans-distr X Y))

{-# REWRITE double-no₁ double-no₂ double-no₃ double-yes
  evens-comm trans-distr #-}

∂ : {n : ℕ} → Tm n → Tm (double n)
∂ (V v) = V (doubleSubset₂ v)
∂ (Lam E) = Lam (Lam (∂ E))
∂ (App E F) = App (App (∂ E) (weakenTm evens F)) (∂ F)

δ : {n : ℕ} → Ty n → Ty (suc (double n))
δ 𝒰 = Π (El (V (yes all-no))) 𝒰
δ (El E) = El (App (WTm (∂ E)) (V (yes all-no)))
δ (Π T S) =
  Π (WTy (weakenTy evens T))
    (Π (weakenTy (yes (no all-yes)) (δ T))
      (δ S [ W₂Tms (W₂Tms (W₁Tms idTms))
        ⊕ App (V (no (no (yes all-no)))) (V (no (yes all-no))) ]Ty))

∂-Tms : {n m : ℕ} → Tms n m → Tms (double n) (double m)
∂-Tms ! = !
∂-Tms (σ ⊕ E) = ∂-Tms σ ⊕ weakenTm evens E ⊕ ∂ E

δ-Ctx : {n : ℕ} → Ctx n → Ctx (double n)
δ-Ctx ∅ = ∅
δ-Ctx (G ⊹ T) = δ-Ctx G ⊹ weakenTy evens T ⊹ δ T

evensRen : {n : ℕ} {G : Ctx n} → Ren (δ-Ctx G) G evens
evensRen {G = ∅} = done
evensRen {G = G ⊹ A} = W₁Ren (W₂Ren (evensRen))

evensLem : {n m : ℕ} (ES : Tms n m) →
  derive (∂-Tms ES) evens ≡ mapVec (weakenTm evens) ES
evensLem ! = refl
evensLem (ES ⊕ E) = cong (_⊕ weakenTm evens E) (evensLem ES)

weaken-∂ : {n m : ℕ} (X : Subset n m) (E : Tm m) →
  ∂ (weakenTm X E) ≡ weakenTm (doubleSubset₃ X) (∂ E)
weaken-∂ X (V v) = refl
weaken-∂ X (Lam E) = cong (Lam ∘ Lam) (weaken-∂ (yes X) E)
weaken-∂ X (App E F) =
  cong₂ App
    (cong₂ App (weaken-∂ X E) refl)
    (weaken-∂ X F)

weaken-∂-Tms : {n m k : ℕ} (X : Subset n m) (ES : Tms m k) →
  ∂-Tms (mapVec (weakenTm X) ES)
    ≡ mapVec (weakenTm (doubleSubset₃ X)) (∂-Tms ES)
weaken-∂-Tms X ! = refl
weaken-∂-Tms X (ES ⊕ E) =
  cong₂ (λ G F → G ⊕ weakenTm (trans (doubleSubset₃ X) evens) E ⊕ F)
    (weaken-∂-Tms X ES) (weaken-∂ X E)

weaken-δ : {n m : ℕ} (X : Subset n m) (T : Ty m) →
  δ (weakenTy X T) ≡ weakenTy (yes (doubleSubset₃ X)) (δ T)
weaken-δ X 𝒰 = refl
weaken-δ X (El E) =
  cong (λ S → El (App (WTm S) (V (yes all-no)))) (weaken-∂ X E)
weaken-δ X (Π T S) =
  cong₂ Π
    refl
    (cong₂ Π
      (cong (weakenTy (yes (no all-yes))) (weaken-δ X T))
      (cong
        _[ W₂Tms (W₂Tms (W₁Tms idTms)) ⊕
          App (V (no (no (yes all-no)))) (V (no (yes all-no))) ]Ty
        (weaken-δ (yes X) S)))

[]-∂ : {n m : ℕ} (ES : Tms n m) (E : Tm m) →
  ∂ (E [ ES ]Tm) ≡ ∂ E [ ∂-Tms ES ]Tm

[]-σ : {n m : ℕ} (ES : Tms n m) (T : Ty m) →
  δ (T [ ES ]Ty) ≡ δ T [ W₂Tms (∂-Tms ES) ]Ty

{-# REWRITE evensLem weaken-∂ weaken-δ weaken-∂-Tms []-∂ []-σ #-}

∂-id : {n : ℕ} → ∂-Tms (idTms {n}) ≡ idTms
∂-id {zero} = refl
∂-id {suc n} = cong (W₂Tms ∘ W₂Tms) ∂-id

{-# REWRITE ∂-id #-}

doubleVar₁ : {n : ℕ} {G : Ctx n} {v : Subset n 1} {T : Ty n} →
  Var G v T → Var (δ-Ctx G) (doubleSubset₁ v) (weakenTy evens T)
doubleVar₁ 𝑧𝑣 = 𝑠𝑣 𝑧𝑣
doubleVar₁ (𝑠𝑣 v) = 𝑠𝑣 (𝑠𝑣 (doubleVar₁ v))

doubleVar₂ : {n : ℕ} {G : Ctx n} {v : Subset n 1} {T : Ty n} → Var G v T →
  Var (δ-Ctx G) (doubleSubset₂ v) (δ T [ idTms ⊕ V (trans evens v) ]Ty)
doubleVar₂ {T = T} 𝑧𝑣 = {!𝑧𝑣!}
doubleVar₂ (𝑠𝑣 v) = 𝑠𝑣 (𝑠𝑣 (doubleVar₂ v))

∂-Tms-Lem : {n m : ℕ} {G : Ctx n} {D : Ctx m} {ES : Tms n m} →
  VTms G ES D → VTms (δ-Ctx G) (∂-Tms ES) (δ-Ctx D)
δ-Ctx-Lem : {n : ℕ} {G : Ctx n} → VCtx G → VCtx (δ-Ctx G)
∂-Lem : {n : ℕ} {G : Ctx n} {E : Tm n} {T : Ty n} →
  VTm G E T → VTm (δ-Ctx G) (∂ E) (δ T [ idTms ⊕ weakenTm evens E ]Ty)
δ-Lem : {n : ℕ} {G : Ctx n} {T : Ty n} →
  VTy G T → VTy (δ-Ctx G ⊹ weakenTy evens T) (δ T)

∂-Tms-Lem ! = !
∂-Tms-Lem (σ ⊕ t) = ∂-Tms-Lem σ ⊕ weakenVTm evensRen t ⊕ ∂-Lem t

δ-Ctx-Lem ∅ = ∅
δ-Ctx-Lem (Γ ⊹ A) = δ-Ctx-Lem Γ ⊹ weakenVTy evensRen A ⊹ δ-Lem A

∂-Lem (R-Var v) = R-Var (doubleVar₂ v)
∂-Lem (R-Lam {E = E} t) = R-Lam (R-Lam {!∂-Lem t!})
∂-Lem (R-App t s) =
  R-App (R-App (∂-Lem t) (weakenVTm evensRen s)) (∂-Lem s)

δ-Lem R-Ty = R-Π (R-El (R-Var 𝑧𝑣)) R-Ty
δ-Lem (R-Π A B) =
  R-Π (weakenVTy (W₁Ren evensRen) A)
    (R-Π (weakenVTy (W₂Ren (W₁Ren idRen)) (δ-Lem A))
      (weakenVTy (W₂Ren (W₂Ren (W₂Ren (W₁Ren idRen)))) (δ-Lem B)
        [ idVTms ⊕ R-App (R-Var (𝑠𝑣 (𝑠𝑣 𝑧𝑣))) (R-Var (𝑠𝑣 𝑧𝑣)) ]VTy))
δ-Lem (R-El t) =
  R-El (R-App (weakenVTm (W₁Ren idRen) (∂-Lem t)) (R-Var 𝑧𝑣))
  
eg0 : VCtx (∅ ⊹ 𝒰 ⊹ El (V (yes done)))
eg0 = ∅ ⊹ R-Ty ⊹ R-El (R-Var 𝑧𝑣)

eg1 = δ-Ctx-Lem eg0

eg2 = δ-Ctx-Lem eg1
