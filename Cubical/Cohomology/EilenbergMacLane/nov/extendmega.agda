{-# OPTIONS --safe --lossy-unification #-}

{-
This file contains
1. The Thom isomorphism (various related forms of it)
2. The Gysin sequence
-}
open import Cubical.Cohomology.EilenbergMacLane.Base
open import Cubical.Cohomology.EilenbergMacLane.Groups.Sn
open import Cubical.Cohomology.EilenbergMacLane.CupProduct

open import Cubical.Homotopy.EilenbergMacLane.CupProduct
open import Cubical.Homotopy.EilenbergMacLane.CupProductTensor
  renaming (_⌣ₖ_ to _⌣ₖ⊗_ ; ⌣ₖ-0ₖ to ⌣ₖ-0ₖ⊗ ; 0ₖ-⌣ₖ to 0ₖ-⌣ₖ⊗)
open import Cubical.Homotopy.Connected
open import Cubical.Homotopy.EilenbergMacLane.GradedCommTensor
  hiding (⌣ₖ-comm)
open import Cubical.Homotopy.EilenbergMacLane.GroupStructure
open import Cubical.Homotopy.EilenbergMacLane.Base
open import Cubical.Homotopy.EilenbergMacLane.Properties
open import Cubical.Homotopy.Loopspace
open import Cubical.Homotopy.Group.Base

open import Cubical.Functions.Morphism
open import Cubical.Functions.Embedding
open import Cubical.Functions.Surjection

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Transport
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Path
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Pointed.Homogeneous
open import Cubical.Foundations.Isomorphism

open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.SetTruncation as ST
open import Cubical.HITs.Truncation as TR
open import Cubical.HITs.Sn
open import Cubical.HITs.Pushout
open import Cubical.HITs.EilenbergMacLane1.Base
open import Cubical.HITs.Susp
open import Cubical.HITs.S1

open import Cubical.Data.Unit
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order hiding (eq)
open import Cubical.Data.Sigma
open import Cubical.Data.Bool hiding (_≤_)

open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.AbGroup.Base
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Ring
open import Cubical.Algebra.CommRing

open import Cubical.HITs.RPn
open import Cubical.Homotopy.EilenbergMacLane.Order2

open import Cubical.Relation.Nullary
open import Cubical.Relation.Nullary.HLevels
open import Cubical.Foundations.Function
open import Cubical.Data.Sum as ⊎
open import Cubical.Data.Empty as ⊥
open import Cubical.HITs.SmashProduct

open import Cubical.Cohomology.EilenbergMacLane.GenSmash

open import Cubical.Foundations.Univalence


open import Cubical.Cohomology.EilenbergMacLane.nov.base
open import Cubical.Cohomology.EilenbergMacLane.nov.boolcase
module Cubical.Cohomology.EilenbergMacLane.nov.extendmega where
open import Cubical.HITs.Join

open import Cubical.Functions.FunExtEquiv


module _ {ℓ  : Level} (I : RP∞' ℓ) where
  open RP' I

  data mixed-base-l (J : RP∞' ℓ) (j : fst J) (A : fst I → fst J → Type ℓ) : Type ℓ where
    inr-inr' : (f : (i : fst I) (j : fst J) → A i j) → mixed-base-l J j A
    inl' : (i : fst I) (a : A i j) (b : TotΠ (A (notI i))) → mixed-base-l J j A
    inr-inl-inl' : (p : (i : fst I) → A i j) → mixed-base-l J j A
    inr-push-inl' : (p : (i : fst I) → A i j)
                    (f : ((i : fst I) (j : fst J) → A i j))
                    (q : (i : fst I) → f i j ≡ p i)
                  → inr-inl-inl' p ≡ inr-inr' f
    push-inl-inl' : (i : fst I) (p : (i : fst I) → A i j)
                    (f : TotΠ (A (notI i))) (q : f j ≡ p (notI i))
                  → inl' i (p i) f ≡ inr-inl-inl' p
    push-inr' : (i : fst I) (a : A i j)
                (f : (i : fst I) (j : fst J) → A i j)
                (q : f i j ≡ a)
      → inl' i a (f (notI i)) ≡ inr-inr' f
    push-push' : (i : fst I) (p : (i : fst I) → A i j)
                 (f : (i : fst I) (j : fst J) → A i j)
                 (q : (i : fst I) → f i j ≡ p i)
               → Square refl
                        (inr-push-inl' p f q)
                        (push-inl-inl' i p (f (notI i)) (q (notI i)))
                        (push-inr' i (p i) f (q i))

  data mixed-base (J : RP∞' ℓ) (A : fst I → fst J → Type ℓ) : Type ℓ where
    inr-inr'' : (f : (i : fst I) (j : fst J) → A i j) → mixed-base J A
    main : (j : fst J) → mixed-base-l J j A → mixed-base J A
    coh : (j : fst J) (f : _) → main j (inr-inr' f) ≡ inr-inr'' f

  data mixed-base-f (J : RP∞' ℓ) (e : fst I ≃ fst J)
                    (A : fst I → fst J → Type ℓ)
                    (p : (i : fst I) → A i (fst e i))
                   : Type ℓ where
    incl : mixed-base J A → mixed-base-f J e A p
    inr-inl-inr'≃ : mixed-base-f J e A p
    inr-push-inr'≃ : (f : _) (q : (i : fst I) → f i (fst e i) ≡ p i)
      → inr-inl-inr'≃ ≡ incl (inr-inr'' f)
    push-inl-inr'≃ : (i : fst I) (f : TotΠ (A (notI i)))
      → f (fst e (notI i)) ≡ p (notI i)
      → incl (main (fst e i) (inl' i (p i) f)) ≡ inr-inl-inr'≃
    sqp : (i : fst I) (f : (i : fst I) (j : fst J) → A i j)
                      (q : (i : fst I) → f i (fst e i) ≡ p i)
      → Square (λ k → incl (main (fst e i) (push-inr' i (p i) f (q i) k)))
               (inr-push-inr'≃ f q)
               (push-inl-inr'≃ i (f (notI i)) (q (notI i)))
               λ k → incl (coh (fst e i) f k)

module _ {ℓ : Level} (I J : RP∞' ℓ) (A : fst I → fst J → Type ℓ) where
  open RP' I
  mixed-base-f-tot : Type ℓ
  mixed-base-f-tot =
    Σ[ e ∈ fst I ≃ fst J ]
     Σ[ p ∈ ((i : fst I) → A i (fst e i)) ]
       mixed-base-f I J e A p

  mixed-base-tot : Type ℓ
  mixed-base-tot =
    Σ[ e ∈ fst I ≃ fst J ]
     Σ[ p ∈ ((i : fst I) → A i (fst e i)) ]
       mixed-base I J A

  mixed-base-f-tot→ : mixed-base-tot → mixed-base-f-tot
  mixed-base-f-tot→ (e , p , t) = e , (p , incl t)

  ExtendMega : Type ℓ
  ExtendMega =
    Pushout
      {B = mixed-base I J A}
      {C = mixed-base-f-tot}
      (λ x → snd (snd x))
      mixed-base-f-tot→

inler : {ℓ : Level} (I : RP∞' ℓ) (A : fst I → Bool → Type ℓ)
  → (i' i : fst I) → A i' true → TotΠ (A (RP'.notI I i'))
  → joinR-gen Bool (A i)
inler I A i' =
  RP'.elimI I {B = λ i → A i' true → TotΠ (A (RP'.notI I i')) → joinR-gen Bool (A i)}
              i' (λ a b → inlR (true , a)) λ a b → inrR b

inler-ids : {ℓ : Level} (I : RP∞' ℓ) (A : fst I → Bool → Type ℓ)
  → (i' : fst I) (a : A i' true) (f : TotΠ (A (RP'.notI I i')))
  → (inler I A i' i' a f ≡ inlR (true , a))
   × (inler I A i' (RP'.notI I i') a f ≡ inrR f)
fst (inler-ids I A i' a f) k = 
  RP'.elimIβ I {B = λ i → A i' true → TotΠ (A (RP'.notI I i')) → joinR-gen Bool (A i)}
       i' (λ a b → inlR (true , a)) (λ a b → inrR b) .fst k a f
snd (inler-ids I A i' a f) k =
  RP'.elimIβ I {B = λ i → A i' true → TotΠ (A (RP'.notI I i')) → joinR-gen Bool (A i)}
       i' (λ a b → inlR (true , a)) (λ a b → inrR b) .snd k a f

inler-cohs : {ℓ : Level} (I : RP∞' ℓ) (i' : fst I) (A : fst I → Bool → Type ℓ)
  → (i : fst I)
  → Σ[ push-inl-inl* ∈ ((p : (i₃ : fst I) → A i₃ true) (f : TotΠ (A (RP'.notI I i')))
                     → (f true ≡ p (RP'.notI I i'))
                     → inler I A i' i (p i') f ≡ inlR (true , p i)) ]
       Σ[ push-inr* ∈ ((a : A i' true) (f : (i₁ : fst I) (j : Bool) → A i₁ j)
                    → f i' true ≡ a → inler I A i' i a (f (RP'.notI I i')) ≡ inrR (f i)) ]
         ((p : (i₁ : fst I) → A i₁ true) (f : (i₁ : fst I) (j : Bool) → A i₁ j)
          (q : (i₁ : fst I) → f i₁ true ≡ p i₁)
           → Square (push-inl-inl* p (f _) (q _))
                     (push-inr* (p i') f (q i'))
                     (λ _ → inler I A i' i (p i') (f (RP'.notI I i'))) -- refl
                     (push* (true , p i) (f i) (q i)))
inler-cohs I i' A =
  RP'.elimI I i'
    ((λ p f q → inler-ids I A i' (p i') f .fst)
     , (λ a f q → inler-ids I A i' a (f _) .fst ∙ push* (true , a) (f i') q)
     , λ p f q → {!!})
    {!!}

ExtendMega→Joinₗ : {ℓ : Level} (I : RP∞' ℓ) (A : fst I → Bool → Type ℓ)
  → (i : fst I)
  → mixed-base-l I (RP∞'· ℓ) true A
  → joinR-gen Bool (A i) 
ExtendMega→Joinₗ I A i (inr-inr' f) = inrR (f i)
ExtendMega→Joinₗ I A i (inl' i₁ a b) = inler I A i₁ i a b 
ExtendMega→Joinₗ I A i (inr-inl-inl' p) = inlR (true , p i)
ExtendMega→Joinₗ I A i (inr-push-inl' p f q i₁) = push* (true , p i) (f i) (q i) i₁
ExtendMega→Joinₗ I A i (push-inl-inl' i' p f q i₂) = inler-cohs I i' A i .fst p f q i₂
ExtendMega→Joinₗ I A i (push-inr' i' a f q i₂) = inler-cohs I i' A i .snd .fst a f q i₂
ExtendMega→Joinₗ I A i (push-push' i' p f q i₂ i₃) = inler-cohs I i' A i .snd .snd p f q i₃ i₂

ExtendMega→Joinₗ-whole : {ℓ : Level} (I J : RP∞' ℓ) (j : fst J) (A : fst I → fst J → Type ℓ)
  → (i : fst I)
  → Σ[ f ∈ (mixed-base-l I J j A → joinR-gen (fst J) (A i)) ]
       ((g : (i₂ : fst I) (j₁ : fst J) → A i₂ j₁) → f (inr-inr' g) ≡ inrR (g i))
ExtendMega→Joinₗ-whole I = JRP∞' λ A i → ExtendMega→Joinₗ I A i , λ _ → refl

mixed-base→ : {ℓ : Level} (I J : RP∞' ℓ) (A : fst I → fst J → Type ℓ)
  → (i : fst I)
  → mixed-base I J A
  → joinR-gen (fst J) (A i) 
mixed-base→ I J A i (inr-inr'' f) = inrR (f i)
mixed-base→ I J A i (main j x) = ExtendMega→Joinₗ-whole I J j A i .fst x
mixed-base→ I J A i (coh j f i₁) = ExtendMega→Joinₗ-whole I J j A i .snd f i₁

ExtendMega→JoinPush : {ℓ : Level} (I : RP∞' ℓ) (A : fst I → fst I → Type ℓ)
  → (p : (i₁ : fst I) → A i₁ i₁) (i : fst I)
  → mixed-base-f I I (idEquiv _) A p → joinR-gen (fst I) (A i)
ExtendMega→JoinPush I A p i (incl x) = mixed-base→ I I A i x
ExtendMega→JoinPush I A p i inr-inl-inr'≃ = inlR (i , p i)
ExtendMega→JoinPush I A p i (inr-push-inr'≃ f q i₁) = push* (i , p i) (f i) (q i) i₁
ExtendMega→JoinPush I A p i (push-inl-inr'≃ i₁ f x i₂) = {!x!}
ExtendMega→JoinPush I A p i (sqp i₁ f q i₂ i₃) = {!!}

ExtendMega→Joinₗ-whole-coh : {ℓ : Level} (I J : RP∞' ℓ) (A : fst I → fst J → Type ℓ)
  → (e : fst I ≃ fst J) (p : (i₁ : fst I) → A i₁ (fst e i₁)) (i : fst I)
  → mixed-base-f I J e A p → joinR-gen (fst J) (A i)
ExtendMega→Joinₗ-whole-coh I J A e p i x = {!!}



ExtendMega→Join : {ℓ : Level} (I J : RP∞' ℓ) (A : fst I → fst J → Type ℓ)
  → (i : fst I)
  → ExtendMega I J A
  → joinR-gen (fst J) (A i) 
ExtendMega→Join I J A i (inl x) = mixed-base→ I J A i x
ExtendMega→Join I J A i (inr (e , p , q)) = {!q!}
ExtendMega→Join I J A i (push (e , p , inr-inr'' f) i₁) = {!!}
ExtendMega→Join I J A i (push (e , p , main j x) i₁) = {!!}
ExtendMega→Join I J A i (push (e , p , coh j f i₂) i₁) = {!!}


--   ExtendMega' : ΠR-extend* I J A → ExtendMega
--   ExtendMega' (inl (i , ((j , a) , b))) = inl (main j (inl' i a b))
--   ExtendMega' (inr (inl (inl j , p))) = inl (main j (inr-inl-inl' p))
--   ExtendMega' (inr (inl (inr e , p))) = inr (e , p , inr-inl-inr'≃)
--   ExtendMega' (inr (inr x)) = inl (inr-inr'' x)
--   ExtendMega' (inr (push ((inl j , p) , f , q) i)) =
--     inl (((λ i → main j (inr-push-inl' p f q i)) ∙ coh j f) i)
--   ExtendMega' (inr (push ((inr e , p) , f , q) i)) =
--       ((λ j → inr (e , p , inr-push-inr'≃ f q j))
--      ∙ sym (push (e , p , inr-inr'' f))) i
--   ExtendMega' (push (i , inl ((inl j , p) , f , q)) k) =
--      inl (main j (push-inl-inl' i p f q k))
--   ExtendMega' (push (i , inl ((inr e , p) , f , q)) k) =
--     ((λ k → inl {!main (fst e i)!}) ∙∙ push (e , p , {!!}) ∙∙ {!push ?!}) k -- (push (e , p , inl' (fst e i) i (p i) f)
--     -- {!!} -- ∙ λ k → inr (e , p , push-inl-inr'≃ i f q k)) k
--   ExtendMega' (push (i , inr ((j , a) , f , q)) k) =
--     {!———— Boundary (wanted) —————————————————————————————————————
-- k = i0 ⊢ inl (main (fst e i) (inl' i (p i) f))
-- k = i1 ⊢ inr (e , p , inr-inl-inr'≃)!}
--     -- inl (push-inr' j i a f q k)
--   ExtendMega' (push (i , push ((inl x , p) , f , q) i₁) j) =
--     {!!} -- inl (push-push' x i p f q j i₁)
--   ExtendMega' (push (i , push ((inr e , p) , f , q) i₁) j) = {!!}
--   {-
--     hcomp (λ k →
--       λ {(j = i0) → push (e , p , inl' (fst e i) i (p i) (f (notI i))) (~ k)
--        ; (j = i1) → compPath-filler
--                       (λ j → inr (e , p , inr-push-inr'≃ f q j))
--                       (λ j → push (e , p , inr-inr' f) (~ j)) k i₁
--        ; (i₁ = i0) → compPath-filler'
--                        (push (e , p , inl' (fst e i) i (p i) (f (notI i))))
--                        (λ k → inr (e , p
--                                  , push-inl-inr'≃ i (f (notI i)) (q (notI i)) k))
--                        k j
--        ; (i₁ = i1) → push (e , p
--                      , push-inr' (fst e i) i (p i) f (q i) j) (~ k) })
--             (inr (e , p , sqp i f q j i₁))
-- -}
--   -- ExtendMegaₗ : mixed-base I J A → ΠR-extend* I J A
--   -- ExtendMegaₗ (inl' j i a b) = inl (i , ((j , a) , b))
--   -- ExtendMegaₗ (inr-inl-inl' j p) = inr (inl (inl j , p))
--   -- ExtendMegaₗ (inr-inr' f) = inr (inr f)
--   -- ExtendMegaₗ (inr-push-inl' j p f q i) =
--   --   inr (push ((inl j , p) , (f , q)) i)
--   -- ExtendMegaₗ (push-inl-inl' j i p f q i₁) =
--   --   push (i , (inl ((inl j , p) , (f , q)))) i₁
--   -- ExtendMegaₗ (push-inr' j i a f q i₁) =
--   --   push (i , (inr ((j , a) , (f , q)))) i₁
--   -- ExtendMegaₗ (push-push' j i p f q i₁ i₂) =
--   --   push (i , push (((inl j) , p) , (f , q)) i₂) i₁

--   -- ExtendMega→ΠR-extend* : ExtendMega → ΠR-extend* I J A
--   -- ExtendMega→ΠR-extend* (inl x) = ExtendMegaₗ x
--   -- ExtendMega→ΠR-extend* (inr (e , p , incl x)) = ExtendMegaₗ x
--   -- ExtendMega→ΠR-extend* (inr (e , p , inr-inl-inr'≃)) = inr (inl ((inr e) , p))
--   -- ExtendMega→ΠR-extend* (inr (e , p , inr-push-inr'≃ f q i)) =
--   --   inr (push ((inr e , p) , (f , q)) i)
--   -- ExtendMega→ΠR-extend* (inr (e , p , push-inl-inr'≃ i f x i₁)) =
--   --   push (i , (inl (((inr e) , p) , (f , x)))) i₁
--   -- ExtendMega→ΠR-extend* (inr (e , p , sqp i f q i₁ i₂)) =
--   --   push (i , (push (((inr e) , p) , (f , q)) i₂)) i₁
--   -- ExtendMega→ΠR-extend* (push (e , p , inl' j i₁ a b) i) = inl (i₁ , (j , a) , b)
--   -- ExtendMega→ΠR-extend* (push (e , p , inr-inl-inl' j p₁) i) = inr (inl (inl j , p₁))
--   -- ExtendMega→ΠR-extend* (push (e , p , inr-inr' f) i) = inr (inr f)
--   -- ExtendMega→ΠR-extend* (push (e , p , inr-push-inl' j p₁ f q i₁) i) =
--   --   inr (push ((inl j , p₁) , f , q) i₁)
--   -- ExtendMega→ΠR-extend* (push (e , p , push-inl-inl' j i₁ p₁ f q i₂) i) =
--   --   push (i₁ , inl ((inl j , p₁) , f , q)) i₂
--   -- ExtendMega→ΠR-extend* (push (e , p , push-inr' j i₁ a f q i₂) i) =
--   --   push (i₁ , inr ((j , a) , f , q)) i₂
--   -- ExtendMega→ΠR-extend* (push (e , p , push-push' j i₁ p₁ f q i₂ i₃) i) =
--   --   push (i₁ , push ((inl j , p₁) , f , q) i₃) i₂
