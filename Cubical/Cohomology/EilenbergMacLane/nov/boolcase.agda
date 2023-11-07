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
module Cubical.Cohomology.EilenbergMacLane.nov.boolcase where
open import Cubical.HITs.Join
open import Cubical.Functions.FunExtEquiv

open import Cubical.HITs.SequentialColimit
joinSeq : (A : Type) → ℕ → Type
joinSeq A zero = A
joinSeq A (suc n) = join A (joinSeq A n)

bigT : (A : Type) → Type
bigT A = Lim→ (record { space = joinSeq A ; map = inr })

module Rewrite1 {ℓ} (I : RP∞' ℓ) (J : Type) (A : fst I → J → Type ℓ) where
  module M = 2-elter I J A
  module _ (AB : Type ℓ) (AB→J : (i : fst I) → AB → J) (AB→A : (i : fst I) (a : AB) → A i (AB→J i a))  where
    fat-ab : Type ℓ
    fat-ab = Σ[ a ∈ AB ]
             Σ[ g ∈ ((i : fst I) (j : J) → A i j) ]
               ((i : fst I) → g i (AB→J i a) ≡ AB→A i a)
    ΠR-base-ab : Type ℓ
    ΠR-base-ab = Pushout {A = fat-ab} {B = AB} {C = ((i : fst I) (j : J) → A i j)}
                         fst (fst ∘ snd)

    left-push-ab : Type _
    left-push-ab = Σ[ i ∈ fst I ] (Σ[ j ∈ J ] (A i j)) × ((j : J) → A (M.notI i) j)

    left-push↑ₗ-ab : fst I → Type _
    left-push↑ₗ-ab i = Σ[ f ∈ AB ]
      Σ[ g ∈ ((j : J) → A (M.notI i) j) ] g (AB→J (M.notI i) f) ≡ AB→A (M.notI i) f

    left-push↑ᵣ-ab : fst I → Type _
    left-push↑ᵣ-ab i = Σ[ f ∈ (Σ[ j ∈ J ] A i j) ]
        Σ[ g ∈ ((i : fst I) (j : J) → A i j) ] g i (fst f) ≡ snd f

    fat→ₗ-ab : (i : fst I) → fat-ab → left-push↑ₗ-ab i
    fat→ₗ-ab  i (f , g , r) = (f , (g (M.notI i)) , (r (M.notI i)))

    fat→ᵣ-ab : (i : fst I) → fat-ab → left-push↑ᵣ-ab i
    fat→ᵣ-ab i (f , g , r) =  (AB→J i f , AB→A i f) , g , r i

    PushTop-ab : Type _
    PushTop-ab = Σ[ i ∈ fst I ] (Pushout (fat→ₗ-ab i) (fat→ᵣ-ab i))

    AB→Σ : (i : fst I) → AB → Σ J (A i)
    fst (AB→Σ a f) = {!!}
    snd (AB→Σ a f) = {!!}

    PushTop→left-push'-ab : (i : fst I)
      → (Pushout (fat→ₗ-ab i) (fat→ᵣ-ab i))
      → (Σ[ j ∈ J ] (A i j)) × ((j : J) → A (M.notI i) j)
    PushTop→left-push'-ab i (inl (f , g , p)) = {!AB→Σ i f!} , {!!} -- (f i) , g
    PushTop→left-push'-ab i (inr (f , g , p)) = f , (g (M.notI i))
    PushTop→left-push'-ab i (push (f , g , p) k) = {!!} -- (f i) , λ j → g (M.notI i) j

--     PushTop→left-push : PushTop → left-push
--     PushTop→left-push (i , x) = (i , PushTop→left-push' i x)

--     PushTop→ΠR-base : PushTop → ΠR-base
--     PushTop→ΠR-base (i , inl (f , g , p)) = inl f
--     PushTop→ΠR-base (i , inr (f , g , p)) = inr g
--     PushTop→ΠR-base (i , push (f , g , p)  i₁) = push (f , g , p) i₁

--     ΠR-extend : Type _
--     ΠR-extend = Pushout PushTop→left-push PushTop→ΠR-base

    

--   abstract-p : Type ℓ
--   abstract-p = {!!}
-- {-
--   fat : Type _
--   fat = (Σ[ f ∈ ((i : fst I) → Σ[ j ∈ J ] A i j) ]
--           Σ[ g ∈ ((i : fst I) (j : J) → A i j) ]
--             ((i : fst I) → g i (f i .fst) ≡ f i .snd))
  
--   ΠR-base : Type _
--   ΠR-base =
--     Pushout {A = fat}
--             {B = TotΠ λ i → Σ[ j ∈ J ] (A i j)}
--             {C = (i : fst I) (j : J) → A i j}
--             fst
--             (fst ∘ snd)

--   left-push : Type _
--   left-push = Σ[ i ∈ fst I ] (Σ[ j ∈ J ] (A i j)) × ((j : J) → A (notI i) j)

--   left-push↑ₗ : fst I → Type _
--   left-push↑ₗ i = Σ[ f ∈ ((i : fst I) → Σ[ j ∈ J ] A i j) ]
--     Σ[ g ∈ ((j : J) → A (notI i) j) ] (g (f (notI i) .fst) ≡ f (notI i) .snd)

--   left-push↑ᵣ : fst I → Type _
--   left-push↑ᵣ i = Σ[ f ∈ (Σ[ j ∈ J ] A i j) ]
--       Σ[ g ∈ ((i : fst I) (j : J) → A i j) ] g i (fst f) ≡ snd f

--   fat→ₗ : (i : fst I) → fat → left-push↑ₗ i
--   fat→ₗ  i (f , g , r) = (f , (g (notI i)) , (r (notI i)))

--   fat→ᵣ : (i : fst I) → fat → left-push↑ᵣ i
--   fat→ᵣ i (f , g , r) =  f i , g , r i

--   PushTop : Type _
--   PushTop = Σ[ i ∈ fst I ] (Pushout (fat→ₗ i) (fat→ᵣ i))

--   PushTop→left-push' : (i : fst I)
--     → (Pushout (fat→ₗ i) (fat→ᵣ i))
--     → (Σ[ j ∈ J ] (A i j)) × ((j : J) → A (notI i) j)
--   PushTop→left-push' i (inl (f , g , p)) = (f i) , g
--   PushTop→left-push' i (inr (f , g , p)) = f , (g (notI i))
--   PushTop→left-push' i (push (f , g , p) k) = (f i) , λ j → g (notI i) j

--   PushTop→left-push : PushTop → left-push
--   PushTop→left-push (i , x) = (i , PushTop→left-push' i x)

--   PushTop→ΠR-base : PushTop → ΠR-base
--   PushTop→ΠR-base (i , inl (f , g , p)) = inl f
--   PushTop→ΠR-base (i , inr (f , g , p)) = inr g
--   PushTop→ΠR-base (i , push (f , g , p)  i₁) = push (f , g , p) i₁

--   ΠR-extend : Type _
--   ΠR-extend = Pushout PushTop→left-push PushTop→ΠR-base

-- -}



-- module BoolC {ℓ} (J : RP∞' ℓ) (A : Bool → fst J → Type ℓ) where
--   open 2-elter (RP∞'· ℓ) (fst J) A
--   left-push→' : left-push → joinR-gen (fst J) (A true)
--   left-push→' (false , t , f) = inrR f
--   left-push→' (true , t , f) = inlR t

--   ΠR-base→' : ΠR-base → joinR-gen (fst J) (A true)
--   ΠR-base→' (inl x) = inlR (x true)
--   ΠR-base→' (inr x) = inrR (x true)
--   ΠR-base→' (push (a , b , c) i) = push* (a true) (b true) (c true) i

--   cohs : (a : Bool) (b : Pushout (fat→ₗ a) (fat→ᵣ a))
--        → left-push→' (a , PushTop→left-push' a b) ≡ ΠR-base→' (PushTop→ΠR-base (a , b))
--   cohs false (inl (a , b , c)) = sym (push* (a true) b c) 
--   cohs false (inr x) = refl
--   cohs false (push (a , b , c) i) j = push* (a true) (b true) (c true) (i ∨ ~ j)
--   cohs true (inl (a , b , c)) = refl
--   cohs true (inr (a , b , c)) = push* a (b true) c
--   cohs true (push (a , b , c) i) j = push* (a true) (b true) (c true) (i ∧ j)

--   T : ΠR-extend → joinR-gen (fst J) (A true)
--   T (inl x) = left-push→' x
--   T (inr x) = ΠR-base→' x
--   T (push (a , b) i) = cohs a b i

--   T-alt : ΠR-extend → joinR-gen (fst J) (A true)
--   T-alt x = ΠR-extend→Π x true

--   idPL : (x : _) → left-push→' x ≡ T-alt (inl x)
--   idPL (false , b) = refl
--   idPL (true , b) = refl

--   idP : (x : ΠR-extend) → T x ≡ T-alt x
--   idP x = l x ∙ ΠR-extend→Π-alt≡ {J = J} A x true
--     where
--     l : (x : _) → T x ≡ ΠR-extend→Π-alt J A x true
--     l (inl (false , snd₁)) = refl
--     l (inl (true , snd₁)) = refl
--     l (inr (inl x)) = refl
--     l (inr (inr x)) = refl
--     l (inr (push a i)) = refl
--     l (push (false , inl x) i) = refl
--     l (push (false , inr x) i) = refl
--     l (push (false , push a i₁) i) = refl
--     l (push (true , inl x) i) = refl
--     l (push (true , inr x) i) = refl
--     l (push (true , push a i₁) i) = refl

--   module MM = 2-elter' (RP∞'· ℓ) (fst J) A

--   left-push→2 : MM.left-push → joinR-gen (fst J) (A true)
--   left-push→2 (false , a , b) = inrR b
--   left-push→2 (true , a , b) = inlR a

--   ΠR-base→2 : MM.ΠR-base → joinR-gen (fst J) (A true)
--   ΠR-base→2 (inl (inl x , b)) = inlR (x , b true)
--   ΠR-base→2 (inl (inr x , b)) = inlR ((fst x true) , (b true))
--   ΠR-base→2 (inr x) = inrR (x true)
--   ΠR-base→2 (push (inl x , b) i) = push* (x , b true x) (b true) refl i
--   ΠR-base→2 (push (inr x , b) i) = push* (fst x true , b true (fst x true)) (b true) refl i

--   coh-false : (s : _) → left-push→2 (false , MM.PushTop→left-push' false s) ≡ ΠR-base→2 (MM.PushTop→ΠR-base (false , s))
--   coh-false (inl (inl x , (a , b))) = sym (push* (x , b x) b refl)
--   coh-false (inl (inr x , (a , b))) = sym (push* (fst x true , b (fst x true)) b refl)
--   coh-false (inr x) = refl
--   coh-false (push (inl x , b) i) j = {!!}
--   coh-false (push (inr x , b) i) = {!!}

--   T-alt2 : MM.ΠR-extend → joinR-gen (fst J) (A true)
--   T-alt2 (inl x) = left-push→2 x
--   T-alt2 (inr x) = ΠR-base→2 x
--   T-alt2 (push (f , s) i) = {!s!}
  

-- -- module _ (I J : RP∞' ℓ-zero) {A : fst I → fst J → Type} where
-- --   private
-- --     GOAL = joinR-gen (fst J) λ j → joinR-gen (fst I) λ x → A x j
-- --   module IM = 2-elter' I (fst J) A
-- --   module JM = 2-elter' J (fst I) (λ x y → A y x)

-- --   extenderₗ : IM.left-push → GOAL
-- --   extenderₗ (i , (j , a) , f) = inrR (JM.elimI j (inrR (IM.elimI i a (f j))) (inlR (IM.notI i , f (JM.notI j))))

-- --   extenderᵣ : IM.ΠR-base → GOAL
-- --   extenderᵣ (inl (inl j , p)) = inlR (j , inrR p)
-- --   extenderᵣ (inl (inr e , p)) = inrR λ j → inlR ((invEq e j) , {!e!})
-- --   extenderᵣ (inr x) = inrR λ j → inrR (λ i → x i j)
-- --   extenderᵣ (push a i) = {!!}
  
-- --   extender : IM.ΠR-extend → GOAL
-- --   extender (inl x) = extenderₗ x
-- --   extender (inr x) = extenderᵣ x
-- --   extender (push (a , inl (inl x , p)) i) = {!!}
-- --   extender (push (a , inl (inr x , p)) i) = {!!}
-- --   extender (push (a , inr x) i) = {!!}
-- --   extender (push (a , push a₁ i₁) i) = {!!}

-- -- module _ (J : RP∞' ℓ-zero) {A : Bool → fst J → Type} where
-- --   open 2-elter' J Bool (λ x y → A y x)
-- --   private
-- --     GOAL = joinR-gen (fst J) λ j → joinR-gen Bool λ x → A x j

-- --   inl-inlₗ : (x : fst J) (f : A true x) (f' : A false x) → GOAL
-- --   inl-inlₗ x f f' = inlR (x , inrR (CasesBool true f f'))

-- --   inl-inlᵣ : (x : fst J) (f : A true x) (f' : A false (notI x)) → GOAL
-- --   inl-inlᵣ x f f' = inrR (elimI x (inlR (true , f)) (inlR (false , f')))

-- --   inl-inl : (x : fst J) → (A true x) → (x' : fst J) → A false x' → GOAL
-- --   inl-inl x f = elimI x (inl-inlₗ x f) (inl-inlᵣ x f)

-- --   inl-inlₗid : (x : fst J) (f : A true x) (f' : A false x) → inl-inl x f x f' ≡ inl-inlₗ x f f'
-- --   inl-inlₗid x f f' = funExt⁻ (elimIβ x (inl-inlₗ x f) (inl-inlᵣ x f) .fst) f'

-- --   inl-inlᵣid : (x : fst J) (f : A true x) (f' : A false (notI x)) → inl-inl x f (notI x) f' ≡ inl-inlᵣ x f f'
-- --   inl-inlᵣid x f f' = funExt⁻ (elimIβ x (inl-inlₗ x f) (inl-inlᵣ x f) .snd) f'

-- --   inl-pushₗ : (x : fst J) (f : A true x) (f' : A false x) (b : TotΠ (A false)) (x₁ : b x ≡ f')
-- --            → inl-inl x f x f'
-- --             ≡ inrR (elimI x (inrR (CasesBool true f (b x))) (inlR (false , b (notI x))))
-- --   inl-pushₗ x f f' b x₁ =
-- --       inl-inlₗid x f f'
-- --     ∙ push* (x , inrR (CasesBool true f f'))
-- --             _
-- --             (elimIβ x (inrR (CasesBool true f (b x)))
-- --                       (inlR (false , b (notI x))) .fst
-- --           ∙ λ i → inrR (CasesBool true f (x₁ i)))



-- --   inl-pushᵣ : (x : fst J) (f : A true x) (f' : A false (notI x)) (b : TotΠ (A false)) (x₁ : b (notI x) ≡ f')
-- --            → inl-inl x f (notI x) f'
-- --             ≡ inrR (elimI x (inrR (CasesBool true f (b x))) (inlR (false , b (notI x))))
-- --   inl-pushᵣ x f f' b x₁ =
-- --       inl-inlᵣid x f f'
-- --     ∙ cong inrR (funExt (elimI x (elimIβ x (inlR (true , f)) (inlR (false , f')) .fst
-- --                               ∙∙ push* (true , f) (CasesBool true f (b x)) refl
-- --                               ∙∙ sym (elimIβ x (inrR (CasesBool true f (b x))) (inlR (false , b (notI x))) .fst))
-- --                                  (elimIβ x (inlR (true , f)) (inlR (false , f')) .snd
-- --                                ∙∙ (λ j → inlR (false , x₁ (~ j)))
-- --                                ∙∙ sym (elimIβ x (inrR (CasesBool true f (b x))) (inlR (false , b (notI x))) .snd))))

-- --   inl-push : (x : fst J) (f : A true x) (x' : fst J) (f' : A false x') (b : TotΠ (A false)) (x₁ : b x' ≡ f')
-- --     → inl-inl x f x' f'
-- --      ≡ inrR (elimI x (inrR (CasesBool true f (b x))) (inlR (false , b (notI x))))
-- --   inl-push x f = elimI x (inl-pushₗ x f) (inl-pushᵣ x f)

-- --   ×→Goal : (x : joinR-gen (fst J) (A true) × joinR-gen (fst J) (A false))
-- --          → GOAL
-- --   ×→Goal (inlR (x , f) , inlR (x' , f')) = inl-inl x f x' f'
-- --   ×→Goal (inlR (x , f) , inrR y) = inrR (elimI x (inrR (CasesBool true f (y x))) (inlR (false , y (notI x))))
-- --   ×→Goal (inlR (j , f) , push* (j' , f') b x₁ i) = inl-push j f j' f' b x₁ i
-- --   ×→Goal (inrR x , inlR x₁) = {!!}
-- --   ×→Goal (inrR x , inrR x₁) = inrR λ j → inrR (CasesBool true (x j) (x₁ j))
-- --   ×→Goal (inrR x , push* a b x₁ i) = {!!}
-- --   ×→Goal (push* a b₁ x i , b) = {!!}

-- --   ⊎→Goal : joinR-gen (fst J) (A true) → GOAL
-- --   ⊎→Goal (inlR (j , a)) = inlR (j , inlR (true , a))
-- --   ⊎→Goal (inrR f) = inrR λ j → inlR (true , f j)
-- --   ⊎→Goal (push* a b x i) = push* (fst a , inlR (true , snd a)) (λ i → inlR (true , b i)) (λ i → inlR (true , x i)) i

-- --   coher : (f : _) → ×→Goal f ≡ ⊎→Goal (fst f)
-- --   coher f = {!f!}

-- --   LType : {!!}
-- --   LType = {!!}

-- -- module final {J : RP∞' ℓ-zero}
-- --          (main-fun : (I : RP∞' ℓ-zero) → {A : fst I → fst J → Type}
-- --                    → TotΠ (λ i → joinR-gen (typ J) (A i))
-- --                    → (joinR-gen (fst J) λ j → joinR-gen (fst I) λ i → A i j))
-- --          (main-fun-id : {A : Bool → fst J → Type}
-- --                      → (x : joinR-gen (fst J) (A true) × joinR-gen (fst J) (A false))
-- --                      → main-fun (RP∞'· ℓ-zero) {A = A} (Iso.inv ΠBool×Iso x)
-- --                       ≡ ×→Goal J x) where

-- --   mainₗ : (I : RP∞' ℓ-zero) (i : fst I) (A : fst I → fst J → Type)
-- --     → joinR-gen (fst J) (A i)
-- --     → joinR-gen (fst J) λ j → joinR-gen (fst I) λ i → A i j
-- --   mainₗ = JRP∞' λ A → ⊎→Goal J

-- --   mainₗ≡ : (A : _) → mainₗ (RP∞'· ℓ-zero) true A ≡ ⊎→Goal J
-- --   mainₗ≡ = funExt⁻ (JRP∞'∙ (λ A → ⊎→Goal J))

-- --   main : (I : RP∞' ℓ-zero) (A : fst I → fst J → Type)
-- --     → (joinR-gen (fst I) λ i → joinR-gen (fst J) (A i))
-- --     → joinR-gen (fst J) λ j → joinR-gen (fst I) λ i → A i j 
-- --   main I A (inlR (i , j)) = mainₗ I i A j
-- --   main I A (inrR x) = main-fun I x
-- --   main I A (push* (i , a) b x k) = help I i b a x k
-- --     where
-- --     help : (I : RP∞' ℓ-zero) (i : fst I) {A : fst I → fst J → Type}
-- --            (b : (i₁ : fst I) → joinR-gen (fst J) (A i₁))
-- --          → (a : joinR-gen (fst J) (A i)) 
-- --          → b i ≡ a
-- --          → mainₗ I i A a ≡ main-fun I b 
-- --     help = JRP∞' λ {A} → λ f → J> funExt⁻ (mainₗ≡ A) (f true)
-- --                                ∙ sym (coher J (f true , f false))
-- --                                ∙ sym (main-fun-id {A} (f true , f false))
-- --                                ∙ cong (main-fun (RP∞'· ℓ-zero))
-- --                                       (funExt λ { false → refl
-- --                                                 ; true → refl})


-- -- joinGen : ∀ {ℓ} (I : Type ℓ)(A : I → Type ℓ) → Type ℓ
-- -- joinGen I A = Pushout {A = I × TotΠ A} {B = Σ I A} (λ fi → (fst fi , snd fi (fst fi))) snd

-- -- join-funct : ∀ {ℓ} (I : Type ℓ) {A B : I → Type ℓ} (f : (i : I) → A i → B i) → joinGen I A → joinGen I B
-- -- join-funct I f (inl x) = inl (fst x , f (fst x) (snd x))
-- -- join-funct I f (inr x) = inr (λ k → f k (x k))
-- -- join-funct I f (push (i , g) k) = push (i , (λ x → f x (g x))) k

-- -- JoinEqFunct : ∀ {ℓ} (I J : Type ℓ) {A : I → J → Type ℓ}
-- --   → joinGen (I ≃ J) (λ e → joinGen J λ j → A (invEq e j) j)
-- --   → joinGen (I ≃ J) (λ e → joinGen I λ i → A i (fst e i))
-- -- JoinEqFunct {ℓ} I J {A = A} = join-funct (I ≃ J)
-- --   λ e → EquivJ (λ I e → (A : I → J → Type ℓ) → (joinGen J λ j → A (invEq e j) j)
-- --       → joinGen I λ i → A i (fst e i)) (λ A → idfun _) e A


-- -- module _ {ℓ} (I J : Type ℓ) {A : I → J → Type ℓ} (mk : (i : I) (j : J) → Σ[ e ∈ I ≃ J ] (fst e i ≡ j)) where
-- --   JoinEq'* :
-- --       (joinGen (I ≃ J) (λ e → joinGen J λ j → A (invEq e j) j))
-- --     → (joinGen I λ i → joinGen J λ j → A i j)
-- --   JoinEq'* (inl (e , t)) = {!!}
-- --   JoinEq'* (inr e) = inr λ i → {!!}
-- --   JoinEq'* (push (e , t) i) = {!!}
  

-- --   JoinEq' : (joinGen I λ i → joinGen J λ j → A i j)
-- --     → joinGen (I ≃ J) (λ e → joinGen J λ j → A (invEq e j) j)
-- --   JoinEq' (inl (i , inl (j , t))) = inl (mk i j .fst , inl (j , subst (λ k → A k j) {!snd (mk i j)!} t))
-- --   JoinEq' (inl (i , inr x)) = inr λ e → inl (fst e i , subst (λ k → A k (fst e i)) (sym (retEq e i)) (x (fst e i)))
-- --   JoinEq' (inl (i , push a i₁)) = {!!}
-- --   JoinEq' (inr x) = {!!}
-- --     where
-- --     s : (e : I ≃ J) (j : _) → joinGen J (λ j₁ → A (invEq e j) j₁) → A (invEq e j) j
-- --     s e j (inl x) = {!snd x!}
-- --     s e j (inr x) = x j
-- --     s e j (push a i) = {!!}
-- --   JoinEq' (push (e , t) i) = {!!}
