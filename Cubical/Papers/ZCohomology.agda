{-# OPTIONS --cubical #-}
{-

Please do not move this file. Changes should only be made if
necessary.

This file contains pointers to the code examples and main results from
the paper:

Synthetic Integral Cohomology in Cubical Agda
Guillaume Brunerie, Axel Ljungström, Anders Mörtberg
Computer Science Logic (CSL) 2022

-}

-- The "--safe" flag ensures that there are no postulates or
-- unfinished goals
module Cubical.Papers.ZCohomology where

-- Misc.
open import Cubical.Data.Int hiding (_+_)
open import Cubical.Data.Nat
open import Cubical.HITs.S1
open import Cubical.Data.Sum
open import Cubical.Data.Sigma

-- 2
open import Cubical.Core.Glue                                as Glue
open import Cubical.Foundations.Prelude                      as Prelude
open import Cubical.Foundations.GroupoidLaws                 as GroupoidLaws
open import Cubical.Foundations.Isomorphism
import Cubical.Foundations.Path                              as Path
open import Cubical.Foundations.Pointed
open import Cubical.HITs.S1                                  as S1
open import Cubical.HITs.Susp                                as Suspension
open import Cubical.HITs.Sn                                  as Sn
open import Cubical.Homotopy.Loopspace                       as Loop
open import Cubical.Foundations.HLevels                      as n-types
open import Cubical.HITs.Truncation                          as Trunc
open import Cubical.Homotopy.Connected                       as Connected
import Cubical.HITs.Pushout                                  as Push
import Cubical.HITs.Wedge                                    as ⋁
import Cubical.Foundations.Univalence                        as Unival
import Cubical.Foundations.SIP                               as StructIdPrinc
import Cubical.Algebra.Group                                 as Gr
import Cubical.Algebra.Group.GroupPath                       as GrPath

-- 3
import Cubical.ZCohomology.Base                              as coHom
  renaming (coHomK to K ; coHomK-ptd to K∙)
import Cubical.HITs.Sn.Properties                            as S
import Cubical.ZCohomology.GroupStructure                    as GroupStructure
import Cubical.ZCohomology.Properties                        as Properties
  renaming (Kn→ΩKn+1 to σ ; ΩKn+1→Kn to σ⁻¹)
import Cubical.Experiments.ZCohomologyOld.Properties as oldCohom

-- 4
import Cubical.ZCohomology.RingStructure.CupProduct          as Cup
import Cubical.ZCohomology.RingStructure.RingLaws            as ⌣Ring
import Cubical.ZCohomology.RingStructure.GradedCommutativity as ⌣Comm
import Cubical.Foundations.Pointed.Homogeneous               as Homogen

-- 5
import Cubical.HITs.Torus                                    as 𝕋²
  renaming (Torus to 𝕋²)
import Cubical.HITs.KleinBottle                              as 𝕂²
  renaming (KleinBottle to 𝕂²)
import Cubical.HITs.RPn                                      as ℝP
  renaming (RP² to ℝP²)
import Cubical.ZCohomology.Groups.Sn                         as HⁿSⁿ
  renaming (Hⁿ-Sᵐ≅0 to Hⁿ-Sᵐ≅1)
import Cubical.ZCohomology.Groups.Torus                      as HⁿT²
import Cubical.ZCohomology.Groups.Wedge                      as Hⁿ-wedge
import Cubical.ZCohomology.Groups.KleinBottle                as Hⁿ𝕂²
import Cubical.ZCohomology.Groups.RP2                        as HⁿℝP²
  renaming (H¹-RP²≅0 to H¹-RP²≅1)
import Cubical.ZCohomology.Groups.CP2                        as HⁿℂP²
  renaming (CP² to ℂP² ; ℤ→HⁿCP²→ℤ to g)
  {- Remark: ℂP² is defined as the pushout S² ← TotalHopf → 1 in
  the formalisation. TotalHopf is just the total space from the Hopf
  fibration. We have TotalHopf ≃ S³, and the map TotalHopf → S²
  is given by taking the first projection. This is equivalent to the
  description given in the paper, since h : S³ → S² is given by
  S³ ≃ TotalHopf → S² -}

-- Additional material
import Cubical.Homotopy.EilenbergSteenrod                    as ES-axioms
import Cubical.ZCohomology.EilenbergSteenrodZ                as satisfies-ES-axioms
  renaming (coHomFunctor to H^~ ; coHomFunctor' to Ĥ)
import Cubical.ZCohomology.MayerVietorisUnreduced            as MayerVietoris

----- 2. HOMOTOPY TYPE THEORY IN CUBICAL AGDA -----

-- 2.1 Important notions in Cubical Agda
open Prelude using ( PathP
                   ; _≡_
                   ; refl
                   ; cong
                   ; cong₂
                   ; funExt)

open GroupoidLaws using (_⁻¹)

open Prelude using ( transport
                   ; subst
                   ; hcomp)

--- 2.2 Important concepts from HoTT/UF in Cubical Agda

-- The circle, 𝕊¹
open S1 using (S¹)

-- Suspensions
open Suspension using (Susp)

-- (Pointed) n-spheres, 𝕊ⁿ
open Sn using (S₊∙)

-- Loop spaces
open Loop using (Ω^_)

-- Eckmann-Hilton argument
Eckmann-Hilton : ∀ {ℓ} {A : Pointed ℓ} (n : ℕ) → isComm∙ ((Ω^ (suc n)) A)
Eckmann-Hilton n α β =
  transport (λ i → cong (λ x → rUnit x (~ i)) α ∙ cong (λ x → lUnit x (~ i)) β
                 ≡ cong (λ x → lUnit x (~ i)) β ∙ cong (λ x → rUnit x (~ i)) α)
        (λ i → (λ j → α (j ∧ ~ i) ∙ β (j ∧ i)) ∙ λ j → α (~ i ∨ j) ∙ β (i ∨ j))

-- n-types Note that we start indexing from 0 in the Cubical Library
-- (so (-2)-types as referred to as 0-types, (-1) as 1-types, and so
-- on)
open n-types using (isOfHLevel)

-- truncations
open Trunc using (hLevelTrunc)

-- elimination principle
open Trunc using (elim)

-- elimination principle for paths
truncPathElim : ∀ {ℓ ℓ'} {A : Type ℓ} {x y : A} (n : ℕ)
              → {B : Path (hLevelTrunc (suc n) A) ∣ x ∣ ∣ y ∣ → Type ℓ'}
              → ((q : _) → isOfHLevel n (B q))
              → ((p : x ≡ y) → B (cong ∣_∣ p))
              → (q : _) → B q
truncPathElim zero hlev ind q = hlev q .fst
truncPathElim (suc n) {B = B} hlev ind q =
  subst B (Iso.ret (Trunc.PathIdTruncIso _) q)
    (help (ΩTrunc.encode-fun ∣ _ ∣ ∣ _ ∣ q))
  where
  help : (q : _) → B (ΩTrunc.decode-fun ∣ _ ∣ ∣ _ ∣ q)
  help = Trunc.elim (λ _ → hlev _) ind

-- Connectedness
open Connected using (isConnected)

-- Pushouts
open Push using (Pushout)

-- Wedge sum
open ⋁ using (_⋁_)


-- 2.3 Univalence

-- Univalence and the ua function respectively
open Unival using (univalence ; ua)

-- Glue types
open Glue using (Glue)

-- The structure identity principle and the sip function
-- respectively
open StructIdPrinc using (SIP ; sip)

-- Groups
open Gr using (Group)

-- Isomorphic groups are path equal
open GrPath using (GroupPath)


----- 3. INTEGRAL COHOMOLOGY IN CUBICAL AGDA -----


-- 3.1 Eilenberg-MacLane spaces

-- Eilenberg-MacLane spaces Kₙ (unpointed and pointed respectively)
open coHom using (K ; K∙)

-- Proposition 7
open S using (sphereConnected)

-- Lemma 8
open S using (wedgeconFun; wedgeconLeft ; wedgeconRight)

-- restated to match the formulation in the paper
wedgeConSn' : ∀ {ℓ} (n m : ℕ) {A : (S₊ (suc n)) → (S₊ (suc m)) → Type ℓ}
            → ((x : S₊ (suc n)) (y : S₊ (suc m)) → isOfHLevel ((suc n) + (suc m)) (A x y))
            → (fₗ : (x : _) → A x (ptSn (suc m)))
            → (fᵣ : (x : _) → A (ptSn (suc n)) x)
            → (p : fₗ (ptSn (suc n)) ≡ fᵣ (ptSn (suc m)))
            → Σ[ F ∈ ((x : S₊ (suc n)) (y : S₊ (suc m)) → A x y) ]
                (Σ[ (left , right) ∈ ((x : S₊ (suc n)) → fₗ x ≡ F x (ptSn (suc m)))
                                   × ((x : S₊ (suc m)) → fᵣ x ≡ F (ptSn (suc n)) x) ]
                  p ≡ left (ptSn (suc n)) ∙ (right (ptSn (suc m))) ⁻¹)
wedgeConSn' zero zero hlev fₗ fᵣ p =
  (wedgeconFun 0 0 hlev fᵣ fₗ p)
   , ((λ x → sym (wedgeconRight 0 0 hlev fᵣ fₗ p x))
   , λ _ → refl) -- right holds by refl
   , rUnit _
wedgeConSn' zero (suc m) hlev fₗ fᵣ p =
  (wedgeconFun 0 (suc m) hlev fᵣ fₗ p)
  , ((λ _ → refl) -- left holds by refl
  , (λ x → sym (wedgeconLeft 0 (suc m) hlev fᵣ fₗ p x)))
  , lUnit _
wedgeConSn' (suc n) m hlev fₗ fᵣ p =
  (wedgeconFun (suc n) m hlev fᵣ fₗ p)
   , ((λ x → sym (wedgeconRight (suc n) m hlev fᵣ fₗ p x))
   , λ _ → refl) -- right holds by refl
   , rUnit _

-- +ₖ (addition) and 0ₖ
open GroupStructure using (_+ₖ_ ; 0ₖ)

-- -ₖ (subtraction)
open GroupStructure using (-ₖ_)

-- The function σ : Kₙ → ΩKₙ₊₁
open Properties using (σ)

-- Group laws for +ₖ
open GroupStructure using ( rUnitₖ ; lUnitₖ
                          ; rCancelₖ ; lCancelₖ
                          ; commₖ
                          ; assocₖ)

-- All group laws are equal to refl at 0ₖ
-- rUnitₖ (definitional)
0-rUnit≡refl : rUnitₖ 0 (0ₖ 0) ≡ refl
1-rUnit≡refl : rUnitₖ 1 (0ₖ 1) ≡ refl
n≥2-rUnit≡refl : {n : ℕ} → rUnitₖ (2 + n) (0ₖ (2 + n)) ≡ refl
0-rUnit≡refl = refl
1-rUnit≡refl = refl
n≥2-rUnit≡refl = refl

-- lUnitₖ (definitional)
0-lUnit≡refl : lUnitₖ 0 (0ₖ 0) ≡ refl
1-lUnit≡refl : lUnitₖ 1 (0ₖ 1) ≡ refl
n≥2-lUnit≡refl : {n : ℕ} → lUnitₖ (2 + n) (0ₖ (2 + n)) ≡ refl
0-lUnit≡refl = refl
1-lUnit≡refl = refl
n≥2-lUnit≡refl = refl

-- assocₖ (definitional)
0-assoc≡refl : assocₖ 0 (0ₖ 0) (0ₖ 0) (0ₖ 0) ≡ refl
1-assoc≡refl : assocₖ 1 (0ₖ 1) (0ₖ 1) (0ₖ 1) ≡ refl
n≥2-assoc≡refl : {n : ℕ} → assocₖ (2 + n) (0ₖ (2 + n)) (0ₖ (2 + n)) (0ₖ (2 + n)) ≡ refl
0-assoc≡refl = refl
1-assoc≡refl = refl
n≥2-assoc≡refl = refl

-- commₖ (≡ refl ∙ refl for n ≥ 2)
0-comm≡refl : commₖ 0 (0ₖ 0) (0ₖ 0) ≡ refl
1-comm≡refl : commₖ 1 (0ₖ 1) (0ₖ 1) ≡ refl
n≥2-comm≡refl : {n : ℕ} → commₖ (2 + n) (0ₖ (2 + n)) (0ₖ (2 + n)) ≡ refl
0-comm≡refl = refl
1-comm≡refl = refl
n≥2-comm≡refl = sym (rUnit refl)

-- lCancelₖ (definitional)
0-lCancel≡refl : lCancelₖ 0 (0ₖ 0) ≡ refl
1-lCancel≡refl : lCancelₖ 1 (0ₖ 1) ≡ refl
n≥2-lCancel≡refl : {n : ℕ} → lCancelₖ (2 + n) (0ₖ (2 + n)) ≡ refl
0-lCancel≡refl = refl
1-lCancel≡refl = refl
n≥2-lCancel≡refl = refl

-- rCancelₖ (≡ (refl ∙ refl) ∙ refl for n ≥ 2)
0-rCancel≡refl : rCancelₖ 0 (0ₖ 0) ≡ refl
1-rCancel≡refl : rCancelₖ 1 (0ₖ 1) ≡ refl
n≥2-rCancel≡refl : {n : ℕ} → rCancelₖ (2 + n) (0ₖ (2 + n)) ≡ refl
0-rCancel≡refl = refl
1-rCancel≡refl = refl
n≥2-rCancel≡refl i = rUnit (rUnit refl (~ i)) (~ i)

-- Proof that there is a unique h-structure on Kₙ
-- +ₖ defines an h-Structure on Kₙ
open GroupStructure using (_+ₖ_ ; 0ₖ ; rUnitₖ ; lUnitₖ ; lUnitₖ≡rUnitₖ)

-- and so does Brunerie's addition
open oldCohom using (_+ₖ_ ; 0ₖ ; rUnitₖ ; lUnitₖ ; rUnitlUnit0)

-- consequently both additions agree
open GroupStructure using (+ₖ-unique)
open oldCohom using (addLemma)
additionsAgree : (n : ℕ) → GroupStructure._+ₖ_ {n = n} ≡ oldCohom._+ₖ_ {n = n}
additionsAgree zero i x y = oldCohom.addLemma x y (~ i)
additionsAgree (suc n) i x y =
  +ₖ-unique n (GroupStructure._+ₖ_) (oldCohom._+ₖ_)
              (GroupStructure.rUnitₖ (suc n)) (GroupStructure.lUnitₖ (suc n))
              (oldCohom.rUnitₖ (suc n)) (oldCohom.lUnitₖ (suc n))
              (sym (lUnitₖ≡rUnitₖ (suc n)))
              (rUnitlUnit0 (suc n)) x y i

-- Theorem 9 (Kₙ ≃ ΩKₙ₊₁)
open Properties using (Kn≃ΩKn+1)

-- σ and σ⁻¹ are morphisms
-- (for σ⁻¹ this is proved directly without using the fact that σ is a morphism)
open Properties using (Kn→ΩKn+1-hom ; ΩKn+1→Kn-hom)

-- Lemma 10 (p ∙ q ≡ cong²₊(p,q)) for n = 1 and n ≥ 2 respectively
open GroupStructure using (∙≡+₁ ; ∙≡+₂)

-- Lemma 11 (cong²₊ is commutative) and Theorem 12 respectively
open GroupStructure using (cong+ₖ-comm ; isCommΩK)

-- 3.2 Group structure on Hⁿ(A)

-- +ₕ (addition), -ₕ and 0ₕ
open GroupStructure using (_+ₕ_ ; -ₕ_ ; 0ₕ)

-- Cohomology group structure
open GroupStructure using ( rUnitₕ ; lUnitₕ
                          ; rCancelₕ ; lCancelₕ
                          ; commₕ
                          ; assocₕ)

--- Additional material -------------------------------------------

-- Reduced cohomology, group structure
open GroupStructure using (coHomRedGroupDir)

-- Equality of unreduced and reduced cohmology
open Properties using (coHomGroup≡coHomRedGroup)
--------------------------------------------------------------------

----- 4. The Cup Product and Cohomology Ring -----
-- 4.1
-- Lemma 13
open Properties using (isOfHLevel↑∙)

-- ⌣ₖ
open Cup using (_⌣ₖ_)

-- ⌣ₖ is pointed in both arguments
open ⌣Ring using (0ₖ-⌣ₖ ; ⌣ₖ-0ₖ)

-- The cup product
open Cup using (_⌣_)

-- 4.2
-- Lemma 14
Lem14 : ∀ {ℓ} {A : Pointed ℓ} (n : ℕ) (f g : A →∙ K∙ n) → fst f ≡ fst g → f ≡ g
Lem14 n f g p = Homogen.→∙Homogeneous≡ (Properties.isHomogeneousKn n) p

-- Proposition 15
open ⌣Ring using (leftDistr-⌣ₖ ; rightDistr-⌣ₖ)

-- Lemma 16
open ⌣Ring using (assocer-helpFun≡)

-- Proposition 17
open ⌣Ring using (assoc-⌣ₖ)

-- Proposition 18
open ⌣Comm using () renaming (gradedComm'-⌣ₖ to gradedComm-⌣ₖ)

-- Ring structure on ⌣
open ⌣Ring using (leftDistr-⌣ ; rightDistr-⌣
                ; assoc-⌣ ; 1⌣
                ; rUnit⌣ ; lUnit⌣
                ; ⌣0 ; 0⌣)
open ⌣Comm using (gradedComm-⌣)

----- 5. CHARACTERIZING INTEGRAL COHOMOLOGY GROUPS -----

-- 5.1
-- Proposition 19
open HⁿSⁿ using (Hⁿ-Sⁿ≅ℤ)

-- 5.2
-- The torus
open 𝕋² using (𝕋²)

-- Propositions 20 and 21 respectively
open HⁿT² using (H¹-T²≅ℤ×ℤ ; H²-T²≅ℤ)

-- 5.3
-- The Klein bottle
open 𝕂² using (𝕂²)

-- The real projective plane
open ℝP using (ℝP²)

-- Proposition 22 and 24 respectively
-- ℤ/2ℤ is represented by Bool with the unique group structure
-- Lemma 23 is used implicitly in H²-𝕂²≅Bool
open Hⁿ𝕂² using (H¹-𝕂²≅ℤ ; H²-𝕂²≅Bool)

-- First and second cohomology groups of ℝP² respectively
open HⁿℝP² using (H¹-RP²≅1 ; H²-RP²≅Bool)

-- 5.4
-- The complex projective plane
open HⁿℂP² using (ℂP²)

-- Second and fourth cohomology groups ℂP² respectively
open HⁿℂP² using (H²CP²≅ℤ ;  H⁴CP²≅ℤ)

-- 6 Proving by computations in Cubical Agda
-- Proof of m = n = 1 case of graded commutativity (post truncation elimination):
-- Uncomment and give it a minute. The proof is currently not running very fast.

{-
open ⌣Comm using (-ₖ'^_·_ ) renaming (-ₖ'^_·_ to -ₖ^_·_)
n=m=1 : (a b : S¹)
    → _⌣ₖ_ {n = 1} {m = 1} ∣ a ∣ ∣ b ∣
     ≡ (-ₖ (_⌣ₖ_ {n = 1} {m = 1} ∣ b ∣ ∣ a ∣))
n=m=1 base base = refl
n=m=1 base (loop i) k = -ₖ (Properties.Kn→ΩKn+10ₖ _ (~ k) i)
n=m=1 (loop i) base k = Properties.Kn→ΩKn+10ₖ _ k i
n=m=1 (loop i) (loop j) k = -- This hcomp is just a simple rewriting to get paths in Ω²K₂
  hcomp (λ r → λ { (i = i0) → -ₖ Properties.Kn→ΩKn+10ₖ _ (~ k ∨ ~ r) j
                  ; (i = i1) → -ₖ Properties.Kn→ΩKn+10ₖ _ (~ k ∨ ~ r) j
                  ; (j = i0) → Properties.Kn→ΩKn+10ₖ _ (k ∨ ~ r) i
                  ; (j = i1) → Properties.Kn→ΩKn+10ₖ _ (k ∨ ~ r) i
                  ; (k = i0) →
                    doubleCompPath-filler
                      (sym (Properties.Kn→ΩKn+10ₖ _))
                      (λ j i →  _⌣ₖ_ {n = 1} {m = 1} ∣ loop i ∣ ∣ loop j ∣)
                      (Properties.Kn→ΩKn+10ₖ _)
                      (~ r) j i
                  ; (k = i1) →
                    -ₖ doubleCompPath-filler
                      (sym (Properties.Kn→ΩKn+10ₖ _))
                      (λ j i →  _⌣ₖ_ {n = 1} {m = 1} ∣ loop i ∣ ∣ loop j ∣)
                      (Properties.Kn→ΩKn+10ₖ _)
                      (~ r) i j})
        ((main
       ∙ sym (cong-∙∙ (cong (-ₖ_)) (sym (Properties.Kn→ΩKn+10ₖ _))
             (λ j i →  (_⌣ₖ_ {n = 1} {m = 1} ∣ loop i ∣ ∣ loop j ∣))
             (Properties.Kn→ΩKn+10ₖ _))) k i j)
  where
  open import Cubical.Foundations.Equiv.HalfAdjoint
  t : Iso (typ ((Ω^ 2) (K∙ 2))) ℤ
  t = compIso (congIso (invIso (Properties.Iso-Kn-ΩKn+1 1)))
       (invIso (Properties.Iso-Kn-ΩKn+1 0))

  p₁ = flipSquare ((sym (Properties.Kn→ΩKn+10ₖ _))
                      ∙∙ (λ j i →  _⌣ₖ_ {n = 1} {m = 1} ∣ loop i ∣ ∣ loop j ∣)
                      ∙∙ (Properties.Kn→ΩKn+10ₖ _))
  p₂ = (cong (cong (-ₖ_))
            ((sym (Properties.Kn→ΩKn+10ₖ _))))
                      ∙∙ (λ j i →  -ₖ (_⌣ₖ_ {n = 1} {m = 1} ∣ loop i ∣ ∣ loop j ∣))
                      ∙∙ (cong (cong (-ₖ_)) (Properties.Kn→ΩKn+10ₖ _))

  computation : Iso.fun t p₁ ≡ Iso.fun t p₂
  computation = refl

  main : p₁ ≡ p₂
  main = p₁                         ≡⟨ sym (Iso.ret t p₁) ⟩
        (Iso.inv t (Iso.fun t p₁))  ≡⟨ cong (Iso.inv t) computation ⟩
        Iso.inv t (Iso.fun t p₂)    ≡⟨ Iso.ret t p₂ ⟩
        p₂ ∎
-}

-- 𝕋² ≠ S² ∨ S¹ ∨ S¹
open HⁿT² using (T²≠S²⋁S¹⋁S¹)

-- Second "Brunerie number"
open HⁿℂP² using (g)
brunerie2 : ℤ
brunerie2 = g 1

-- Additional material (from the appendix of the preprint)
----- A. Proofs -----

-- A.2 Proofs for Section 4

-- Lemma 27
open Homogen using (→∙Homogeneous≡)

-- Lemma 28
open Homogen using (isHomogeneous→∙)

-- Lemma 29
open Properties using (isHomogeneousKn)

-- Lemma 30, parts 1-3 respectively
open Path using (sym≡flipSquare ; sym-cong-sym≡id ; sym≡cong-sym)

-- Lemma 31
open ⌣Comm using () renaming (cong-ₖ'-gen-inr to cong-ₖ-gen-inr)


-- A.3 Proofs for Section 5

-- Proposition 32
open HⁿSⁿ using (Hⁿ-Sᵐ≅1)

----- B. THE EILENBERG-STEENROD AXIOMS -----

-- B.1 The axioms in HoTT/UF

-- The axioms are defined as a record type
open ES-axioms.coHomTheory

-- Proof of the claim that the alternative reduced cohomology functor
-- Ĥ is the same as the usual reduced cohomology functor
_ : ∀ {ℓ} → satisfies-ES-axioms.H^~ {ℓ} ≡ satisfies-ES-axioms.Ĥ
_ = satisfies-ES-axioms.coHomFunctor≡coHomFunctor'

-- B.2 Verifying the axioms

-- Propositions 35 and 36.
_ : ∀ {ℓ} → ES-axioms.coHomTheory {ℓ} satisfies-ES-axioms.H^~
_ = satisfies-ES-axioms.isCohomTheoryZ


-- B.3 Characterizing Z-cohomology groups using the axioms

-- Theorem 37
open MayerVietoris.MV using ( Ker-i⊂Im-d ; Im-d⊂Ker-i
                            ; Ker-Δ⊂Im-i ; Im-i⊂Ker-Δ
                            ; Ker-d⊂Im-Δ ; Im-Δ⊂Ker-d)


----- C. BENCHMARKING COMPUTATIONS WITH THE COHOMOLOGY GROUPS -----

import Cubical.Experiments.ZCohomology.Benchmarks
