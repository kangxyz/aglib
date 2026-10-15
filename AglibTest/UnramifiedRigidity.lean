/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.RingTheory.Unramified.Rigidity
public import Aglib.AlgebraicGeometry.Morphisms.FormallyUnramified.SectionRigidity

/-! # Clients of the two general unramified-rigidity interfaces -/
@[expose] public section

set_option autoImplicit false
set_option warningAsError true
set_option linter.mathlibStandardSet true

noncomputable section
open CategoryTheory AlgebraicGeometry
universe u v w

namespace AglibTest.UnramifiedRigidity

/-- Prime reduction determines maps into a domain without a nilpotent-ideal premise. -/
example {R : Type u} {A : Type v} {B : Type w}
    [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B] [IsDomain B]
    [Algebra.EssFiniteType R A] [Algebra.FormallyUnramified R A]
    (Q : Ideal B) [Q.IsPrime] (f g : A →ₐ[R] B)
    (hfg : ∀ a, Ideal.Quotient.mk Q (f a) = Ideal.Quotient.mk Q (g a)) : f = g :=
  Algebra.FormallyUnramified.eq_of_comp_mkQ_eq Q f g hfg

/-- Section rigidity needs no finite/etale hypothesis on the target map or reduced parameter. -/
example {X Y Z T : Scheme.{u}} (p : X ⟶ Y)
    [IsSeparated p] [FormallyUnramified p] [LocallyOfFiniteType p]
    (q : Z ⟶ T) [GeometricallyConnected q]
    (s : T ⟶ Z) (hs : s ≫ q = 𝟙 T)
    (f g : Z ⟶ X) (hfg : f ≫ p = g ≫ p) (hsection : s ≫ f = s ≫ g) : f = g :=
  Scheme.Hom.eq_of_comp_eq_of_section p q s hs f g hfg hsection

end AglibTest.UnramifiedRigidity
