/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.TrivialCoverFunctor

/-! Natural comparison between finite trivial covers and constant sheaves.
The comparison factors through actual sheafification. -/

@[expose] public section

noncomputable section
set_option autoImplicit false

open _root_.CategoryTheory _root_.CategoryTheory.Limits AlgebraicGeometry Opposite

namespace AlgebraicGeometry.Scheme.FiniteEtale

universe u

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The natural map from finite constant presheaves to the section presheaves of the
corresponding trivial covers. -/
def trivialCoverConstantPresheafNatTrans (X : Scheme.{u}) :
    FintypeCat.incl ⋙ uliftFunctor.{u + 1} ⋙ Functor.const X.Etaleᵒᵖ ⟶
      trivialCoverFunctor X ⋙ finiteCoverSectionSheafFunctor X ⋙
        sheafToPresheaf (Scheme.smallEtaleTopology X) (Type (u + 1)) where
  app A := constantTrivialPresheafMap X A
  naturality {A B} f := by
    ext U a
    apply ULift.ext
    apply Over.OverMorphism.ext
    change U.unop.hom ≫ (trivialCoverι X B (f a.down)).hom.left =
      (U.unop.hom ≫ (trivialCoverι X A a.down).hom.left) ≫ (trivialCoverMap X f).hom.left
    rw [Category.assoc]
    exact (congrArg (fun k : terminalCover X ⟶ trivialCover X B => U.unop.hom ≫ k.hom.left)
      (trivialCoverι_map X f a.down)).symm

/-- The natural map from finite constant sheaves to the section sheaves of trivial covers,
obtained by sheafifying the presheaf comparison. -/
def trivialCoverConstantSheafNatTrans (X : Scheme.{u}) :
    FintypeCat.incl ⋙ uliftFunctor.{u + 1} ⋙
        constantSheaf (Scheme.smallEtaleTopology X) (Type (u + 1)) ⟶
      trivialCoverFunctor X ⋙ finiteCoverSectionSheafFunctor X :=
  Functor.whiskerRight (trivialCoverConstantPresheafNatTrans X)
      (presheafToSheaf (Scheme.smallEtaleTopology X) (Type (u + 1))) ≫
    Functor.whiskerLeft (trivialCoverFunctor X ⋙ finiteCoverSectionSheafFunctor X)
      (sheafificationAdjunction (Scheme.smallEtaleTopology X) (Type (u + 1))).counit

instance trivialCoverConstantSheafNatTrans_app_isIso (X : Scheme.{u}) (A : FintypeCat.{u}) :
    IsIso ((trivialCoverConstantSheafNatTrans X).app A) := by
  change IsIso (trivialCoverConstantIso X A).inv
  infer_instance

instance trivialCoverConstantSheafNatTrans_isIso (X : Scheme.{u}) :
    IsIso (trivialCoverConstantSheafNatTrans X) :=
  NatIso.isIso_of_isIso_app _

/-- Genuine Yoneda/constant-sheaf natural isomorphism on finite labels. -/
def trivialCoverConstantNatIso (X : Scheme.{u}) :
    trivialCoverFunctor X ⋙ finiteCoverSectionSheafFunctor X ≅
      FintypeCat.incl ⋙ uliftFunctor.{u + 1} ⋙
        constantSheaf (Scheme.smallEtaleTopology X) (Type (u + 1)) :=
  (asIso (trivialCoverConstantSheafNatTrans X)).symm

end AlgebraicGeometry.Scheme.FiniteEtale

/- Migration source: the R5Lab/Aglib mirror; exact module in the migration record.
R5 revision c82abf3a72ce1e1cedf4a4f1fe08bea994ad4df5.
SHA256 316ea6cee24ed8493c3dd7e04edfcc302a757bbc19ce27273d8cc50ac63b9468.
Definitions, hypotheses and universes are retained modulo native names. -/
