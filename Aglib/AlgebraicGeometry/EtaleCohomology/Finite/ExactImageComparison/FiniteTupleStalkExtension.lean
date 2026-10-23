/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Finite.ExactImageComparison.FiniteComponentStalkExtension
public import Aglib.AlgebraicGeometry.EtaleCohomology.Finite.TupleStalkColimit

/-! # The original finite stalk tuple with all points in the common geometric field -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology

universe u

variable (A B Ω : Type u) [CommRing A] [CommRing B]
  [HenselianLocalRing B] [IsSepClosed (IsLocalRing.ResidueField B)]
  [Algebra B A] [Module.Finite B A]
  [Field Ω] [IsAlgClosed Ω] [Algebra (IsLocalRing.ResidueField B) Ω]
  {X : Scheme.{u}} {I : Type u} [Category.{u} I] [IsCofiltered I]
  (D : I ⥤ X.Etale) (c : Cone (D ⋙ Scheme.Etale.forget X))
  (e : Spec (.of A) ≅ c.pt.left) (F : AbelianSheaf.{u, u + 1} X)

/-- The common-field tuple retains the same actual finite-component index. -/
abbrev finiteSourceExtendedStalkTuple : AddCommGrpCat.{u + 1} :=
  AddCommGrpCat.of (∀ m : MaximalSpectrum A,
    ((pointSmallEtale (extendedFiniteComponentPoint B A Ω (e.hom ≫ c.pt.hom) m)).presheafFiber.obj
      F.obj : AddCommGrpCat.{u + 1}))

/-- Coordinatewise original point extension identifies the original residue-field
stalk tuple with the common-field tuple. -/
def finiteSourceStalkTupleExtensionIso :
    Finite.finiteSourceStalkTuple A B D c e F ≅
      finiteSourceExtendedStalkTuple A B Ω D c e F :=
  (AddEquiv.piCongrRight fun m =>
    CategoryTheory.Iso.addCommGroupIsoToAddEquiv
      ((finiteSourceComponentStalkExtension B A Ω (e.hom ≫ c.pt.hom) m).app F.obj)).toAddCommGrpIso

omit [IsCofiltered I] in
/-- The tuple comparison acts by the original point-extension map in each coordinate. -/
theorem finiteSourceStalkTupleExtensionIso_apply
    (a : Finite.finiteSourceStalkTuple A B D c e F) (m : MaximalSpectrum A) :
    (finiteSourceStalkTupleExtensionIso A B Ω D c e F).hom a m =
      (finiteSourceComponentStalkExtension B A Ω (e.hom ≫ c.pt.hom) m).hom.app F.obj (a m) :=
  rfl

end AlgebraicGeometry.Scheme.EtaleCohomology
