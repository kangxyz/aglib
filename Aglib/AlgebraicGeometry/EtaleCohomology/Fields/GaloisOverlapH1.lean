/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Fields.GaloisCechCover
public import Aglib.CategoryTheory.Sites.SheafCohomology.ModuleCoefficients.UniqueFamily

/-! # Original degree-one Ext of the actual field-cover resolution

Unique-family and universal-tuple isomorphisms identify the original free
resolution term with the original overlap representable. The actual Artinian
scheme and original slice/Picard comparison then kill its degree-one Ext.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open CategoryTheory.Sheaf.Hypercohomology
open GroupCohomology.Kummer.Coefficients

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Fields

universe u w₁

variable (E L : Type u) [Field E] [Field L] [Algebra E L]
  [FiniteDimensional E L] [Algebra.IsSeparable E L]

attribute [local instance] hasSheafifyLarge

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The literal sheafified free tuple term is the original overlap representable. -/
def galoisCechFreeIso (n : ℕ) :
    (Presheaf.Cech.sheafComplex (Presheaf.Cech.familyMap (galoisCoverFamily E L))
      (Scheme.smallEtaleTopology (Spec (.of E)))).X n ≅
        freeAbelianSheaf.{u + 1} (Scheme.smallEtaleTopology (Spec (.of E)))
          (∏ᶜ fun _ : Fin (n + 1) => galoisCoverOver E L).left :=
  Presheaf.Cech.sheafComplexUniqueFamilyIso PUnit.{u + 2}
    (Scheme.smallEtaleTopology (Spec (.of E))) (galoisCoverOver E L) n

variable [HasExt.{w₁} (AbelianSheaf.{u, u + 1} (Spec (.of E)))]

/-- Degree-one Ext of the actual first free-resolution term vanishes. -/
theorem galoisCech_ext_one_eq_zero
    (β : Ext.{w₁}
      ((Presheaf.Cech.sheafComplex (Presheaf.Cech.familyMap (galoisCoverFamily E L))
        (Scheme.smallEtaleTopology (Spec (.of E)))).X 1) (gm (Spec (.of E))) 1) : β = 0 := by
  let e := (((extFunctor 1).mapIso (galoisCechFreeIso E L 1).op).app
    (gm (Spec (.of E)))).addCommGroupIsoToAddEquiv
  exact e.symm.injective
    ((subsingleton_ext_one_gm_of_isArtinianScheme.{u, w₁}
      (∏ᶜ fun _ : Fin 2 => galoisCoverOver E L).left).elim _ _)

end AlgebraicGeometry.Scheme.EtaleCohomology.Fields
