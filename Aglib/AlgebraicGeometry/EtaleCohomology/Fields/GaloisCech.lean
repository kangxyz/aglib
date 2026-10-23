/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Fields.AmitsurComplex
public import Aglib.AlgebraicGeometry.EtaleCohomology.Fields.FiniteGaloisCover
public import Aglib.AlgebraicGeometry.EtaleCohomology.QuasiCoherent.AmitsurProducts
public import Aglib.AlgebraicGeometry.EtaleCohomology.QuasiCoherent.EtaleSliceProducts
public import Aglib.CategoryTheory.Sites.SheafCohomology.BasisAcyclicity.TupleProducts
public import Aglib.CategoryTheory.Sites.SheafCohomology.BasisAcyclicity.UniqueCover
public import Aglib.CategoryTheory.Sites.SheafCohomology.BasisAcyclicity.CechNerveIso

/-! # Original finite-field-cover tuple cochains and Amitsur units

Every comparison below is an actual complex isomorphism: universal tuple
evaluation, original Gm restrictions, product preservation of the etale
inclusion, the unique-index projection, the native spectrum/conerve product
comparison, and the native affine global-sections counit. Thus all original
cofaces and their alternating signs are retained.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open GroupCohomology.Kummer.Coefficients
open Algebra.Amitsur

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Fields

universe u

open Scheme.FiniteEtale Scheme.FiniteEtale.FieldGalois.Arbitrary
open QuasiCoherent

variable (E L : Type u) [Field E] [Field L] [Algebra E L]
  [FiniteDimensional E L] [Algebra.IsSeparable E L]

/-- The actual finite field cover as an object of the terminal small-etale slice. -/
def galoisCoverOver : Over (StrictlyLocal.terminalObject E) :=
  Over.mk ((StrictlyLocal.terminalIsTerminal E).from
    ((toEtale _).obj (finiteFieldCover E L)))

/-- The actual field cover, regarded as a unique-index covering family. -/
def galoisCoverFamily : PUnit.{u + 2} → Over (StrictlyLocal.terminalObject E) :=
  fun _ => galoisCoverOver E L

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The scheme-slice image retains the original algebra-map spectrum. -/
def galoisCoverSchemeIso :
    (etaleSliceToScheme (StrictlyLocal.terminalObject E)).obj (galoisCoverOver E L) ≅
      (algSpec (CommRingCat.of E)).obj (op (CommAlgCat.of E L)) :=
  Over.isoMk (Iso.refl _) (by rfl)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The literal free-tuple Hom complex of the actual field cover is the original
alternating Amitsur unit complex, with its original value universe. -/
def galoisCechAmitsurIso :
    Presheaf.Cech.additiveHomComplex (Presheaf.Cech.familyMap (galoisCoverFamily E L))
      (gm (Spec (.of E))).obj ≅ amitsurUnitComplex E L := by
  let W := StrictlyLocal.terminalObject E
  let P := (Over.forget (Spec (.of E))).op ⋙ globalUnitCoefficients
  let Q := (Over.map W.hom).op ⋙ P
  let Z := (etaleSliceToScheme W).obj (galoisCoverOver E L)
  let e₁ := Presheaf.Cech.tupleHomCechIso.{u + 1, u, 0}
    (galoisCoverFamily E L) (gm (Spec (.of E))).obj
  let e₂ := (cechComplexFunctor (galoisCoverFamily E L)).mapIso
    (Functor.isoWhiskerLeft (Over.forget W).op (gmGlobalUnitsIso (Spec (.of E))))
  let e₃ := etaleSliceCechIso W (galoisCoverFamily E L) P
  let e₄ := CategoryTheory.Cech.uniqueCoverComplexIso PUnit.{u + 2} Z Q
  let e₅ := CategoryTheory.Cech.productNerveComplexIso (galoisCoverSchemeIso E L) Q
  let q := amitsurSpecCechIso E L
  let r : ((conerve E L).op ⋙ algSpec (CommRingCat.of E)).rightOp ≅
      (cechNerveTerminalFrom
        ((algSpec (CommRingCat.of E)).obj (op (CommAlgCat.of E L)))).rightOp :=
    { hom := q.inv.rightOp
      inv := q.hom.rightOp
      hom_inv_id := by rw [← NatTrans.rightOp_comp, Iso.hom_inv_id, NatTrans.rightOp_id]
      inv_hom_id := by rw [← NatTrans.rightOp_comp, Iso.inv_hom_id, NatTrans.rightOp_id] }
  let e₆ := (AlgebraicTopology.alternatingCofaceMapComplex AddCommGrpCat.{u + 1}).mapIso
    (Functor.isoWhiskerRight r Q)
  let e₇ := (AlgebraicTopology.alternatingCofaceMapComplex AddCommGrpCat.{u + 1}).mapIso
    (Functor.isoWhiskerLeft (conerve E L ⋙ forget₂ (CommAlgCat E) CommRingCat)
      affineGlobalUnitsIso)
  exact e₁ ≪≫ e₂ ≪≫ e₃ ≪≫ e₄ ≪≫ e₅ ≪≫ e₆.symm ≪≫ e₇

end AlgebraicGeometry.Scheme.EtaleCohomology.Fields
