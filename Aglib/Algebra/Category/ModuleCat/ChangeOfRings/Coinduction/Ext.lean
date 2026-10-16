/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.ChangeOfRings.Coinduction
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.SingleHomology
public import Mathlib.CategoryTheory.Abelian.Injective.Ext
public import Mathlib.Algebra.Category.ModuleCat.EnoughInjectives

/-!
# Homology of native derived coinduction and original Ext

The underlying additive cochain complex of the original scalar coinduction
is the native Hom complex from the restricted regular target ring. Its
component is the actual linear map, viewed as a cochain from degree zero.
The original forgetful homology comparison, native Hom-complex cohomology
classes and supplied injective resolution then identify its homology with
native Ext. This also computes homology of the installed D+ right-derived
functor at the original degree-zero single.

Both rings and module carriers have the same universe, as in the quotient
Ext consumer. Ext and the two supplied derived-category sizes remain
independent. The rings need not be commutative, and no flatness, regularity
or finiteness premise is used. These equivalences are additive; identifying
the target-ring action with Yoneda source multiplication is a separate
normalization needed for quotient-linear purity.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open HomologicalComplex CochainComplex CochainComplex.HomComplex
noncomputable section
universe u w
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace ModuleCat
variable {R S : Type u} [Ring R] [Ring S] (σ : R →+* S)

/-- The original coinduced linear map is the actual cochain from the restricted target ring. -/
def coextendScalarsCochainEquiv (K : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ) :
    (coextendScalars σ).obj (K.X n) ≃+
      Cochain ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj
        ((restrictScalars σ).obj (ModuleCat.of S S))) K n :=
  let e : (coextendScalars σ).obj (K.X n) ≃+
      (((restrictScalars σ).obj (ModuleCat.of S S)) ⟶ K.X n) :=
      {toFun := fun f => ModuleCat.ofHom
          (X := (restrictScalars σ).obj (ModuleCat.of S S)) (Y := K.X n)
          ((CoextendScalars.equiv σ (K.X n)) f)
       invFun := fun f => (CoextendScalars.equiv σ (K.X n)).symm f.hom
       left_inv := fun _ => rfl
       right_inv := fun _ => rfl
       map_add' := fun _ _ => rfl}
  e.trans (Cochain.fromSingleEquiv (zero_add n)).symm

/-- The cochain comparison retains the original linear map on every component. -/
theorem coextendScalarsCochainEquiv_apply
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ)
    (x : (coextendScalars σ).obj (K.X n)) :
    coextendScalarsCochainEquiv σ K n x =
      Cochain.fromSingleMk
        (ModuleCat.ofHom (X := (restrictScalars σ).obj (ModuleCat.of S S)) (Y := K.X n)
          ((CoextendScalars.equiv σ (K.X n)) x)) (zero_add n) := rfl

/-- Underlying additive coinduction is the native Hom complex, with its original differential. -/
def coextendScalarsHomComplexIso (K : CochainComplex (ModuleCat.{u} R) ℤ) :
    (((coextendScalars σ) ⋙ forget₂ (ModuleCat S) AddCommGrpCat).mapHomologicalComplex
      (.up ℤ)).obj K ≅
      HomComplex ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj
        ((restrictScalars σ).obj (ModuleCat.of S S))) K :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => (coextendScalarsCochainEquiv σ K n).toAddCommGrpIso)
    (by
      intro i j hij
      ext x
      change δ i j (coextendScalarsCochainEquiv σ K i x) =
        coextendScalarsCochainEquiv σ K j ((coextendScalars σ).map (K.d i j) x)
      rw [coextendScalarsCochainEquiv_apply, Cochain.δ_fromSingleMk,
        coextendScalarsCochainEquiv_apply]
      rfl)

variable [HasExt.{w} (ModuleCat.{u} R)]

/-- The supplied original injective resolution computes coinduction homology
as native Ext. -/
def coextendScalarsResolutionExtAddEquiv {M : ModuleCat.{u} R}
    (I : InjectiveResolution M) (n : ℕ) :
    (((coextendScalars σ).mapHomologicalComplex (.up ℤ)).obj I.cochainComplex).homology
      (n : ℤ) ≃+
      Ext.{w} ((restrictScalars σ).obj (ModuleCat.of S S)) M n := by
  let K := ((coextendScalars σ).mapHomologicalComplex (.up ℤ)).obj I.cochainComplex
  let U := forget₂ (ModuleCat.{u} S) AddCommGrpCat
  let e₁ : U.obj (K.homology (n : ℤ)) ≅
      ((U.mapHomologicalComplex (.up ℤ)).obj K).homology (n : ℤ) :=
    ((K.sc (n : ℤ)).mapHomologyIso U).symm
  let e₂ := (homologyFunctor AddCommGrpCat (.up ℤ) (n : ℤ)).mapIso
    (coextendScalarsHomComplexIso σ I.cochainComplex)
  exact e₁.addCommGroupIsoToAddEquiv.trans
    (e₂.addCommGroupIsoToAddEquiv.trans
      ((HomComplex.homologyAddEquiv _ _ (n : ℤ)).trans
        I.extAddEquivCohomologyClass.symm))

/-- Native higher right-derived coinduction has the original Ext group
as its additive carrier. -/
def coextendScalarsRightDerivedExtAddEquiv (M : ModuleCat.{u} R)
    (I : InjectiveResolution M) (n : ℕ) :
    ((coextendScalars σ).rightDerived n).obj M ≃+
      Ext.{w} ((restrictScalars σ).obj (ModuleCat.of S S)) M n :=
  (I.isoRightDerivedObjCochain (coextendScalars σ) n).toLinearEquiv.toAddEquiv.trans
    (coextendScalarsResolutionExtAddEquiv σ I n)

universe a b
variable [HasDerivedCategory.{a} (ModuleCat.{u} R)]
  [HasDerivedCategory.{b} (ModuleCat.{u} S)]

/-- Homology of the installed D+ coinduction at the original single computes the same native Ext. -/
def derivedCoextendScalarsPlusHomologyExtAddEquiv (M : ModuleCat.{u} R)
    (I : InjectiveResolution M) (n : ℕ) :
    (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} S) (n : ℤ)).obj
      ((coextendScalars σ).rightDerivedFunctorPlus.obj
        ((DerivedCategory.Plus.singleFunctor (ModuleCat.{u} R) 0).obj M)) ≃+
      Ext.{w} ((restrictScalars σ).obj (ModuleCat.of S S)) M n :=
  (I.isoRightDerivedSingleHomology (coextendScalars σ) n).symm.toLinearEquiv.toAddEquiv.trans
      (coextendScalarsRightDerivedExtAddEquiv σ M I n)

end ModuleCat
