/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Topology.Sheaves.Cohomology.Restriction
public import Aglib.AlgebraicGeometry.Cohomology.Cech.Comparison
public import Aglib.AlgebraicGeometry.Cohomology.Modules.Scalars.Open

/-!
# Open cohomology and the actual restricted additive sheaf

The existing open `Sheaf.H'` on an ambient scheme is canonically identified
with the original `Sheaf.H` of the actual restricted additive sheaf. The
comparison uses exact extension by zero and the native Ext adjunction, then
the existing whole-space comparison. No quasicoherence, compactness,
separatedness or acyclicity premise is required.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

namespace AlgebraicGeometry.Scheme.Cohomology

universe u

/-- The actual native restriction of additive sheaves to a scheme open. -/
abbrev openAdditiveRestriction (X : Scheme.{u}) (U : X.Opens) :
    Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} ⥤
      Sheaf (Opens.grothendieckTopology U.toScheme) AddCommGrpCat.{u} :=
  U.sheafRestrict (C := AddCommGrpCat.{u})

/-- The image of the whole open subspace is the original ambient open. -/
theorem openRestriction_image_top (X : Scheme.{u}) (U : X.Opens) :
    (Topology.IsOpenEmbedding.functor (X := TopCat.of U) (Y := TopCat.of X)
      U.isOpenEmbedding).obj ⊤ = U := by
  ext x
  change (∃ y : U, y ∈ (⊤ : TopologicalSpace.Opens U) ∧ (y : X) = x) ↔ x ∈ U
  constructor
  · rintro ⟨y, _, rfl⟩
    exact y.property
  · intro hx
    exact ⟨⟨x, hx⟩, trivial, rfl⟩

/-- Actual open-Ext cohomology is original cohomology of the native restricted additive sheaf. -/
def sheafHPrimeOpenRestrictionAddEquiv (X : Scheme.{u}) (U : X.Opens)
    (A : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) (n : ℕ) :
    Sheaf.H'.{u + 1} A n U ≃+
      Sheaf.H.{u + 1} ((openAdditiveRestriction X U).obj A) n := by
  let e := (A.cohomologyPresheaf n).mapIso (eqToIso (openRestriction_image_top X U)).op
  exact e.addCommGroupIsoToAddEquiv.trans
    ((TopCat.Sheaf.cohomologyOpenRestrictionAddEquiv (X := TopCat.of X) U A n ⊤).trans
      (sheafHPrimeTopAddEquiv U.toScheme ((openAdditiveRestriction X U).obj A) n))

/-- The open restriction comparison is natural in the original additive coefficient sheaf. -/
theorem sheafHPrimeOpenRestrictionAddEquiv_naturality (X : Scheme.{u}) (U : X.Opens)
    {A B : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}}
    (φ : A ⟶ B) (n : ℕ) (x : Sheaf.H'.{u + 1} A n U) :
    sheafHPrimeOpenRestrictionAddEquiv X U B n
        (((Sheaf.cohomologyPresheafFunctor (Opens.grothendieckTopology X) n).map φ).app
          (op U) x) =
      Sheaf.H.map ((openAdditiveRestriction X U).map φ) n
        (sheafHPrimeOpenRestrictionAddEquiv X U A n x) := by
  let i := (eqToHom (openRestriction_image_top X U)).op
  have hi := congrArg (fun f => f x)
    (((Sheaf.cohomologyPresheafFunctor (Opens.grothendieckTopology X) n).map φ).naturality i)
  change ((Sheaf.cohomologyPresheafFunctor (Opens.grothendieckTopology X) n).map φ).app
      (op (U.isOpenEmbedding.functor.obj ⊤)) ((A.cohomologyPresheaf n).map i x) =
    (B.cohomologyPresheaf n).map i
      (((Sheaf.cohomologyPresheafFunctor (Opens.grothendieckTopology X) n).map φ).app
        (op U) x) at hi
  change sheafHPrimeTopAddEquiv U.toScheme ((openAdditiveRestriction X U).obj B) n
      (TopCat.Sheaf.cohomologyOpenRestrictionAddEquiv U B n ⊤
        ((B.cohomologyPresheaf n).map i
          (((Sheaf.cohomologyPresheafFunctor (Opens.grothendieckTopology X) n).map φ).app
            (op U) x))) =
    Sheaf.H.map ((openAdditiveRestriction X U).map φ) n
      (sheafHPrimeTopAddEquiv U.toScheme ((openAdditiveRestriction X U).obj A) n
        (TopCat.Sheaf.cohomologyOpenRestrictionAddEquiv U A n ⊤
          ((A.cohomologyPresheaf n).map i x)))
  rw [← hi, TopCat.Sheaf.cohomologyOpenRestrictionAddEquiv_naturality]
  exact sheafHPrimeTopAddEquiv_naturality U.toScheme
    ((openAdditiveRestriction X U).map φ) n _

/-- Restricting the actual additive module sheaf gives the additive sheaf of the native
module restriction. Its section maps are the original maps. -/
def openRestrictionModuleAddSheafIso (X : Scheme.{u}) (U : X.Opens) (M : X.Modules) :
    (openAdditiveRestriction X U).obj (moduleAddSheaf X M) ≅
      moduleAddSheaf U.toScheme (M.restrict U.ι) :=
  Iso.refl _

/-- An actual open-chart ring map commutes with restriction of global functions. -/
theorem appIso_globalRestriction {Y X : Scheme.{u}} (j : Y ⟶ X) [IsOpenImmersion j]
    (V : Y.Opens) (a : Γ(X, ⊤)) :
    (j.appIso V).hom (globalRestriction X (j ''ᵁ V) a) =
      globalRestriction Y V (j.appTop a) := by
  change (X.presheaf.map (homOfLE le_top).op ≫ (j.appIso V).hom) a =
    (j.appTop ≫ Y.presheaf.map (homOfLE le_top).op) a
  rw [Scheme.Hom.appIso_hom', Scheme.Hom.map_appLE,
    Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_map]

/-- Native additive restriction preserves the original coefficient multiplication. -/
theorem openRestrictionModule_scalar (X : Scheme.{u}) (U : X.Opens) (M : X.Modules)
    (a : Γ(X, ⊤)) :
    (openAdditiveRestriction X U).map (moduleScalarOfGlobal X M a) =
      moduleScalarOfGlobal U.toScheme (M.restrict U.ι) (U.ι.appTop a) := by
  ext V x
  change M.val.obj (op (U.ι ''ᵁ V.unop)) at x
  change globalRestriction X (U.ι ''ᵁ V.unop) a • x =
    (U.ι.appIso V.unop).inv
      (globalRestriction U.toScheme V.unop (U.ι.appTop a)) • x
  congr 1
  rw [← appIso_globalRestriction U.ι V.unop a]
  exact (ConcreteCategory.congr_hom (U.ι.appIso V.unop).hom_inv_id _).symm

/-- Native open cohomology is the original restricted-module cohomology, with the actual
structural ring actions on both sides. -/
def moduleHPrimeOpenLinearEquiv (X : Scheme.{u}) {R : Type u} [CommRing R]
    (α : R →+* Γ(X, ⊤)) (M : X.Modules) (U : X.Opens) (n : ℕ) :
    letI := moduleHPrimeModuleOfHom X α M n U
    letI := moduleCohomologyModuleOfHom U.toScheme (U.ι.appTop.hom.comp α) (M.restrict U.ι) n
    Sheaf.H'.{u + 1} (moduleAddSheaf X M) n U ≃ₗ[R]
      Sheaf.H.{u + 1} (moduleAddSheaf U.toScheme (M.restrict U.ι)) n := by
  letI := moduleHPrimeModuleOfHom X α M n U
  letI := moduleCohomologyModuleOfHom U.toScheme (U.ι.appTop.hom.comp α) (M.restrict U.ι) n
  refine {
    __ := sheafHPrimeOpenRestrictionAddEquiv X U (moduleAddSheaf X M) n
    map_smul' := fun a x => ?_ }
  change sheafHPrimeOpenRestrictionAddEquiv X U (moduleAddSheaf X M) n
      (((Sheaf.cohomologyPresheafFunctor (Opens.grothendieckTopology X) n).map
        (moduleScalarOfGlobal X M (α a))).app (op U) x) =
    Sheaf.H.map (moduleScalarOfGlobal U.toScheme (M.restrict U.ι) (U.ι.appTop (α a))) n
      (sheafHPrimeOpenRestrictionAddEquiv X U (moduleAddSheaf X M) n x)
  have h := sheafHPrimeOpenRestrictionAddEquiv_naturality X U
    (moduleScalarOfGlobal X M (α a)) n x
  rw [openRestrictionModule_scalar] at h
  exact h

end AlgebraicGeometry.Scheme.Cohomology
