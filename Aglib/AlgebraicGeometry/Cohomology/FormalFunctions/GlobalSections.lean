/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.FormalFunctions.Affine
public import Aglib.AlgebraicGeometry.Cohomology.DirectImage.ResolutionSections
public import Aglib.Algebra.Category.ModuleCat.NatTowerExactUniverses

/-! # Degree-zero formal functions on original global sections

This comparison uses the original coefficient reductions. Its target is an
ambient inverse tower, not an assumed compatible adic module system.
The base ring is Noetherian but is not required to be complete.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme.Cohomology

universe u
variable {A : Type u} [CommRing A] (X : Scheme.{u}) (α : A →+* Γ(X, ⊤))
  (F : X.Modules) (I : Ideal A)

/-- Degree zero expressed with the actual global-sections functor as object head. -/
def moduleH0GlobalSectionsEquiv :
    (moduleCohomologyFunctorOfHom X α 0).obj F ≃ₗ[A]
      (moduleGlobalSectionsFunctorOfHom X α).obj F :=
  moduleH0EquivOfHom X α F

/-- Actual global sections of the original quotient sheaves and transition maps. -/
abbrev idealPowerQuotientGlobalSections : ℕᵒᵖ ⥤ ModuleCat.{u} A :=
  idealPowerQuotientFunctor X α F I ⋙ moduleGlobalSectionsFunctorOfHom X α

/-- The native degree-zero equivalence on the original whole inverse family.
It allows the cohomology and section carrier universes to differ. -/
def idealPowerH0SectionsEquiv :
    ModuleCat.sectionsSubmodule (idealPowerQuotientCohomology X α F I 0) ≃ₗ[A]
      ModuleCat.sectionsSubmodule (idealPowerQuotientGlobalSections X α F I) where
  toFun s := ⟨fun j => moduleH0EquivOfHom X α _ (s.val j), by
    intro j k a
    change (Modules.idealPowerQuotientMap X α F I (leOfHom a.unop)).app ⊤
      (moduleH0EquivOfHom X α _ (s.val j)) = moduleH0EquivOfHom X α _ (s.val k)
    exact (Sheaf.H.equiv₀_naturality CategoryTheory.Limits.isTerminalTop
      ((SheafOfModules.toSheaf X.ringCatSheaf).map
        (Modules.idealPowerQuotientMap X α F I (leOfHom a.unop))) (s.val j)).trans
          (congrArg (moduleH0EquivOfHom X α _) (s.property a))⟩
  invFun s := ⟨fun j => (moduleH0EquivOfHom X α _).symm (s.val j), by
    intro j k a
    change moduleCohomologyMapOfHom X α
      (Modules.idealPowerQuotientMap X α F I (leOfHom a.unop)) 0
      ((moduleH0EquivOfHom X α _).symm (s.val j)) =
        (moduleH0EquivOfHom X α _).symm (s.val k)
    exact (Sheaf.H.equiv₀_symm_naturality CategoryTheory.Limits.isTerminalTop
      ((SheafOfModules.toSheaf X.ringCatSheaf).map
        (Modules.idealPowerQuotientMap X α F I (leOfHom a.unop))) (s.val j)).trans
          (congrArg (moduleH0EquivOfHom X α _).symm (s.property a))⟩
  left_inv s := by
    apply Subtype.ext
    funext j
    exact (moduleH0EquivOfHom X α _).symm_apply_apply (s.val j)
  right_inv s := by
    apply Subtype.ext
    funext j
    exact (moduleH0EquivOfHom X α _).apply_symm_apply (s.val j)
  map_add' s t := by
    apply Subtype.ext
    funext j
    exact (moduleH0EquivOfHom X α _).map_add (s.val j) (t.val j)
  map_smul' r s := by
    apply Subtype.ext
    funext j
    exact (moduleH0EquivOfHom X α _).map_smul r (s.val j)

variable [IsNoetherianRing A] {X}
  (f : X ⟶ Spec (CommRingCat.of A)) [IsProper f]
  (hF : Modules.QuasiCoherent.affineLocallyFiniteType X F)

/-- Proper degree-zero formal functions for the original global section module. -/
def moduleGlobalSectionsFormalFunctionsEquiv :
    AdicCompletion I ((moduleGlobalSectionsFunctorOfHom X
      (affineFormalFunctionsScalar f)).obj F) ≃ₗ[A]
      ModuleCat.sectionsSubmodule
        (idealPowerQuotientGlobalSections X (affineFormalFunctionsScalar f) F I) := by
  exact ((AdicCompletion.congr I
    (moduleH0GlobalSectionsEquiv X (affineFormalFunctionsScalar f) F).symm).restrictScalars A).trans
      ((moduleCohomologyFormalFunctionsEquiv I f F hF 0).trans
        (idealPowerH0SectionsEquiv X (affineFormalFunctionsScalar f) F I))

/-- The comparison retains every original quotient map on original sections. -/
theorem moduleGlobalSectionsFormalFunctionsEquiv_of
    (x : (moduleGlobalSectionsFunctorOfHom X (affineFormalFunctionsScalar f)).obj F)
    (n : ℕ) :
    (moduleGlobalSectionsFormalFunctionsEquiv F I f hF (AdicCompletion.of I _ x)).val
        (op n) =
      (Modules.idealQuotientπ X (affineFormalFunctionsScalar f) F (I ^ n)).app ⊤ x := by
  change moduleH0EquivOfHom X (affineFormalFunctionsScalar f) _
    ((moduleCohomologyFormalFunctionsEquiv I f F hF 0
      (AdicCompletion.map I
        (moduleH0GlobalSectionsEquiv X (affineFormalFunctionsScalar f) F).symm.toLinearMap
        (AdicCompletion.of I _ x))).val (op n)) = _
  rw [AdicCompletion.map_of, moduleCohomologyFormalFunctionsEquiv_of]
  exact (Sheaf.H.equiv₀_naturality CategoryTheory.Limits.isTerminalTop
    ((SheafOfModules.toSheaf X.ringCatSheaf).map
      (Modules.idealQuotientπ X (affineFormalFunctionsScalar f) F (I ^ n)))
    ((moduleH0GlobalSectionsEquiv X (affineFormalFunctionsScalar f) F).symm x)).symm.trans
      (congrArg ((Modules.idealQuotientπ X (affineFormalFunctionsScalar f) F (I ^ n)).app ⊤)
        ((moduleH0EquivOfHom X (affineFormalFunctionsScalar f) F).apply_symm_apply x))

end AlgebraicGeometry.Scheme.Cohomology
