/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.IdealPowers.ThickeningSections
public import Mathlib.Topology.Sheaves.SheafCondition.Sites

/-!
# Actual coefficient quotients and pushforward from an ideal thickening

The quotient comparison is the unique descent of the original geometric
pullback unit through the actual coefficient cokernel. Its invertibility is
checked on affine opens using the quotient description of sections, not a
nonflat cohomology base-change theorem.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.Modules

universe u
variable {A : Type u} [CommRing A] {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of A)) (F : X.Modules) [F.IsQuasicoherent] (J : Ideal A)

/-- The structural scalar map for ideal thickenings over an affine base. -/
abbrev idealThickeningBaseScalar : A →+* Γ(X, ⊤) :=
  f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom

local notation "α" => idealThickeningBaseScalar f

/-- The original geometric unit for the actual ideal thickening. -/
abbrev idealThickeningUnit : F ⟶
    (pushforward (idealThickeningι f J)).obj (idealThickeningCoefficient f F J) :=
  (pullbackPushforwardAdjunction (idealThickeningι f J)).unit.app F

/-- On affine sections, the original thickening unit has precisely the expected kernel. -/
theorem idealThickeningUnit_eq_zero_iff (U : X.Opens) (hU : IsAffineOpen U)
    (s : idealThickeningOriginalSections f F U) :
    (idealThickeningUnit f F J).app U s = 0 ↔
      s ∈ J • (⊤ : Submodule A (idealThickeningOriginalSections f F U)) := by
  change (((pullbackPushforwardAdjunction (idealThickeningι f J)).unit.app F).app U) s = 0 ↔ _
  erw [← idealThickeningSectionsQuotientEquiv_mk f F J U hU s,
    LinearEquiv.map_eq_zero_iff, Submodule.Quotient.mk_eq_zero]

/-- The actual ideal-multiple inclusion is killed by the original geometric unit. -/
theorem idealMultipleι_thickeningUnit :
    idealMultipleι X α F J ≫ idealThickeningUnit f F J = 0 := by
  apply moduleHom_ext_affine
  intro U
  ext s
  change (idealThickeningUnit f F J).app U.val ((idealMultipleι X α F J).app U.val s) = 0
  apply (idealThickeningUnit_eq_zero_iff f F J U.val U.property _).mpr
  exact (idealMultipleAffineSectionsEquiv X α F J U s).property

/-- The canonical map from the original coefficient quotient to the actual
pushforward of its pullback to the ideal thickening. -/
def idealQuotientToThickening : idealQuotient X α F J ⟶
    (pushforward (idealThickeningι f J)).obj (idealThickeningCoefficient f F J) :=
  cokernel.desc (idealMultipleι X α F J) (idealThickeningUnit f F J)
    (idealMultipleι_thickeningUnit f F J)

/-- The quotient map followed by the comparison is exactly the original unit. -/
@[reassoc (attr := simp)]
theorem idealQuotientπ_toThickening :
    idealQuotientπ X α F J ≫ idealQuotientToThickening f F J =
      idealThickeningUnit f F J := cokernel.π_desc _ _ _

/-- Original affine sections of the coefficient quotient surject under the
original quotient projection. -/
theorem idealQuotientπ_affine_surjective (U : X.affineOpens) :
    Function.Surjective ((idealQuotientπ X α F J).app U.val) := by
  let := idealQuotient_isQuasicoherent X α F J
  let := QuasiCoherent.quasicoherent_kernel (idealQuotientπ X α F J)
  exact affineOpenSections_epi_surjective U (idealQuotientπ X α F J)

/-- The canonical thickening comparison is bijective on every affine open. -/
theorem idealQuotientToThickening_affine_bijective (U : X.affineOpens) :
    Function.Bijective ((idealQuotientToThickening f F J).app U.val) := by
  have hcomp (s : idealThickeningOriginalSections f F U.val) :
      (idealQuotientToThickening f F J).app U.val ((idealQuotientπ X α F J).app U.val s) =
        (idealThickeningUnit f F J).app U.val s :=
    congrArg (fun k => k.app U.val s) (idealQuotientπ_toThickening f F J)
  constructor
  · apply (injective_iff_map_eq_zero _).mpr
    intro q hq
    obtain ⟨s, rfl⟩ := idealQuotientπ_affine_surjective f F J U q
    have hs : s ∈ J • (⊤ : Submodule A (idealThickeningOriginalSections f F U.val)) :=
      (idealThickeningUnit_eq_zero_iff f F J U.val U.property s).mp ((hcomp s).symm.trans hq)
    let e := idealMultipleAffineSectionsEquiv X α F J U
    let t := e.symm ⟨s, hs⟩
    have ht : (idealMultipleι X α F J).app U.val t = s :=
      congrArg Subtype.val (e.apply_symm_apply ⟨s, hs⟩)
    rw [← ht]
    exact congrArg (fun k => k.app U.val t) (idealMultipleι_quotientπ X α F J)
  · intro t
    let e := idealThickeningSectionsQuotientEquiv f F J U.val U.property
    obtain ⟨s, hs⟩ := Submodule.Quotient.mk_surjective _ (e.symm t)
    refine ⟨(idealQuotientπ X α F J).app U.val s, ?_⟩
    rw [hcomp]
    change (((pullbackPushforwardAdjunction (idealThickeningι f J)).unit.app F).app U.val) s = t
    erw [← idealThickeningSectionsQuotientEquiv_mk f F J U.val U.property s]
    exact (congrArg e hs).trans (e.apply_symm_apply t)

/-- The canonical quotient-to-thickening map is an isomorphism for arbitrary
quasicoherent coefficients, with no flatness hypothesis. -/
instance idealQuotientToThickening_isIso : IsIso (idealQuotientToThickening f F J) := by
  let φ := idealQuotientToThickening f F J
  let ψ := (SheafOfModules.toSheaf X.ringCatSheaf).map φ
  have : IsIso ψ := TopCat.Sheaf.isIso_iff_isIso_basis
    (B := fun U : X.affineOpens => U.val) (by simpa using X.isBasis_affineOpens)
    (fun U => (ConcreteCategory.isIso_iff_bijective _).mpr
      (idealQuotientToThickening_affine_bijective f F J U))
  have : IsIso ((Scheme.Modules.toPresheaf X).map φ) :=
    inferInstanceAs (IsIso ((sheafToPresheaf (Opens.grothendieckTopology X)
      AddCommGrpCat).map ψ))
  exact isIso_of_reflects_iso φ (Scheme.Modules.toPresheaf X)

/-- The actual coefficient quotient is the actual pushed-forward thickening
coefficient, through the map descended from the original geometric unit. -/
def idealQuotientThickeningIso : idealQuotient X α F J ≅
    (pushforward (idealThickeningι f J)).obj (idealThickeningCoefficient f F J) :=
  asIso (idealQuotientToThickening f F J)

@[reassoc (attr := simp)]
theorem idealQuotientπ_thickeningIso_hom :
    idealQuotientπ X α F J ≫ (idealQuotientThickeningIso f F J).hom =
      idealThickeningUnit f F J := idealQuotientπ_toThickening f F J

end AlgebraicGeometry.Scheme.Modules
