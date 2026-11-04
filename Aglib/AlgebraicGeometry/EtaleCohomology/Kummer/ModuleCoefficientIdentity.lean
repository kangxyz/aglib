/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Kummer.ModuleRootsComposition
public import Aglib.AlgebraicGeometry.EtaleCohomology.Duality.PointPurity.Finite
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Open.ModuleIdentityCoherence
public import Aglib.CategoryTheory.Sites.Representable.SectionComparisonValues

/-! Identity of the original module coefficient transports. -/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients
universe u

attribute [local instance] hasSheafifyLarge hasSheafifyModules
  moduleForget_preservesSheafification

/-- Equality transport retains the original unit coefficient map. -/
theorem moduleUnitInverseImageIso_eqToHom {X Y : Scheme.{u}} {f g : Y ⟶ X}
    (h : f = g) (n : ℕ) :
    eqToHom (congrArg (fun j => (moduleInverseImage j (ULift.{u + 1} (ZMod n))).obj
      (moduleUnit X (ULift.{u + 1} (ZMod n)))) h) ≫ (moduleUnitInverseImageIso g n).hom =
      (moduleUnitInverseImageIso f n).hom := by
  subst g
  exact Category.id_comp _

/-- The original unit transport at the identity is the original inverse-image identity. -/
theorem moduleUnitInverseImageIso_identity (X : Scheme.{u}) (n : ℕ) :
    (moduleUnitInverseImageIso (𝟙 X) n).hom =
      (moduleInverseImageIdIso (ULift.{u + 1} (ZMod n)) X).hom.app
        (moduleUnit X (ULift.{u + 1} (ZMod n))) := by
  let Λ := ULift.{u + 1} (ZMod n)
  let M := moduleUnit X Λ
  let j := eqToHom (congrArg (fun f => (moduleInverseImage f Λ).obj M)
    (Category.comp_id (𝟙 X)))
  have hc := moduleUnitInverseImageIso_comp (𝟙 X) (𝟙 X) n
  have hg := moduleUnitInverseImageIso_eqToHom (Category.comp_id (𝟙 X)) n
  have hu := congrArg (fun e => e.hom.app M) (moduleInverseImageCompIso_id_comp Λ (𝟙 X))
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Functor.leftUnitor_hom_app, eqToIso.hom, eqToHom_app] at hu
  change (moduleInverseImageCompIso Λ (𝟙 X) (𝟙 X)).hom.app M ≫
    (moduleInverseImage (𝟙 X) Λ).map ((moduleInverseImageIdIso Λ X).hom.app M) ≫
      𝟙 ((moduleInverseImage (𝟙 X) Λ).obj M) = j at hu
  exact Functor.coefficientIso_identity_of_unit_composite
    (moduleInverseImage (𝟙 X) Λ) (moduleInverseImageIdIso Λ X)
    (moduleInverseImageCompIso Λ (𝟙 X) (𝟙 X)) M j (moduleUnitInverseImageIso (𝟙 X) n)
    (hc.trans hg.symm) hu

/-- The original roots transport at the identity uses the same native identity comparison. -/
theorem moduleRootsOfUnityInverseImageIso_identity (X : Scheme.{u}) (n : ℕ) (hn : 0 < n)
    (hi : IsUnit (n : Γ(X, ⊤))) :
    (moduleRootsOfUnityInverseImageIso (𝟙 X) n hn hi).hom =
      (moduleInverseImageIdIso (ULift.{u + 1} (ZMod n)) X).hom.app (moduleRootsOfUnity X n) := by
  let Λ := ULift.{u + 1} (ZMod n)
  let M := moduleRootsOfUnity X n
  let j := eqToHom (congrArg (fun f => (moduleInverseImage f Λ).obj M)
    (Category.comp_id (𝟙 X)))
  have hc := moduleRootsOfUnityInverseImageIso_comp (𝟙 X) (𝟙 X) n hn hi
  have hg := moduleRootsOfUnityInverseImageIso_eqToHom n hn hi (Category.comp_id (𝟙 X))
  have hu := congrArg (fun e => e.hom.app M) (moduleInverseImageCompIso_id_comp Λ (𝟙 X))
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Functor.leftUnitor_hom_app, eqToIso.hom, eqToHom_app] at hu
  change (moduleInverseImageCompIso Λ (𝟙 X) (𝟙 X)).hom.app M ≫
    (moduleInverseImage (𝟙 X) Λ).map ((moduleInverseImageIdIso Λ X).hom.app M) ≫
      𝟙 ((moduleInverseImage (𝟙 X) Λ).obj M) = j at hu
  exact Functor.coefficientIso_identity_of_unit_composite
    (moduleInverseImage (𝟙 X) Λ) (moduleInverseImageIdIso Λ X)
    (moduleInverseImageCompIso Λ (𝟙 X) (𝟙 X)) M j
    (moduleRootsOfUnityInverseImageIso (𝟙 X) n hn hi) (hc.trans hg.symm) hu

end AlgebraicGeometry.Scheme.EtaleCohomology
