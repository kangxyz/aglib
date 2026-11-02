/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Finite.LowerShriek
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Open.ModuleUnderlyingCoherence
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Coefficients.GeometricFunctors
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Coefficients.ZMod
public import Mathlib.CategoryTheory.Whiskering

/-!
# The original finite comparison over constant cyclic coefficients

Fully faithful scalar forgetting lifts the same whole abelian comparison to
the original module functors. The construction and its whole underlying law
include levels zero and one. Invertibility is reflected for this same map;
it is not assumed to hold merely because the coefficient lift exists.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

attribute [local instance] hasSheafifyLarge hasSheafifyModules

variable {Y X : Scheme.{u}} (f : Y ⟶ X) [Etale f] [IsSeparated f] (n : ℕ)

/-- The whole module comparison lifts the same original abelian comparison,
with the existing underlying isomorphisms on both sides. -/
def moduleEtaleLowerShriekToDirectImage :
    moduleLowerShriek f (ULift.{u + 1} (ZMod n)) ⟶
      moduleDirectImage f (ULift.{u + 1} (ZMod n)) :=
  letI := moduleSheaf_uLiftZMod_toSheaf_full X n
  ((Functor.whiskeringRight (ModuleSheaf Y (ULift.{u + 1} (ZMod n)))
      (ModuleSheaf X (ULift.{u + 1} (ZMod n))) (AbelianSheaf.{u, u + 1} X)).obj
      (SheafOfModules.toSheaf (constantRing X (ULift.{u + 1} (ZMod n))))).preimage
    ((moduleLowerShriekUnderlyingIso f (ULift.{u + 1} (ZMod n))).hom ≫
      Functor.whiskerLeft
        (SheafOfModules.toSheaf (constantRing Y (ULift.{u + 1} (ZMod n))))
        (etaleLowerShriekToDirectImage f) ≫
      (moduleDirectImageUnderlyingIso f (ULift.{u + 1} (ZMod n))).inv)

/-- Scalar forgetting identifies the entire original comparison, before
evaluation at a module coefficient. -/
theorem moduleEtaleLowerShriekToDirectImage_underlying :
    Functor.whiskerRight (moduleEtaleLowerShriekToDirectImage f n)
        (SheafOfModules.toSheaf (constantRing X (ULift.{u + 1} (ZMod n)))) =
      (moduleLowerShriekUnderlyingIso f (ULift.{u + 1} (ZMod n))).hom ≫
        Functor.whiskerLeft
          (SheafOfModules.toSheaf (constantRing Y (ULift.{u + 1} (ZMod n))))
          (etaleLowerShriekToDirectImage f) ≫
        (moduleDirectImageUnderlyingIso f (ULift.{u + 1} (ZMod n))).inv := by
  let := moduleSheaf_uLiftZMod_toSheaf_full X n
  exact Functor.map_preimage
    ((Functor.whiskeringRight (ModuleSheaf Y (ULift.{u + 1} (ZMod n)))
      (ModuleSheaf X (ULift.{u + 1} (ZMod n))) (AbelianSheaf.{u, u + 1} X)).obj
      (SheafOfModules.toSheaf (constantRing X (ULift.{u + 1} (ZMod n))))) _

/-- Evaluating the proved whole equation preserves the actual module action,
source coefficient and original abelian map. -/
theorem moduleEtaleLowerShriekToDirectImage_underlying_app
    (M : ModuleSheaf Y (ULift.{u + 1} (ZMod n))) :
    (SheafOfModules.toSheaf (constantRing X (ULift.{u + 1} (ZMod n)))).map
        ((moduleEtaleLowerShriekToDirectImage f n).app M) =
      (moduleLowerShriekUnderlyingIso f (ULift.{u + 1} (ZMod n))).hom.app M ≫
        (etaleLowerShriekToDirectImage f).app
          ((SheafOfModules.toSheaf (constantRing Y (ULift.{u + 1} (ZMod n)))).obj M) ≫
        (moduleDirectImageUnderlyingIso f (ULift.{u + 1} (ZMod n))).inv.app M :=
  NatTrans.congr_app (moduleEtaleLowerShriekToDirectImage_underlying f n) M

/-- Invertibility of this same abelian comparison reflects to its actual
module lift. This lemma retains the precise still-required abelian input. -/
theorem moduleEtaleLowerShriekToDirectImage_isIso
    [IsIso (etaleLowerShriekToDirectImage f)] :
    IsIso (moduleEtaleLowerShriekToDirectImage f n) := by
  let := moduleSheaf_uLiftZMod_toSheaf_full X n
  let H := (Functor.whiskeringRight (ModuleSheaf Y (ULift.{u + 1} (ZMod n)))
    (ModuleSheaf X (ULift.{u + 1} (ZMod n))) (AbelianSheaf.{u, u + 1} X)).obj
    (SheafOfModules.toSheaf (constantRing X (ULift.{u + 1} (ZMod n))))
  have : IsIso (H.map (moduleEtaleLowerShriekToDirectImage f n)) := by
    change IsIso (Functor.whiskerRight (moduleEtaleLowerShriekToDirectImage f n)
      (SheafOfModules.toSheaf (constantRing X (ULift.{u + 1} (ZMod n)))))
    rw [moduleEtaleLowerShriekToDirectImage_underlying]
    infer_instance
  exact isIso_of_reflects_iso (moduleEtaleLowerShriekToDirectImage f n) H

section FiniteEtale

variable [IsFinite f] (d : ℕ) (hd : ∀ x : X, f.finrank x = d)

include d hd

/-- The SAME module comparison is invertible at every cyclic coefficient
level, including zero and one, from the original abelian comparison. -/
theorem moduleFiniteEtaleLowerShriekToDirectImage_isIso :
    IsIso (moduleEtaleLowerShriekToDirectImage f n) := by
  let h := finiteEtaleLowerShriekToDirectImage_isIso (Scheme.FiniteEtale.mk f) d hd
  change IsIso (etaleLowerShriekToDirectImage f) at h
  exact moduleEtaleLowerShriekToDirectImage_isIso f n

/-- The actual module isomorphism has the existing comparison as its hom. -/
def moduleFiniteEtaleLowerShriekDirectImageIso :
    moduleLowerShriek f (ULift.{u + 1} (ZMod n)) ≅
      moduleDirectImage f (ULift.{u + 1} (ZMod n)) := by
  letI := moduleFiniteEtaleLowerShriekToDirectImage_isIso f n d hd
  exact asIso (moduleEtaleLowerShriekToDirectImage f n)

@[simp] theorem moduleFiniteEtaleLowerShriekDirectImageIso_hom :
    (moduleFiniteEtaleLowerShriekDirectImageIso f n d hd).hom =
      moduleEtaleLowerShriekToDirectImage f n := rfl

/-- Transport of the original lower-shriek adjunction along the SAME proved
comparison. Its unit and counit retain the original maps. -/
def moduleFiniteEtaleDirectImageAdjunction :
    moduleDirectImage f (ULift.{u + 1} (ZMod n)) ⊣
      moduleInverseImage f (ULift.{u + 1} (ZMod n)) :=
  (moduleLowerShriekAdjunction f (ULift.{u + 1} (ZMod n))).ofNatIsoLeft
    (moduleFiniteEtaleLowerShriekDirectImageIso f n d hd)

/-- The transported adjunction retains the whole original counit formula
before any module coefficient is chosen. -/
theorem moduleFiniteEtaleDirectImageAdjunction_counit :
    (moduleFiniteEtaleDirectImageAdjunction f n d hd).counit =
      Functor.whiskerLeft (moduleInverseImage f (ULift.{u + 1} (ZMod n)))
          (moduleFiniteEtaleLowerShriekDirectImageIso f n d hd).inv ≫
        (moduleLowerShriekAdjunction f (ULift.{u + 1} (ZMod n))).counit := rfl

/-- The inverse module comparison has the inverse of the same original
abelian comparison underneath, with both original coefficient isomorphisms. -/
theorem moduleFiniteEtaleLowerShriekDirectImageIso_inv_underlying
    (M : ModuleSheaf Y (ULift.{u + 1} (ZMod n))) :
    (SheafOfModules.toSheaf (constantRing X (ULift.{u + 1} (ZMod n)))).map
        ((moduleFiniteEtaleLowerShriekDirectImageIso f n d hd).inv.app M) =
      (moduleDirectImageUnderlyingIso f (ULift.{u + 1} (ZMod n))).hom.app M ≫
        (finiteEtaleLowerShriekDirectImageIso (Scheme.FiniteEtale.mk f) d hd).inv.app
          ((SheafOfModules.toSheaf (constantRing Y (ULift.{u + 1} (ZMod n)))).obj M) ≫
        (moduleLowerShriekUnderlyingIso f (ULift.{u + 1} (ZMod n))).inv.app M := by
  let U := SheafOfModules.toSheaf (constantRing X (ULift.{u + 1} (ZMod n)))
  let e := moduleFiniteEtaleLowerShriekDirectImageIso f n d hd
  let a : etaleLowerShriek f ≅ directImage f :=
    finiteEtaleLowerShriekDirectImageIso (Scheme.FiniteEtale.mk f) d hd
  have ha := finiteEtaleLowerShriekDirectImageIso_hom (Scheme.FiniteEtale.mk f) d hd
  change a.hom = etaleLowerShriekToDirectImage f at ha
  apply (cancel_mono (U.map (e.hom.app M))).mp
  rw [← U.map_comp, Iso.inv_hom_id_app, U.map_id]
  rw [moduleFiniteEtaleLowerShriekDirectImageIso_hom,
    moduleEtaleLowerShriekToDirectImage_underlying_app]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
  rw [← ha, a.inv_hom_id_app_assoc]
  exact ((moduleDirectImageUnderlyingIso f (ULift.{u + 1} (ZMod n))).hom_inv_id_app M).symm


end FiniteEtale

end AlgebraicGeometry.Scheme.EtaleCohomology
