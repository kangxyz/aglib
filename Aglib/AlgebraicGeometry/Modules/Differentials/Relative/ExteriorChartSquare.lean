/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Differentials.Relative.ExteriorCoefficient
public import Aglib.AlgebraicGeometry.Modules.Differentials.Relative.ExteriorOpenArrow
public import Aglib.AlgebraicGeometry.Modules.Differentials.Relative.ExteriorOpenRestriction
public import Aglib.AlgebraicGeometry.Modules.Differentials.Relative.ExteriorPullbackComposition


/-!
# The original raw arrow in an actual open chart triangle

The source restriction is the original open comparison, and both structural
comparisons come from the supplied actual triangle. The equation follows
from the already-proved original pullback composition and open arrows.
-/

@[expose] public noncomputable section

open CategoryTheory
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Differentials

universe u

namespace AlgebraicGeometry.Scheme.Modules.Differentials

private theorem chart_square {C : Type*} [Category C] {A B D E F : C}
    (u : B ≅ A) (v : E ≅ F) (p : B ⟶ D) (q : D ⟶ F) (t : A ⟶ E)
    (h : u.inv ≫ p ≫ q = t ≫ v.hom) : p ≫ q ≫ v.inv = u.hom ≫ t := by
  have ht := congrArg (fun z => u.hom ≫ z ≫ v.inv) h
  simpa only [Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id,
    Category.comp_id] using ht

/-- Original restriction and the original atlas triangle compare the raw arrows. -/
theorem rawFormsPullback_openTriangle {X Y U : Scheme.{u}} {Λ : CommRingCat.{u}}
    (a : X ⟶ Spec Λ) (b : Y ⟶ X) (f : U ⟶ Y) [IsOpenImmersion f]
    (k : U ⟶ X) (hk : f ≫ b = k) (n : ℕ) :
    (pullback f).map (rawFormsPullback a b n) ≫
      (Scheme.Modules.restrictFunctorIsoPullback f).inv.app
        (moduleExteriorPower Y (relativeDifferentialSheaf (b ≫ a)) n) ≫
      (rawFormsOpenIso (b ≫ a) f n).hom ≫
      (moduleExteriorPowerFunctor U n).map
        (relativeDifferentialCongrIso (f ≫ (b ≫ a))
          ((Category.assoc f b a).symm.trans (congrArg (fun z => z ≫ a) hk))).hom =
    (pullbackComp f b).hom.app (moduleExteriorPower X (relativeDifferentialSheaf a) n) ≫
      (pullbackCongr hk).hom.app (moduleExteriorPower X (relativeDifferentialSheaf a) n) ≫
      rawFormsPullback a k n := by
  subst k
  have ho :
      (Scheme.Modules.restrictFunctorIsoPullback f).inv.app
          (moduleExteriorPower Y (relativeDifferentialSheaf (b ≫ a)) n) ≫
        (rawFormsOpenIso (b ≫ a) f n).hom = rawFormsPullback (b ≫ a) f n := by
    rw [← rawFormsPullback_restrict (b ≫ a) f n, Iso.inv_hom_id_app_assoc]
  have hc := chart_square
    ((pullbackComp f b).app (moduleExteriorPower X (relativeDifferentialSheaf a) n))
    ((moduleExteriorPowerFunctor U n).mapIso
      (relativeDifferentialCongrIso ((f ≫ b) ≫ a) (Category.assoc f b a)))
    ((pullback f).map (rawFormsPullback a b n)) (rawFormsPullback (b ≫ a) f n)
    (rawFormsPullback a (f ≫ b) n) (rawFormsPullback_comp a b f n)
  have hid : (pullbackCongr (rfl : f ≫ b = f ≫ b)).hom.app
      (moduleExteriorPower X (relativeDifferentialSheaf a) n) = 𝟙 _ := rfl
  rw [hid, Category.id_comp]
  rw [← Category.assoc _ (rawFormsOpenIso (b ≫ a) f n).hom, ho]
  exact hc

/-- The same original open-triangle square, retaining both whole comparison isomorphisms. -/
theorem rawFormsPullback_openTriangle_iso {X Y U : Scheme.{u}} {Λ : CommRingCat.{u}}
    (a : X ⟶ Spec Λ) (b : Y ⟶ X) (f : U ⟶ Y) [IsOpenImmersion f]
    (k : U ⟶ X) (hk : f ≫ b = k) (n : ℕ) :
    let r : (moduleExteriorPower Y (relativeDifferentialSheaf (b ≫ a)) n).restrict f ≅
        moduleExteriorPower U (relativeDifferentialSheaf (k ≫ a)) n :=
      rawFormsOpenIso (b ≫ a) f n ≪≫
        (moduleExteriorPowerFunctor U n).mapIso
          (relativeDifferentialCongrIso (f ≫ (b ≫ a))
            ((Category.assoc f b a).symm.trans (congrArg (fun z => z ≫ a) hk)))
    let c := pullbackComp f b ≪≫ pullbackCongr hk
    (pullback f).map (rawFormsPullback a b n) ≫
        (Scheme.Modules.restrictFunctorIsoPullback f).inv.app
          (moduleExteriorPower Y (relativeDifferentialSheaf (b ≫ a)) n) ≫ r.hom =
      c.hom.app (moduleExteriorPower X (relativeDifferentialSheaf a) n) ≫
        rawFormsPullback a k n := by
  intro r c
  simpa only [r, c, Iso.trans_hom, Functor.mapIso_hom, NatTrans.comp_app,
    Category.assoc] using rawFormsPullback_openTriangle a b f k hk n


end AlgebraicGeometry.Scheme.Modules.Differentials
