/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.InternalHom.Gluing
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free

/-! # Original overlap compatibility from native free frames

The same overlap restriction comparisons and supplied free frames construct the
whole indexed matching datum before specializing a geometric chart family.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.Modules.InternalHom

universe u v

private theorem freeHom_ext {Z : Scheme.{u}} {J : Type u} {N : Z.Modules}
    (f g : SheafOfModules.free (R := Z.ringCatSheaf) J ⟶ N)
    (h : ∀ (j : J) (V : Z.Opens), f.val.app (op V)
      ((SheafOfModules.freeSection (R := Z.ringCatSheaf) j).val (op V)) =
        g.val.app (op V)
          ((SheafOfModules.freeSection (R := Z.ringCatSheaf) j).val (op V))) : f = g := by
  apply N.freeHomEquiv.injective
  funext j
  ext V
  change f.val.app V ((SheafOfModules.freeSection (R := Z.ringCatSheaf) j).val V) =
    g.val.app V ((SheafOfModules.freeSection (R := Z.ringCatSheaf) j).val V)
  exact h j V.unop

variable {X : Scheme.{u}} {ι : Type v} {Y : ι → Scheme.{u}}
  (a : ∀ i, Y i ⟶ X) [∀ i, IsOpenImmersion (a i)]
  (M N : X.Modules) (f : ∀ i, M.restrict (a i) ⟶ N.restrict (a i))

/-- Original free-frame generator equations give the complete native indexed overlap law. -/
theorem restrictionHomCompatible_of_freeFrames
    (J : ι → ι → Type u)
    (E : ∀ i k, SheafOfModules.free (R := (Limits.pullback (a i) (a k)).ringCatSheaf) (J i k) ≅
      (M.restrict (a k)).restrict (pullback.snd (a i) (a k)))
    (h : ∀ (i k : ι) (j : J i k) (W : (Limits.pullback (a i) (a k)).Opens),
      let p := pullback.fst (a i) (a k)
      let q := pullback.snd (a i) (a k)
      let cM := (Scheme.Modules.overlapRestrictIso (a i) (a k)).app M
      let cN := (Scheme.Modules.overlapRestrictIso (a i) (a k)).app N
      let s := (SheafOfModules.freeSection
        (R := (Limits.pullback (a i) (a k)).ringCatSheaf) j).val (op W)
      ((E i k).hom ≫ cM.inv ≫ (Scheme.Modules.restrictFunctor p).map (f i) ≫
        cN.hom).val.app (op W) s =
      ((E i k).hom ≫ (Scheme.Modules.restrictFunctor q).map (f k)).val.app (op W) s) :
    RestrictionHomCompatible a M N f := by
  intro i k
  apply (cancel_epi ((Scheme.Modules.overlapRestrictIso (a i) (a k)).app M).inv).1
  apply (cancel_epi (E i k).hom).1
  change (E i k).hom ≫ ((Scheme.Modules.overlapRestrictIso (a i) (a k)).app M).inv ≫
      (Scheme.Modules.restrictFunctor (pullback.fst (a i) (a k))).map (f i) ≫
        ((Scheme.Modules.overlapRestrictIso (a i) (a k)).app N).hom =
    (E i k).hom ≫ ((Scheme.Modules.overlapRestrictIso (a i) (a k)).app M).inv ≫
      ((Scheme.Modules.overlapRestrictIso (a i) (a k)).app M).hom ≫
        (Scheme.Modules.restrictFunctor (pullback.snd (a i) (a k))).map (f k)
  rw [Iso.inv_hom_id_assoc]
  apply freeHom_ext
  exact h i k

/-- Evaluate the indexed law at the same native pullback, with its original pointwise form. -/
theorem restrictionHomCompatible_eq
    (h : RestrictionHomCompatible a M N f) (i k : ι) :
    (Scheme.Modules.restrictFunctor (pullback.fst (a i) (a k))).map (f i) ≫
      (Scheme.Modules.overlapRestrictIso (a i) (a k)).hom.app N =
    (Scheme.Modules.overlapRestrictIso (a i) (a k)).hom.app M ≫
      (Scheme.Modules.restrictFunctor (pullback.snd (a i) (a k))).map (f k) :=
  h i k

end AlgebraicGeometry.Scheme.Modules.InternalHom
