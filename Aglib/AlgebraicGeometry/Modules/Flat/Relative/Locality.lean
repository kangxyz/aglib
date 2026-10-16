/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Flat.Relative
public import Aglib.AlgebraicGeometry.Modules.Flat.Locality
public import Mathlib.RingTheory.Flat.Localization

/-!
# Open restriction and actual base-ring stalk flatness

Relative flatness transports through the original open-restriction stalk
isomorphism. Over `Spec A`, the native localization flatness of the base local
ring makes the actual coefficient stalk flat over `A`, with the original
stalk ring map retained. The affine `Spec.map` specialization keeps the given
ring map and its native structural stalk action.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules

/-- Relative flatness is invariant under an actual coefficient isomorphism. -/
theorem relativeFlat_of_iso {X Y : Scheme.{u}} (f : X ⟶ Y) {M N : X.Modules}
    (e : M ≅ N) (hN : relativeFlat f N) : relativeFlat f M := by
  intro x
  let := hN x
  exact Module.Flat.of_linearEquiv
    ((ModuleCat.restrictScalars (f.stalkMap x).hom).mapIso
      ((moduleStalk X x).mapIso e)).toLinearEquiv

/-- Original open restriction preserves flatness over the same base local ring. -/
theorem relativeFlat_restrict {U X Y : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (f : X ⟶ Y) {M : X.Modules} (hM : relativeFlat f M) :
    relativeFlat (j ≫ f) (M.restrict j) := by
  intro x
  let T := (moduleStalk U x).obj (M.restrict j)
  have he : ((j ≫ f).stalkMap x).hom =
      (j.stalkMap x).hom.comp (f.stalkMap (j x)).hom :=
    congrArg CommRingCat.Hom.hom (Scheme.Hom.stalkMap_comp j f x)
  let e := (ModuleCat.restrictScalarsComp' (f.stalkMap (j x)).hom (j.stalkMap x).hom
      ((j ≫ f).stalkMap x).hom he).app T ≪≫
    (ModuleCat.restrictScalars (f.stalkMap (j x)).hom).mapIso
      ((restrictModuleStalkIso j x).app M)
  exact (Module.Flat.equiv_iff e.toLinearEquiv).mpr (hM (j x))

/-- Over an affine base, a relatively flat actual stalk is flat over the
original base ring through its original composed structural stalk map. -/
theorem flat_stalk_over_spec_of_relativeFlat {X : Scheme.{u}} {A : CommRingCat.{u}}
    (f : X ⟶ Spec A) {M : X.Modules} (hM : relativeFlat f M) (x : X) :
    Module.Flat A
      ((ModuleCat.restrictScalars ((f.stalkMap x).hom.comp
        (StructureSheaf.toStalk A (f x)).hom)).obj ((moduleStalk X x).obj M)) := by
  let T := (moduleStalk X x).obj M
  let N : ModuleCat ((structurePresheafInCommRingCat A).stalk (f x)) :=
    (ModuleCat.restrictScalars (f.stalkMap x).hom).obj T
  let : Module.Flat ((structurePresheafInCommRingCat A).stalk (f x)) N := hM x
  have hA : (StructureSheaf.toStalk A (f x)).hom.Flat := by
    let : Algebra A ((Spec.structureSheaf A).presheaf.stalk (f x)) :=
      StructureSheaf.stalkAlgebra A (f x)
    let : IsLocalization.AtPrime ((Spec.structureSheaf A).presheaf.stalk (f x))
        (f x).asIdeal := StructureSheaf.IsLocalization.to_stalk A (f x)
    change Module.Flat A ((Spec.structureSheaf A).presheaf.stalk (f x))
    exact IsLocalization.flat _ (f x).asIdeal.primeCompl
  have H := flat_restrictScalars (StructureSheaf.toStalk A (f x)).hom hA N
  exact (Module.Flat.equiv_iff
    ((ModuleCat.restrictScalarsComp (StructureSheaf.toStalk A (f x)).hom
      (f.stalkMap x).hom).app T).toLinearEquiv).mpr H

/-- For the original affine ring map, the base-ring action on the actual
source stalk is restriction along that ring map followed by its native stalk map. -/
theorem flat_stalk_of_relativeFlat_specMap {A B : CommRingCat.{u}} (φ : A ⟶ B)
    {M : (Spec B).Modules} (hM : relativeFlat (Spec.map φ) M) (x : Spec B) :
    Module.Flat A ((ModuleCat.restrictScalars φ.hom).obj
      ((ModuleCat.restrictScalars (StructureSheaf.toStalk B x).hom).obj
        ((moduleStalk (Spec B) x).obj M))) := by
  have h := flat_stalk_over_spec_of_relativeFlat (Spec.map φ) hM x
  have he : ((Spec.map φ).stalkMap x).hom.comp
      (StructureSheaf.toStalk A ((Spec.map φ) x)).hom =
      (StructureSheaf.toStalk B x).hom.comp φ.hom :=
    congrArg CommRingCat.Hom.hom (AlgebraicGeometry.stalkMap_toStalk φ x)
  rw [he] at h
  exact (Module.Flat.equiv_iff
    ((ModuleCat.restrictScalarsComp φ.hom (StructureSheaf.toStalk B x).hom).app
      ((moduleStalk (Spec B) x).obj M)).symm.toLinearEquiv).mpr h

/-- Relative flatness over a composite with an open immersion is relative flatness
over the open target itself, through its actual base-stalk ring isomorphism. -/
theorem relativeFlat_of_comp_isOpenImmersion {W V Y : Scheme.{u}}
    (b : W ⟶ V) (j : V ⟶ Y) [IsOpenImmersion j] {N : W.Modules}
    (hN : relativeFlat (b ≫ j) N) : relativeFlat b N := by
  intro x
  let T := (moduleStalk W x).obj N
  let P := (ModuleCat.restrictScalars (b.stalkMap x).hom).obj T
  let e := (asIso (j.stalkMap (b x))).commRingCatIsoToRingEquiv
  let F := ModuleCat.restrictScalarsEquivalenceOfRingEquiv e
  have hc : ((b ≫ j).stalkMap x).hom =
      (b.stalkMap x).hom.comp (j.stalkMap (b x)).hom :=
    congrArg CommRingCat.Hom.hom (Scheme.Hom.stalkMap_comp b j x)
  let E := (ModuleCat.restrictScalarsComp' (j.stalkMap (b x)).hom (b.stalkMap x).hom
    ((b ≫ j).stalkMap x).hom hc).app T
  let : Module.Flat (Y.presheaf.stalk (j (b x)))
      (F.functor.obj P) :=
    (Module.Flat.equiv_iff E.toLinearEquiv).mp (hN x)
  let : Module.Flat (V.presheaf.stalk (b x))
      ((F.functor ⋙ F.inverse).obj P) :=
    flat_restrictScalars e.symm.toRingHom (RingHom.Flat.of_bijective e.symm.bijective)
      (F.functor.obj P)
  exact Module.Flat.of_linearEquiv (F.unitIso.app P).toLinearEquiv

/-- Ordinary pullback to an open target preserves intrinsic relative flatness.
The proof uses actual open-restriction stalks and the original base-stalk isomorphism. -/
theorem relativeFlat_pullback_of_isOpenImmersion {X Y V : Scheme.{u}}
    (f : X ⟶ Y) (j : V ⟶ Y) [IsOpenImmersion j] {M : X.Modules}
    (hM : relativeFlat f M) :
    relativeFlat (pullback.snd f j) ((Scheme.Modules.pullback (pullback.fst f j)).obj M) := by
  let a := pullback.fst f j
  let b := pullback.snd f j
  have hsource := relativeFlat_restrict a f hM
  have he : a ≫ f = b ≫ j := pullback.condition
  rw [he] at hsource
  have hrest := relativeFlat_of_comp_isOpenImmersion b j hsource
  exact relativeFlat_of_iso b ((Scheme.Modules.restrictFunctorIsoPullback a).app M).symm hrest

end AlgebraicGeometry.Scheme.Modules
