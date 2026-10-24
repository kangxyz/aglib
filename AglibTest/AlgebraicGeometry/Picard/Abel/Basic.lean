/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Picard.Abel.Basic

/-!
# Consumer checks for the Abel class

The Abel class `−[I_D]` of a relative effective Cartier divisor `D ⊆ X ×_S T` (Kleiman,
*The Picard scheme*, arXiv:math/0504020v1, Def. 4.6, p. 27) is natural for the maps of
`familyPicardFunctor p`, and the variable form applies to the base-change map written as
`pullback.map p _ p _ (𝟙 X) g.left (𝟙 S)`, the presentation used by divisor functors that act by
`IdealSheafData.comap` along it.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits Opposite AlgebraicGeometry
open Scheme.RelativePicard Scheme.Modules.Invertible

universe u

namespace AglibTest.Abel

variable {S X : Scheme.{u}} (p : X ⟶ S) {T T' : Over S} (g : T' ⟶ T)
  (D : (pullback p T.hom).IdealSheafData)
  (hD : Scheme.Hom.IsRelativeEffectiveCartier D.subschemeι (pullback.snd p T.hom))

/-- The Abel class is the class of `𝒪_{X_T}(D) = I_D^∨`. -/
example : abelClass p D hD = classOf _ (dualLineBundle _ hD.idealLineBundle) :=
  abelClass_eq_classOf_dualLineBundle p D hD

/-- Naturality in `T`, in the form of `familyPicardFunctor p`. -/
example : ((familyPicardFunctor p).map g.op).hom (abelClass p D hD) =
    abelClass p (T := T') (D.comap ((familyScheme p).map g))
      (isRelativeEffectiveCartier_comap_familyScheme_map p g hD) :=
  familyPicardFunctor_map_abelClass p g D hD

/-- Naturality of the class in `Pic_{X/S,(fppf)}`. -/
example : (fppfPicardSheaf p).obj.map g.op (fppfAbelClass p D hD) =
    fppfAbelClass p (T := T') (D.comap ((familyScheme p).map g))
      (isRelativeEffectiveCartier_comap_familyScheme_map p g hD) :=
  fppfPicardSheaf_map_fppfAbelClass p g D hD

/-- Naturality for the base-change map presented as `pullback.map`. -/
example : pullbackClass (pullback.map p T'.hom p T.hom (𝟙 X) g.left (𝟙 S) (by simp)
      (by rw [Category.comp_id, Over.w g])) (abelClass p D hD) =
    abelClass p (T := T') (D.comap (pullback.map p T'.hom p T.hom (𝟙 X) g.left (𝟙 S) (by simp)
      (by rw [Category.comp_id, Over.w g])))
      (hD.of_isPullback (Scheme.isPullback_pullbackMap_snd p T.hom T'.hom g.left (Over.w g))
        (D.isPullback_subschemeMap_comap _)) :=
  pullbackClass_abelClass p (Scheme.isPullback_pullbackMap_snd p T.hom T'.hom g.left (Over.w g))
    D hD

/-- The ideal of the base change is the pullback of the ideal, as line bundles. -/
example {Y T₀ S₀ D' D₀ X₀ : Scheme.{u}} {p₀ : X₀ ⟶ S₀} {q : T₀ ⟶ S₀} {p' : Y ⟶ T₀}
    {b : Y ⟶ X₀} {i : D₀ ⟶ X₀} {i' : D' ⟶ Y} {a : D' ⟶ D₀} (H : IsPullback b p' p₀ q)
    (H' : IsPullback a i' i b) (hi : Scheme.Hom.IsRelativeEffectiveCartier i p₀) :
    Nonempty ((pullbackLineBundle b hi.idealLineBundle).val ≅
      (hi.of_isPullback H H').idealLineBundle.val) :=
  ⟨hi.pullbackIdealLineBundleIso H H'⟩

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.familyPicardFunctor_map_abelClass' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms familyPicardFunctor_map_abelClass

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.pullbackClass_abelClass' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms pullbackClass_abelClass

end AglibTest.Abel
