/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Localization.ClosedSummandDetection
public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Localization.ClosedCoefficientRefinementCore

/-! # Original closed coefficient classes under target refinement

The original closed coefficient arrow commutes with target refinement through
its actual inverse-image comparison maps. The equation is proved by canonical
horizontal square coherence and naturality, before taking cohomology or
specializing to native modules. Only commutativity of the scheme squares is
needed; neither finite exchange nor a coefficient compatibility assumption is
used. The resulting zero equivalence concerns the transformed class after the
original coefficient arrow, not its unmapped closed restriction.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology

universe u eT eW eT₂ eW₂ uM vM uN vN

attribute [local instance] hasSheafifyLarge

section Underlying

variable {X Z T W T₂ W₂ : Scheme.{u}}
  (i : Z ⟶ X) (i' : W ⟶ T) (i₂ : W₂ ⟶ T₂)
  (b : T ⟶ X) (b' : W ⟶ Z) (t : T₂ ⟶ T) (t' : W₂ ⟶ W)
  (h : i' ≫ b = b' ≫ i) (ht : i₂ ≫ t = t' ≫ i')
  (hcomp : i₂ ≫ (t ≫ b) = (t' ≫ b') ≫ i)
  {M : Type uM} [Category.{vM} M] {N : Type uN} [Category.{vN} N]
  {L : M ⥤ N}
  (U : M ⥤ AbelianSheaf.{u, u + 1} X)
  (V : N ⥤ AbelianSheaf.{u, u + 1} Z)
  (e : L ⋙ V ≅ U ⋙ inverseImage i)
  (I : M) (J : N) (a : L.obj I ⟶ J)

/-- The literal original closed coefficient arrow satisfies horizontal
refinement coherence. The comparison equation is proved, not assumed. -/
theorem underlyingClosedPullbackCoefficientMap_refinement :
    (inverseImage i₂).map ((inverseImageComp b t).hom.app (U.obj I)) ≫
        (inverseImageSquareIso i' i₂ t t' ht).hom.app ((inverseImage b).obj (U.obj I)) ≫
        (inverseImage t').map
          (underlyingClosedPullbackCoefficientMap i i' b b' h U V e I J a) =
      underlyingClosedPullbackCoefficientMap i i₂ (t ≫ b) (t' ≫ b') hcomp U V e I J a ≫
        (inverseImageComp b' t').hom.app (V.obj J) :=
  inverseImageSquareIso_coefficient_refinement i i' i₂ b b' t t' h ht hcomp
    (U.obj I) (V.obj J)
    (show (inverseImage i).obj (U.obj I) ⟶ V.obj J from e.inv.app I ≫ V.map a)

variable [HasExt.{eT} (AbelianSheaf.{u, u + 1} T)]
  [HasExt.{eW} (AbelianSheaf.{u, u + 1} W)]
  [HasExt.{eT₂} (AbelianSheaf.{u, u + 1} T₂)]
  [HasExt.{eW₂} (AbelianSheaf.{u, u + 1} W₂)]

include ht

/-- The same original coefficient class commutes with target refinement,
with both actual composition isomorphisms displayed. The refined input is
the original pullback class, transported to the composite inverse image. -/
theorem underlyingClosedPullbackCoefficientClass_refinement
    (q : ℕ) (x : Sheaf.H.{eT} ((inverseImage b).obj (U.obj I)) q) :
    Sheaf.H.map ((inverseImageComp b' t').hom.app (V.obj J)) q
        (Sheaf.H.map
          (underlyingClosedPullbackCoefficientMap i i₂ (t ≫ b) (t' ≫ b')
            hcomp U V e I J a) q
          (cohomologyPullback i₂ _ q
            (Sheaf.H.map ((inverseImageComp b t).inv.app (U.obj I)) q
              (cohomologyPullback t _ q x)))) =
      cohomologyPullback t' _ q
        (Sheaf.H.map
          (underlyingClosedPullbackCoefficientMap i i' b b' h U V e I J a) q
          (cohomologyPullback i' _ q x)) :=
  inverseImageSquareIso_coefficientClass_refinement i i' i₂ b b' t t' h ht hcomp
    (U.obj I) (V.obj J)
    (show (inverseImage i).obj (U.obj I) ⟶ V.obj J from e.inv.app I ≫ V.map a) q x

/-- Zero of the refined original transformed class is equivalent to zero of
the actual refinement pullback of the old transformed class. -/
theorem underlyingClosedPullbackCoefficientClass_refinement_eq_zero_iff
    (q : ℕ) (x : Sheaf.H.{eT} ((inverseImage b).obj (U.obj I)) q) :
    Sheaf.H.map
        (underlyingClosedPullbackCoefficientMap i i₂ (t ≫ b) (t' ≫ b')
          hcomp U V e I J a) q
        (cohomologyPullback i₂ _ q
          (Sheaf.H.map ((inverseImageComp b t).inv.app (U.obj I)) q
            (cohomologyPullback t _ q x))) = 0 ↔
      cohomologyPullback t' _ q
        (Sheaf.H.map
          (underlyingClosedPullbackCoefficientMap i i' b b' h U V e I J a) q
          (cohomologyPullback i' _ q x)) = 0 :=
  inverseImageSquareIso_coefficientClass_refinement_eq_zero_iff
    i i' i₂ b b' t t' h ht hcomp (U.obj I) (V.obj J)
    (show (inverseImage i).obj (U.obj I) ⟶ V.obj J from e.inv.app I ≫ V.map a) q x

end Underlying

section Modules

open Coefficients

variable {X Z T W T₂ W₂ : Scheme.{u}}
  (i : Z ⟶ X) (i' : W ⟶ T) (i₂ : W₂ ⟶ T₂)
  (b : T ⟶ X) (b' : W ⟶ Z) (t : T₂ ⟶ T) (t' : W₂ ⟶ W)
  (h : i' ≫ b = b' ≫ i) (ht : i₂ ≫ t = t' ≫ i')
  (hcomp : i₂ ≫ (t ≫ b) = (t' ≫ b') ≫ i)
  (Λ : Type (u + 1)) [Ring Λ]
  (I : ModuleSheaf X Λ) (J : ModuleSheaf Z Λ)
  (a : (moduleInverseImage i Λ).obj I ⟶ J)

/-- Native module coefficients use the proved general refinement equation
for their unchanged underlying comparison and original coefficient arrow.
The whole proposition is specialized from the underlying theorem, so that its
category and functor dictionaries are shared rather than independently
re-elaborated. Its maps are the defining underlying expressions of
`moduleClosedPullbackCoefficientMap`, with the same original module arrow. -/
theorem moduleClosedPullbackCoefficientMap_refinement :
    type_of% (underlyingClosedPullbackCoefficientMap_refinement
      i i' i₂ b b' t t' h ht hcomp
      (SheafOfModules.toSheaf (constantRing X Λ))
      (SheafOfModules.toSheaf (constantRing Z Λ))
      (moduleInverseImageUnderlyingIso Λ i) I J a) :=
  underlyingClosedPullbackCoefficientMap_refinement i i' i₂ b b' t t' h ht hcomp
    (SheafOfModules.toSheaf (constantRing X Λ))
    (SheafOfModules.toSheaf (constantRing Z Λ))
    (moduleInverseImageUnderlyingIso Λ i) I J a

variable [HasExt.{eT} (AbelianSheaf.{u, u + 1} T)]
  [HasExt.{eW} (AbelianSheaf.{u, u + 1} W)]
  [HasExt.{eT₂} (AbelianSheaf.{u, u + 1} T₂)]
  [HasExt.{eW₂} (AbelianSheaf.{u, u + 1} W₂)]

include ht

/-- The literal native closed coefficient class commutes with every target
refinement, through the original inverse-image composition isomorphisms. -/
theorem moduleClosedPullbackCoefficientClass_refinement
    (q : ℕ) (x : Sheaf.H.{eT} ((inverseImage b).obj
      ((SheafOfModules.toSheaf (constantRing X Λ)).obj I)) q) :
    Sheaf.H.map ((inverseImageComp b' t').hom.app
        ((SheafOfModules.toSheaf (constantRing Z Λ)).obj J)) q
        (Sheaf.H.map
          (moduleClosedPullbackCoefficientMap i i₂ (t ≫ b) (t' ≫ b') hcomp Λ I J a) q
          (cohomologyPullback i₂ _ q
            (Sheaf.H.map ((inverseImageComp b t).inv.app
              ((SheafOfModules.toSheaf (constantRing X Λ)).obj I)) q
              (cohomologyPullback t _ q x)))) =
      cohomologyPullback t' _ q
        (Sheaf.H.map (moduleClosedPullbackCoefficientMap i i' b b' h Λ I J a) q
          (cohomologyPullback i' _ q x)) :=
  underlyingClosedPullbackCoefficientClass_refinement i i' i₂ b b' t t' h ht hcomp
    (SheafOfModules.toSheaf (constantRing X Λ))
    (SheafOfModules.toSheaf (constantRing Z Λ))
    (moduleInverseImageUnderlyingIso Λ i) I J a q x

/-- The original module closed-class zero condition transports to, and is
detected after, the same actual target refinement. -/
theorem moduleClosedPullbackCoefficientClass_refinement_eq_zero_iff
    (q : ℕ) (x : Sheaf.H.{eT} ((inverseImage b).obj
      ((SheafOfModules.toSheaf (constantRing X Λ)).obj I)) q) :
    Sheaf.H.map
        (moduleClosedPullbackCoefficientMap i i₂ (t ≫ b) (t' ≫ b') hcomp Λ I J a) q
        (cohomologyPullback i₂ _ q
          (Sheaf.H.map ((inverseImageComp b t).inv.app
            ((SheafOfModules.toSheaf (constantRing X Λ)).obj I)) q
            (cohomologyPullback t _ q x))) = 0 ↔
      cohomologyPullback t' _ q
        (Sheaf.H.map (moduleClosedPullbackCoefficientMap i i' b b' h Λ I J a) q
          (cohomologyPullback i' _ q x)) = 0 :=
  underlyingClosedPullbackCoefficientClass_refinement_eq_zero_iff
    i i' i₂ b b' t t' h ht hcomp
    (SheafOfModules.toSheaf (constantRing X Λ))
    (SheafOfModules.toSheaf (constantRing Z Λ))
    (moduleInverseImageUnderlyingIso Λ i) I J a q x

end Modules

end AlgebraicGeometry.Scheme.EtaleCohomology
