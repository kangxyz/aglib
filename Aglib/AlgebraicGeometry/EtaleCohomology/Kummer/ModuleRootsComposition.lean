/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Kummer.RootsOfUnityInverseImage
public import Aglib.CategoryTheory.Adjunction.Mates.ScalarForgetting
public import Aglib.AlgebraicGeometry.EtaleCohomology.Kummer.RootsComposition
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Coefficients.UnderlyingComposition

/-!
# Composition of the original module roots inverse-image isomorphisms

Faithful scalar forgetting reflects the intrinsic roots composition equation through the
original module/abelian inverse-image comparison. The existing module roots isomorphism is
retained; no coefficient marking, geometric point or new comparison model is introduced.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open GroupCohomology.Kummer.Coefficients GroupCohomology.Kummer.CoefficientBaseChange

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

universe u

attribute [local instance] hasSheafifyLarge hasSheafifyModules
  moduleForget_preservesSheafification

variable {X Y Z : Scheme.{u}} (f : Y ⟶ X) (g : Z ⟶ Y)
  (n : ℕ) (hn : 0 < n) (hinv : IsUnit (n : Γ(X, ⊤)))

/-- The actual module roots isomorphisms respect the whole original inverse-image comparison. -/
theorem moduleRootsOfUnityInverseImageIso_comp :
    (moduleInverseImageCompIso (ULift.{u + 1} (ZMod n)) f g).hom.app (moduleRootsOfUnity X n) ≫
      (moduleInverseImage g (ULift.{u + 1} (ZMod n))).map
        (moduleRootsOfUnityInverseImageIso f n hn hinv).hom ≫
      (moduleRootsOfUnityInverseImageIso g n hn (levelInvertible f n hinv)).hom =
    (moduleRootsOfUnityInverseImageIso (g ≫ f) n hn hinv).hom := by
  let Λ := ULift.{u + 1} (ZMod n)
  let Q := SheafOfModules.toSheaf (constantRing Z Λ)
  let F := moduleRootsOfUnity X n
  have hc : Q.map ((moduleInverseImageCompIso Λ f g).hom.app F) ≫
      (moduleInverseImageUnderlyingIso Λ g).hom.app ((moduleInverseImage f Λ).obj F) ≫
      (inverseImage g).map ((moduleInverseImageUnderlyingIso Λ f).hom.app F) =
    (moduleInverseImageUnderlyingIso Λ (g ≫ f)).hom.app F ≫
      (inverseImageComp f g).hom.app
        ((SheafOfModules.toSheaf (constantRing X Λ)).obj F) := by
    have h := hom_square_of_inv ((moduleInverseImageUnderlyingIso Λ (g ≫ f)).app F)
      (((moduleInverseImageUnderlyingIso Λ g).app ((moduleInverseImage f Λ).obj F)) ≪≫
        (inverseImage g).mapIso ((moduleInverseImageUnderlyingIso Λ f).app F))
      (Q.map ((moduleInverseImageCompIso Λ f g).hom.app F))
      ((inverseImageComp f g).hom.app
        ((SheafOfModules.toSheaf (constantRing X Λ)).obj F)) (by
        simpa only [Iso.trans_inv, Functor.mapIso_inv, Iso.app_inv, Category.assoc] using
          moduleInverseImageUnderlyingIso_inv_comp Λ f g F)
    simpa only [Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom, Category.assoc] using h
  apply Q.map_injective
  apply (cancel_mono (moduleRootsOfUnityUnderlyingIso Z n).hom).mp
  rw [Q.map_comp, Q.map_comp, Category.assoc, Category.assoc,
    moduleRootsOfUnityInverseImageIso_underlying g,
    moduleRootsOfUnityInverseImageIso_underlying (g ≫ f)]
  have he := (moduleInverseImageUnderlyingIso Λ g).hom.naturality
    (moduleRootsOfUnityInverseImageIso f n hn hinv).hom
  change Q.map ((moduleInverseImage g Λ).map
      (moduleRootsOfUnityInverseImageIso f n hn hinv).hom) ≫
      (moduleInverseImageUnderlyingIso Λ g).hom.app (moduleRootsOfUnity Y n) =
    (moduleInverseImageUnderlyingIso Λ g).hom.app ((moduleInverseImage f Λ).obj F) ≫
      (inverseImage g).map ((SheafOfModules.toSheaf (constantRing Y Λ)).map
        (moduleRootsOfUnityInverseImageIso f n hn hinv).hom) at he
  rw [reassoc_of% he, ← Functor.map_comp_assoc, moduleRootsOfUnityInverseImageIso_underlying f]
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% hc]
  have ht := (inverseImageComp f g).hom.naturality (moduleRootsOfUnityUnderlyingIso X n).hom
  change (inverseImage (g ≫ f)).map (moduleRootsOfUnityUnderlyingIso X n).hom ≫
      (inverseImageComp f g).hom.app (mu X n) =
    (inverseImageComp f g).hom.app
      ((SheafOfModules.toSheaf (constantRing X Λ)).obj F) ≫
      (inverseImage g).map ((inverseImage f).map (moduleRootsOfUnityUnderlyingIso X n).hom) at ht
  rw [reassoc_of% ht.symm,
    GroupCohomology.Kummer.CoefficientBaseChange.rootsPullbackIso_comp]

/-- Equality transport preserves the original module roots inverse-image map. -/
theorem moduleRootsOfUnityInverseImageIso_eqToHom {f g : Y ⟶ X} (h : f = g) :
    eqToHom (congrArg (fun j => (moduleInverseImage j (ULift.{u + 1} (ZMod n))).obj
        (moduleRootsOfUnity X n)) h) ≫
      (moduleRootsOfUnityInverseImageIso g n hn hinv).hom =
        (moduleRootsOfUnityInverseImageIso f n hn hinv).hom := by
  subst g
  exact Category.id_comp _

end AlgebraicGeometry.Scheme.EtaleCohomology
