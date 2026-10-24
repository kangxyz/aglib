/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Artin.ModuleSheafEquivalence
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Modules.FieldSections
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Modules.Pullback
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Modules.SigmaSections
public import Aglib.AlgebraicGeometry.Stalk.Artinian

/-! # Finite original constructible module sections on actual Artinian schemes

The native residue pullback identifies the original sections of each actual
local Artinian component with sections over its separably closed residue field.
The original stalk-spectrum coproduct and literal component restrictions then
give a finite product. No Noetherian condition on the coefficient ring, torsion,
finite additive carrier, or finite-presentation direct-image theorem is used.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.Modules

universe u r

attribute [local instance] hasSheafifyLarge ModuleCat.Sheaf.hasSheafify

variable (R : Type r) [CommRing R]

/-- The actual module inverse image of a scheme isomorphism, with its native
identity and composition comparisons, forms an equivalence. -/
def moduleInverseImageEquivalenceOfIso {S X : Scheme.{u}} (e : S ≅ X) :
    ModuleSheaf R X ≌ ModuleSheaf R S :=
  CategoryTheory.Equivalence.mk (moduleInverseImage R e.hom) (moduleInverseImage R e.inv)
    ((moduleInverseImageId R X).symm ≪≫
      eqToIso (congrArg (fun f : X ⟶ X => moduleInverseImage R f) e.inv_hom_id).symm ≪≫
      moduleInverseImageComp R e.hom e.inv)
    ((moduleInverseImageComp R e.inv e.hom).symm ≪≫
      eqToIso (congrArg (fun f : S ⟶ S => moduleInverseImage R f) e.hom_inv_id) ≪≫
      moduleInverseImageId R S)

instance moduleInverseImage_isEquivalence_of_isIso {S X : Scheme.{u}} (f : S ⟶ X)
    [IsIso f] : (moduleInverseImage R f).IsEquivalence :=
  (moduleInverseImageEquivalenceOfIso R (asIso f)).isEquivalence_functor

/-- Original sections of a constructible module coefficient on a local Artinian
ring are finite if its actual residue field is separably closed. -/
theorem moduleGlobalSections_finite_of_isConstructible_localArtin
    (A : Type u) [CommRing A] [IsArtinianRing A] [IsLocalRing A]
    [IsSepClosed (IsLocalRing.ResidueField A)]
    {F : ModuleSheaf R (Spec (.of A))} (hF : IsConstructible F) :
    Module.Finite R ((moduleGlobalSections R (Spec (.of A))).obj F) := by
  let f := Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))
  let := Artin.moduleGlobalSectionsPullback_residue_isIso R A F
  let : Module.Finite R ((moduleGlobalSections R
      (Spec (.of (IsLocalRing.ResidueField A)))).obj ((moduleInverseImage R f).obj F)) :=
    moduleGlobalSections_finite_of_isConstructible_field (IsLocalRing.ResidueField A)
      (isConstructible_pullback f hF)
  exact Module.Finite.equiv (asIso (moduleGlobalSectionsPullback R f F)).symm.toLinearEquiv

/-- The original coproduct component coefficient is the original pullback to
that actual stalk spectrum; the comparison retains the original summand map. -/
def moduleStalkComponentIso {X : Scheme.{u}} [IsLocallyArtinian X]
    (F : ModuleSheaf R X) (x : X) :
    (moduleInverseImage R (Sigma.ι (fun y : X => Spec (X.presheaf.stalk y)) x)).obj
      ((moduleInverseImage R (stalkCoproductIso X).hom).obj F) ≅
        (moduleInverseImage R (X.fromSpecStalk x)).obj F :=
  ((moduleInverseImageComp R (stalkCoproductIso X).hom
    (Sigma.ι (fun y : X => Spec (X.presheaf.stalk y)) x)).app F).symm ≪≫
    eqToIso (congrArg (fun f => (moduleInverseImage R f).obj F)
      (stalkCoproductIso_component X x))

/-- Original constructible module sections on an actual Artinian scheme are
finite when its actual residue fields are separably closed. -/
theorem moduleGlobalSections_finite_of_isConstructible_artinian
    (X : Scheme.{u}) [IsArtinianScheme X]
    (hres : ∀ x : X, IsSepClosed (X.residueField x))
    {F : ModuleSheaf R X} (hF : IsConstructible F) :
    Module.Finite R ((moduleGlobalSections R X).obj F) := by
  let C (x : X) := Spec (X.presheaf.stalk x)
  let e := stalkCoproductIso X
  let G : ModuleSheaf R (∐ C) := (moduleInverseImage R e.hom).obj F
  have hcomponent (x : X) : Module.Finite R ((moduleGlobalSections R (C x)).obj
      ((moduleInverseImage R (Sigma.ι C x)).obj G)) := by
    let : IsArtinianRing (X.presheaf.stalk x) := stalk_isArtinian_of_isLocallyArtinian X x
    let : IsSepClosed (IsLocalRing.ResidueField (X.presheaf.stalk x)) := hres x
    let : Module.Finite R ((moduleGlobalSections R (C x)).obj
        ((moduleInverseImage R (X.fromSpecStalk x)).obj F)) :=
      moduleGlobalSections_finite_of_isConstructible_localArtin R (X.presheaf.stalk x)
        (isConstructible_pullback (X.fromSpecStalk x) hF)
    exact Module.Finite.equiv
      ((moduleGlobalSections R (C x)).mapIso (moduleStalkComponentIso R F x).symm).toLinearEquiv
  let : Module.Finite R ((moduleGlobalSections R (∐ C)).obj G) :=
    moduleGlobalSections_finite_of_finite_components R C G hcomponent
  let := Artin.moduleGlobalSectionsPullback_isIso_of_isEquivalence R e.hom F
  exact Module.Finite.equiv (asIso (moduleGlobalSectionsPullback R e.hom F)).symm.toLinearEquiv

end AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.Modules
