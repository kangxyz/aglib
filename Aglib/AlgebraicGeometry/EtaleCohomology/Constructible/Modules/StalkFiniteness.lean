/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.GeometricPoints.InverseImage.Module
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Modules.FieldSections
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Modules.Pullback

/-! # Finite original geometric stalks of constructible module coefficients

Native inverse image and the actual terminal germ reduce this statement to
constructible module sections over a separably closed field. No finiteness
hypothesis on the scheme or its morphisms is required.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.Modules

universe v r

attribute [local instance] hasSheafifyLarge ModuleCat.Sheaf.hasSheafify

variable (R : Type r) [CommRing R]

/-- Every actual geometric stalk of a constructible module coefficient is
finite over its original ring, with independent coefficient universe. -/
theorem moduleGeometricStalk_finite_of_isConstructible
    {X : Scheme.{v}} {Ω : Type v} [Field Ω] [IsSepClosed Ω]
    (η : Spec (.of Ω) ⟶ X) {F : ModuleSheaf R X} (hF : IsConstructible F) :
    Module.Finite R (((pointSmallEtale η).sheafFiber (A := ModuleCat.{v + 1} R)).obj F) := by
  let E := (moduleInverseImage R η).obj F
  let : Module.Finite R (E.obj.obj (op (etaleTerminal (Spec (.of Ω))))) :=
    moduleGlobalSections_finite_of_isConstructible_field Ω (isConstructible_pullback η hF)
  have hstalk : Module.Finite R
      (((pointSmallEtale (𝟙 (Spec (.of Ω)))).sheafFiber (A := ModuleCat.{v + 1} R)).obj E) :=
    Module.Finite.equiv (asIso ((pointSmallEtale (𝟙 (Spec (.of Ω)))).toPresheafFiber
      (etaleTerminal (Spec (.of Ω))) (fieldTerminalPoint Ω) E.obj)).toLinearEquiv
  let : Module.Finite R
      (((siteBaseChange η).sheafPullback (ModuleCat.{v + 1} R)
        X.smallEtaleTopology (Spec (.of Ω)).smallEtaleTopology ⋙
          (pointSmallEtale (𝟙 (Spec (.of Ω)))).sheafFiber).obj F) := hstalk
  let i := eqToIso (congrArg
    (fun f : Spec (.of Ω) ⟶ X =>
      ((pointSmallEtale f).sheafFiber (A := ModuleCat.{v + 1} R)).obj F)
    (Category.id_comp η))
  exact Module.Finite.equiv
    (((geometricModuleStalkInverseImageIso η (𝟙 (Spec (.of Ω))) R).app F).symm ≪≫
      i).toLinearEquiv

end AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.Modules
