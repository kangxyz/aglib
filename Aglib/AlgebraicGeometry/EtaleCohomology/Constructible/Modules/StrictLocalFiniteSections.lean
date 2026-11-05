/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Finite.ModuleStalkProduct
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Modules.ConnectedTorsionSections
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Modules.StalkFiniteness
public import Mathlib.Algebra.Category.ModuleCat.Products
public import Mathlib.LinearAlgebra.Pi

/-! # Finite original module sections over finite strictly local bases

Each actual component residue point has finite module stalk, by constructible
pullback and the genuine field section theorem. The original linear stalk
product then proves finite generation of original sections. No Artinian,
Noetherian, torsion or coefficient cardinality hypothesis is imposed.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.Modules

universe u v r

attribute [local instance] hasSheafifyLarge ModuleCat.Sheaf.hasSheafify

variable (R : Type r) [CommRing R]

/-- Original sections of a constructible module sheaf on a finite algebra over
a strictly henselian local base are finite. The algebra may be zero, so the
empty component product is included. All three ring universes are independent. -/
theorem moduleGlobalSections_finite_of_isConstructible_finite_strictLocal
    (A : Type v) [CommRing A] (B : Type u) [CommRing B]
    [HenselianLocalRing B] [IsSepClosed (IsLocalRing.ResidueField B)]
    [Algebra B A] [Module.Finite B A]
    {F : ModuleSheaf R (Spec (.of A))} (hF : IsConstructible F) :
    Module.Finite R ((moduleGlobalSections R (Spec (.of A))).obj F) := by
  let M := Finite.localComponentModuleStalk R A B F
  have hfinite (p : MaximalSpectrum A) : Module.Finite R (M p) := by
    let := HenselianLocalRing.henselian_localizationAtPrime B A p.asIdeal
    let := HenselianLocalRing.residueField_isSepClosed_localizationAtPrime B A p.asIdeal
    exact moduleGeometricStalk_finite_of_isConstructible R
      (LocalRing.residueSpecMap (Localization.AtPrime p.asIdeal) ≫
        Finite.localComponentInclusion A p) hF
  let := hfinite
  let : _root_.Finite (MaximalSpectrum A) := Module.finiteAlgebra_maximalSpectrum_finite B A
  let : Module.Finite R (∀ p, M p) := inferInstance
  exact Module.Finite.equiv
    ((Finite.finiteModuleStalkProductIso R A B F) ≪≫
      ModuleCat.piIsoPi.{r, v, v + 1} M).symm.toLinearEquiv

end AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.Modules
