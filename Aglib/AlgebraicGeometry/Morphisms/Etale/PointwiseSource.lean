/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Etale.FaithfullyFlatSource
public import Aglib.AlgebraicGeometry.Morphisms.Etale.At
public import Aglib.AlgebraicGeometry.Morphisms.Etale.Locus

/-!
# Pointwise etale descent from an etale source neighborhood

The proof uses the actual three stalks and their original composable stalk
maps. Local finite presentation of the original morphism and Noetherianity
of its specified target stalk remain explicit. No replacement local rings,
faithful-flatness of a whole target cover, or etaleness of an entire target
base change is required.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Hom

universe u

/-- Etaleness descends at the image of a specified etale source-neighborhood
point when the original morphism is locally finitely presented and its target
stalk is Noetherian. All local algebras come from the original stalk maps. -/
theorem etaleAt_of_etale_source_of_noetherian
    {W Z X : Scheme.{u}} (π : W ⟶ Z) (f : Z ⟶ X)
    [Etale π] [Etale (π ≫ f)] [LocallyOfFinitePresentation f] (w : W)
    [IsNoetherianRing (X.presheaf.stalk (f (π w)))] : f.etaleAt (π w) := by
  let A := X.presheaf.stalk (f (π w))
  let B := Z.presheaf.stalk (π w)
  let C := W.presheaf.stalk w
  let : Algebra A B := (f.stalkMap (π w)).hom.toAlgebra
  let : Algebra B C := (π.stalkMap w).hom.toAlgebra
  let : Algebra A C := ((π ≫ f).stalkMap w).hom.toAlgebra
  let : IsScalarTower A B C := IsScalarTower.of_algebraMap_eq' (by
    change ((π ≫ f).stalkMap w).hom = (π.stalkMap w).hom.comp (f.stalkMap (π w)).hom
    exact congrArg CommRingCat.Hom.hom (stalkMap_comp π f w))
  let : IsLocalHom (algebraMap A B) := f.toLRSHom.prop (π w)
  let : IsLocalHom (algebraMap B C) := π.toLRSHom.prop w
  let : Algebra.EssFiniteType A B := LocallyOfFiniteType.stalkMap f (π w)
  let : Module.Flat A C := Flat.stalkMap (π ≫ f) w
  let : Module.Flat B C := Flat.stalkMap π w
  let : Module.FaithfullyFlat B C := Module.FaithfullyFlat.of_flat_of_isLocalHom
  let : Algebra.FormallyEtale B C := LocalRing.Etale.etale_stalkMap_formallyEtale π w
  let : Algebra.FormallyUnramified A C := FormallyUnramified.stalkMap (π ≫ f) w
  have h : (f.stalkMap (π w)).hom.FormallyEtale :=
    Algebra.FormallyEtale.of_faithfullyFlat_source_of_noetherian A B C
  exact LocalRing.Etale.exists_etale_neighborhood_of_stalkMap_formallyEtale f (π w) h

end AlgebraicGeometry.Scheme.Hom
