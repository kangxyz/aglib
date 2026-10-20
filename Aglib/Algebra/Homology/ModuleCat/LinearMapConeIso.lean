/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.Algebra.Homology.MappingCone.Iso
public import Aglib.Algebra.Homology.ModuleCat.LinearMapConeShift

/-! # Original two-term complexes under linear coordinate isomorphisms

The single-map cone and its explicit minus-one shift retain the given source and target
coordinate isomorphisms and the original commuting differential square.
-/

/-!
Source: `quillen-k-theory/Quillen/Aglib/Algebra/Homology/ModuleCat/LinearMapConeIso.lean` from the
supplied frozen Quillen snapshot.
SHA-256: `bae4cc884a53b3552e6e88790379de102741f740ef6c777da709c924970e2c90`.
Only native objects, maps and mathematical namespaces are used in this extraction.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe u v
namespace ModuleCat
variable {R : Type u} [CommRing R]
variable {A B A' B' : Type v} [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
variable [AddCommGroup A'] [Module R A'] [AddCommGroup B'] [Module R B']

/-- Specified linear coordinate isomorphisms induce an actual isomorphism of the original
cones. -/
def linearMapConeIsoOfEquivs (d : A →ₗ[R] B) (d' : A' →ₗ[R] B')
    (a : A ≃ₗ[R] A') (b : B ≃ₗ[R] B')
    (h : b.toLinearMap.comp d = d'.comp a.toLinearMap) : linearMapCone d ≅ linearMapCone d' := by
  let F := HomologicalComplex.single (ModuleCat.{v} R) (.up ℤ) 0
  apply CochainComplex.mappingCone.isoOfIso (F.map (ModuleCat.ofHom d))
    (F.map (ModuleCat.ofHom d')) (F.mapIso a.toModuleIso) (F.mapIso b.toModuleIso)
  change F.map (ModuleCat.ofHom d) ≫ F.map b.toModuleIso.hom =
    F.map a.toModuleIso.hom ≫ F.map (ModuleCat.ofHom d')
  rw [← F.map_comp, ← F.map_comp]
  congr 1
  apply ModuleCat.hom_ext
  exact h

/-- The same coordinate isomorphisms preserve the explicit shifted Cech complexes. -/
def linearMapCechIsoOfEquivs (d : A →ₗ[R] B) (d' : A' →ₗ[R] B')
    (a : A ≃ₗ[R] A') (b : B ≃ₗ[R] B')
    (h : b.toLinearMap.comp d = d'.comp a.toLinearMap) :
    linearMapCechComplex d ≅ linearMapCechComplex d' :=
  (shiftFunctor _ (-1 : ℤ)).mapIso (linearMapConeIsoOfEquivs d d' a b h)

end ModuleCat
