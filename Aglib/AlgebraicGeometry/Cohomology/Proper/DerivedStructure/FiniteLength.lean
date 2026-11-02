/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Proper.DerivedStructure.Basic
public import Aglib.AlgebraicGeometry.Cohomology.DirectImage.ResolutionSections.Derived
public import Aglib.AlgebraicGeometry.Cohomology.Proper.FiniteLength
public import Aglib.AlgebraicGeometry.Cohomology.Proper.StructureSheaf.Coefficient
public import Aglib.AlgebraicGeometry.Morphisms.Proper.BirationalSurface
public import Aglib.AlgebraicGeometry.Properties.Normal.Affine
public import Aglib.AlgebraicGeometry.Modules.DerivedCategory.Basic

/-!
# Finite length of the original derived structural H1

The original proper birational map is an isomorphism on the punctured
spectrum. Its actual derived section comparison transports finite length
without changing the source, scalar action or cohomology backend.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.QuasiCoherent

universe u

namespace AlgebraicGeometry.Scheme.Cohomology

attribute [local instance] AlgebraicGeometry.Scheme.Modules.standardHasDerivedCategory

local instance structureFiniteLengthModuleDerived (A : Type u) [CommRing A] :
    HasDerivedCategory.{u + 1} (ModuleCat.{u} A) := HasDerivedCategory.standard _

/-- The punctured isomorphism and original section comparison give finite length
for the installed H1, with its original structural action. -/
theorem moduleDerivedStructure_homologyOne_finiteLength_of_proper_birational_surface
    {A : Type u} [CommRing A] [IsDomain A] [IsLocalRing A]
    [IsNoetherianRing A] [IsIntegrallyClosed A]
    {X : Scheme.{u}} [IsIntegral X]
    (f : X ⟶ Spec (.of A)) [IsProper f] [IsDominant f]
    (hff : IsIso (CommRingCat.ofHom (Scheme.functionFieldMap f)))
    (hA : ringKrullDim A = 2)
    (IX : InjectiveResolution (SheafOfModules.unit X.ringCatSheaf : X.Modules)) :
    IsFiniteLength A
      ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} A) 1).obj
        (moduleDerivedStructure X (f.appTop.hom.comp (ΓSpecIso (.of A)).inv.hom))) := by
  let O : X.Modules := SheafOfModules.unit X.ringCatSheaf
  let α := f.appTop.hom.comp (ΓSpecIso (.of A)).inv.hom
  have hiso : IsIso (f ∣_ localPuncturedSpectrum A) :=
    f.isIso_restrict_of_stalk_dimension_le_one hff
      (fun p => (isIntegrallyClosed_and_isDomain_stalk_Spec A p).symm)
      (localPuncturedSpectrum A) (by
        intro p hp
        exact ringKrullDim_stalk_le_one_of_ne_closedPoint A hA.le p
          ((mem_localPuncturedSpectrum A p).mp hp))
  let := moduleCohomologyModuleOfHom X α O 1
  have hlen : IsFiniteLength A (Sheaf.H.{u + 1} (moduleAddSheaf X O) 1) :=
    moduleCohomology_isFiniteLength_of_proper_of_isIso_puncturedSpectrum
      A f hiso O (affineLocallyFiniteType_unit X) 1 (by decide)
  exact (moduleDerivedGlobalSectionsSingleCohomologyLinearEquiv X α IX 1).symm.isFiniteLength
    hlen

end AlgebraicGeometry.Scheme.Cohomology
