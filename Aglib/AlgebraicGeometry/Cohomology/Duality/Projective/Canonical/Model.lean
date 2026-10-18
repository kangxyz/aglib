/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.ClosedImmersion.RightAdjoint
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.InjectiveResolution
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.Homology
public import Aglib.CategoryTheory.Abelian.Injective.MapAugmentation
public import Aglib.Algebra.Homology.Embedding.MapExtend

/-!
# A common original injective model for the canonical homology maps

The installed global closed right adjoint is compared with its original
injective-resolution model. Actual open restriction commutes with homology
and with the original ordinary closed right adjoint. Restricting one fixed
ambient resolution therefore supplies the local models used in the
canonical homology maps, with no assumed local purity-comparison family.
-/

@[expose] public section
noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry

universe u
namespace AlgebraicGeometry.Scheme.Modules

/-- The standard derived-category model for modules on `Z`, used locally. -/
local instance canonicalModelStandardDerived (Z : Scheme.{u}) :
    HasDerivedCategory.{u + 1} Z.Modules := HasDerivedCategory.standard _

variable {X P : Scheme.{u}} (i : X ⟶ P) [IsClosedImmersion i]
  {L : P.Modules} (J : InjectiveResolution L)

/-- The original derived unit and original resolution inclusion identify the actual native
homology with homology of the sole ordinary closed-adjoint resolution model. -/
def closedImmersionModelHomologyIso (c : ℤ) :
    (DerivedCategory.Plus.homologyFunctor X.Modules c).obj
      ((closedImmersionRightAdjoint i).rightDerivedFunctorPlus.obj
        ((DerivedCategory.Plus.singleFunctor P.Modules 0).obj L)) ≅
      (((closedImmersionRightAdjoint i).mapHomologicalComplex (.up ℤ)).obj
        J.cochainComplex).homology c :=
  (DerivedCategory.Plus.homologyFunctor X.Modules c).mapIso
    (J.rightDerivedFunctorPlusIso (closedImmersionRightAdjoint i)).symm ≪≫
    (DerivedCategory.Plus.homologyFunctorFactors (A := X.Modules) c).app
      ((closedImmersionRightAdjoint i).mapCochainComplexPlus.obj J.cochainComplexPlus)

variable {W : Scheme.{u}} (a : W ⟶ X) [IsOpenImmersion a]

/-- Actual open restriction of the native homology retains the same original sheaf model. -/
def closedImmersionRestrictedModelHomologyIso (c : ℤ) :
    ((DerivedCategory.Plus.homologyFunctor X.Modules c).obj
      ((closedImmersionRightAdjoint i).rightDerivedFunctorPlus.obj
        ((DerivedCategory.Plus.singleFunctor P.Modules 0).obj L))).restrict a ≅
    (((restrictFunctor a).mapHomologicalComplex (.up ℤ)).obj
      (((closedImmersionRightAdjoint i).mapHomologicalComplex (.up ℤ)).obj
        J.cochainComplex)).homology c :=
  (restrictFunctor a).mapIso (closedImmersionModelHomologyIso i J c) ≪≫
    (((((closedImmersionRightAdjoint i).mapHomologicalComplex (.up ℤ)).obj
      J.cochainComplex).sc c).mapHomologyIso (restrictFunctor a)).symm

section AmbientRestriction
variable {V : Scheme.{u}} (j : V ⟶ P) [IsOpenImmersion j]

/-- The literal restriction of the fixed original ambient injective resolution. -/
def canonicalAmbientChartResolution : InjectiveResolution (L.restrict j) := by
  let F := restrictFunctor j
  let : QuasiIso (J.mapAugmentation F) := by
    rw [InjectiveResolution.mapAugmentation_eq]
    infer_instance
  exact {
    cocomplex := (F.mapHomologicalComplex (.up ℕ)).obj J.cocomplex
    injective n := by
      change Injective (F.obj (J.cocomplex.X n))
      infer_instance
    ι := J.mapAugmentation F }

variable (b : W ⟶ V) [IsClosedImmersion b] (h : IsPullback a b i j)

/-- The actual ordinary closed-adjoint open comparison on that same fixed ambient model. -/
def closedImmersionModelOpenIso :
    ((restrictFunctor a).mapHomologicalComplex (.up ℤ)).obj
      (((closedImmersionRightAdjoint i).mapHomologicalComplex (.up ℤ)).obj J.cochainComplex) ≅
    ((closedImmersionRightAdjoint b).mapHomologicalComplex (.up ℤ)).obj
      (canonicalAmbientChartResolution J j).cochainComplex :=
  (Functor.mapHomologicalComplexCompIso
    (closedImmersionRightAdjointOpenIso a b i j h) (.up ℤ)).app J.cochainComplex ≪≫
    (Functor.mapHomologicalComplexCompIso
      (Iso.refl (restrictFunctor j ⋙ closedImmersionRightAdjoint b)) (.up ℤ)).symm.app
        J.cochainComplex ≪≫
    ((closedImmersionRightAdjoint b).mapHomologicalComplex (.up ℤ)).mapIso
      (J.cocomplex.mapExtendIso (restrictFunctor j) ComplexShape.embeddingUpNat)

end AmbientRestriction
end AlgebraicGeometry.Scheme.Modules
