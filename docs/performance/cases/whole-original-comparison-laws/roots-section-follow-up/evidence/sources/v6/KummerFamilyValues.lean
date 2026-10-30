/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant.TriangleCoherence
public import Aglib.AlgebraicGeometry.EtaleCohomology.BaseChangeMap
public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.SectionPullback
public import Aglib.AlgebraicGeometry.EtaleCohomology.Kummer.BoundaryNaturality
public import Aglib.AlgebraicGeometry.EtaleCohomology.Kummer.SectionPullback

/-! # Original Kummer classes as fixed-coefficient family values

The comparison retains the original roots pullback isomorphism and the
original section pullback. These legacy pointed headers delegate to the
intrinsic SectionPullback producer; its new core uses actual point-free
coefficient coherence. The parameter family need not be connected.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.PreGaloisCategory
open AlgebraicGeometry.Scheme.FiniteEtale (fiberToFinite)
open AlgebraicGeometry.Scheme.EtaleCohomology.PointedNaturality
open GroupCohomology.Kummer.Coefficients GroupCohomology.Kummer.CoefficientBaseChange

universe u w w'

namespace AlgebraicGeometry.Scheme.EtaleCohomology.KummerFamilyValues

attribute [local instance] hasSheafifyLarge

variable {X : Scheme.{u}} {D : Type u} [Field D] [IsSepClosed D]
  (z : Spec (.of D) ⟶ X)
  [GaloisCategory (Scheme.FiniteEtale X)]
  [PreGaloisCategory.FiberFunctor (fiberToFinite z)]

include z

/-- The original roots coefficient map at the identity is the native unit
comparison, proved from the actual composition law. -/
theorem rootsPullbackIso_identity (n : ℕ) (hn : 0 < n)
    (hinv : IsUnit (n : Γ(X, ⊤))) :
    (rootsPullbackIso (𝟙 X) n hn hinv).hom = (inverseImageId X).hom.app (mu X n) := by
  exact (fun (_ : IsSepClosed D) (_ : GaloisCategory (Scheme.FiniteEtale X))
      (_ : PreGaloisCategory.FiberFunctor (fiberToFinite z)) =>
    Kummer.SectionPullback.rootsPullbackIso_identity X n hn hinv)
    inferInstance inferInstance inferInstance

/-- The literal roots coefficient maps contract along an actual section. -/
theorem roots_section_coefficients {Y : Scheme.{u}} (r : Y ⟶ X) (a : X ⟶ Y)
    (ha : a ≫ r = 𝟙 X) (n : ℕ) (hn : 0 < n)
    (hinv : IsUnit (n : Γ(X, ⊤))) :
    (inverseImage a).map (rootsPullbackIso r n hn hinv).hom ≫
        (rootsPullbackIso a n hn (levelInvertible r n hinv)).hom =
      (sectionCoefficientIso r a ha (mu X n)).hom := by
  exact (fun (_ : IsSepClosed D) (_ : GaloisCategory (Scheme.FiniteEtale X))
      (_ : PreGaloisCategory.FiberFunctor (fiberToFinite z)) =>
    Kummer.SectionPullback.roots_section_coefficients r a ha n hn hinv)
    inferInstance inferInstance inferInstance

/-- Pulling a Kummer family class to the fixed roots coefficient and then to
an actual section is exactly the original Kummer cohomology pullback. -/
theorem sectionPullback_roots {Y : Scheme.{u}} (r : Y ⟶ X) (a : X ⟶ Y)
    (ha : a ≫ r = 𝟙 X) (n : ℕ) (hn : 0 < n)
    (hinv : IsUnit (n : Γ(X, ⊤)))
    [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]
    [HasExt.{w'} (AbelianSheaf.{u, u + 1} Y)]
    (c : H1Etale.{u, u + 1, w'} Y (mu Y n)) :
    sectionPullback r a ha (mu X n)
        (coefficientMap (rootsPullbackIso r n hn hinv).inv c) =
      Kummer.rootsCohomologyPullback a n hn (levelInvertible r n hinv) 1 c := by
  exact (fun (_ : IsSepClosed D) (_ : GaloisCategory (Scheme.FiniteEtale X))
      (_ : PreGaloisCategory.FiberFunctor (fiberToFinite z)) =>
    Kummer.SectionPullback.sectionPullback_roots r a ha n hn hinv c)
    inferInstance inferInstance inferInstance

end AlgebraicGeometry.Scheme.EtaleCohomology.KummerFamilyValues
