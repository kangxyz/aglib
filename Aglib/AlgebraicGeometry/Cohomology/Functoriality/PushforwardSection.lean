/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Functoriality.PushforwardComposition
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.Identity

/-!
Source: `Quillen/AlgebraicGeometry/Scheme/Sheaf/DerivedPushforwardSection.lean` at LOCAL Quillen
`189a8e779f0c68b2dfc6f8195daebb3e684a5905`. Selection: whole_general_prerequisite;
source ranges [[1, 70]]. Actual objects, maps and hypotheses are preserved.
-/

/-!
# Derived direct image along a geometric section

The original direct-image composition, geometric section equality, and identity
comparison identify the composite derived direct image with the identity. The
comparison retains both installed derived units. The original derived direct
image also carries its installed shift and triangulated structures.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Modules
/-- Standard original module-sheaf derived categories. -/
local instance pushforwardSectionStandardDerived (X : Scheme.{u}) :
    HasDerivedCategory.{u + 1} X.Modules := HasDerivedCategory.standard _
/-- The original installed derived pushforward commutes with the actual shifts. -/
instance derivedPushforwardPlusCommShift {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (derivedPushforwardPlus f).CommShift ℤ := by
  unfold derivedPushforwardPlus
  infer_instance
/-- The original installed derived pushforward preserves distinguished triangles. -/
instance derivedPushforwardPlusTriangulated {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (derivedPushforwardPlus f).IsTriangulated := by
  unfold derivedPushforwardPlus
  infer_instance
variable {X Y : Scheme.{u}} (s : Y ⟶ X) (p : X ⟶ Y) (h : s ≫ p = 𝟙 Y)
/-- The original direct-image composition along a geometric section. -/
def sectionPushforwardIso : Scheme.Modules.pushforward s ⋙ Scheme.Modules.pushforward p ≅
    𝟭 Y.Modules :=
  Scheme.Modules.pushforwardComp s p ≪≫ Scheme.Modules.pushforwardCongr h ≪≫
    Scheme.Modules.pushforwardId Y
/-- The canonical derived section comparison retains the original geometric section equality. -/
def derivedPushforwardPlusSectionIso :
    derivedPushforwardPlus s ⋙ derivedPushforwardPlus p ≅ 𝟭 (DerivedCategory.Plus Y.Modules) :=
  (derivedPushforwardFunctorCompIso s p).symm ≪≫
    (Scheme.Modules.pushforward s ⋙ Scheme.Modules.pushforward p).rightDerivedFunctorPlusIso
      (sectionPushforwardIso s p h) ≪≫
    Functor.rightDerivedFunctorPlusIdIso Y.Modules
/-- The section comparison retains the original geometric composition and both installed units. -/
theorem derivedPushforwardPlusSectionIso_unit (K : CochainComplex.Plus Y.Modules) :
    (Functor.rightDerivedFunctorPlusCompUnit
      (Scheme.Modules.pushforward s) (Scheme.Modules.pushforward p)).app K ≫
        (derivedPushforwardPlusSectionIso s p h).hom.app (DerivedCategory.Plus.Q.obj K) =
      DerivedCategory.Plus.Q.map
        ((NatIso.mapCochainComplexPlus (sectionPushforwardIso s p h)).hom.app K ≫
          (Functor.mapCochainComplexPlusIdIso Y.Modules).hom.app K) := by
  have hE := (Scheme.Modules.pushforward s ⋙
    Scheme.Modules.pushforward p).rightDerivedFunctorPlusIso_hom_app
      (sectionPushforwardIso s p h) K
  rw [← derivedPushforwardFunctorCompIso_unit s p K]
  change (_ ≫ _) ≫ (_ ≫ _ ≫ _) = _
  simp only [Iso.symm_hom, Category.assoc]
  erw [Iso.hom_inv_id_app_assoc]
  rw [← Category.assoc]
  erw [hE]
  rw [Category.assoc, Functor.rightDerivedFunctorPlusIdIso_unit, ← Functor.map_comp]
end AlgebraicGeometry.Scheme.Modules
