/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.CochainComplexPlus.Functoriality
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.Identity
public import Mathlib.AlgebraicGeometry.Modules.Sheaf

/-!
Source: `Quillen/AlgebraicGeometry/Scheme/ProjectiveLine/OriginalLineContractionComplexes.lean`
at LOCAL Quillen
`189a8e779f0c68b2dfc6f8195daebb3e684a5905`. Selection: cut_general;
source ranges [[25, 62]]. Actual objects, maps and hypotheses are preserved.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v w
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry CategoryTheory.Functor

namespace AlgebraicGeometry.Scheme.Modules

/-- The supplied contraction `F ⋙ G ≅ 𝟭 X.Modules` lifted degreewise to integer-indexed cochain
complexes. -/
def cochainContractionIso {X : Scheme.{u}} (F G : X.Modules ⥤ X.Modules)
    [F.Additive] [G.Additive] (e : F ⋙ G ≅ 𝟭 X.Modules) :
    F.mapHomologicalComplex (.up ℤ) ⋙ G.mapHomologicalComplex (.up ℤ) ≅
      𝟭 (CochainComplex X.Modules ℤ) :=
  Functor.mapHomologicalComplexCompIso e (.up ℤ) ≪≫
    Functor.mapHomologicalComplexIdIso X.Modules (.up ℤ)

lemma cochainContractionIso_hom_f {X : Scheme.{u}} (F G : X.Modules ⥤ X.Modules)
    [F.Additive] [G.Additive] (e : F ⋙ G ≅ 𝟭 X.Modules)
    (K : CochainComplex X.Modules ℤ) (n : ℤ) :
    ((cochainContractionIso F G e).hom.app K).f n = e.hom.app (K.X n) := by
  simp [cochainContractionIso]

/-- The supplied contraction `F ⋙ G ≅ 𝟭 X.Modules` lifted to bounded-below cochain complexes. -/
def plusContractionIso {X : Scheme.{u}} (F G : X.Modules ⥤ X.Modules)
    [F.Additive] [G.Additive] (e : F ⋙ G ≅ 𝟭 X.Modules) :
    F.mapCochainComplexPlus ⋙ G.mapCochainComplexPlus ≅
      𝟭 (CochainComplex.Plus X.Modules) :=
  (Functor.mapCochainComplexPlusCompIso F G).symm ≪≫
    NatIso.mapCochainComplexPlus e ≪≫ Functor.mapCochainComplexPlusIdIso X.Modules

lemma plusContractionIso_hom_app {X : Scheme.{u}} (F G : X.Modules ⥤ X.Modules)
    [F.Additive] [G.Additive] (e : F ⋙ G ≅ 𝟭 X.Modules)
    (K : CochainComplex.Plus X.Modules) :
    (plusContractionIso F G e).hom.app K =
      (Functor.mapCochainComplexPlusCompIso F G).inv.app K ≫
        (NatIso.mapCochainComplexPlus e).hom.app K ≫
        (Functor.mapCochainComplexPlusIdIso X.Modules).hom.app K := rfl

lemma plusContractionIso_hom_f {X : Scheme.{u}} (F G : X.Modules ⥤ X.Modules)
    [F.Additive] [G.Additive] (e : F ⋙ G ≅ 𝟭 X.Modules)
    (K : CochainComplex.Plus X.Modules) (n : ℤ) :
    ((plusContractionIso F G e).hom.app K).hom.f n = e.hom.app (K.obj.X n) := by
  simp [plusContractionIso, Functor.mapCochainComplexPlusCompIso,
    NatIso.mapCochainComplexPlus, Functor.mapCochainComplexPlusIdIso]

end AlgebraicGeometry.Scheme.Modules
