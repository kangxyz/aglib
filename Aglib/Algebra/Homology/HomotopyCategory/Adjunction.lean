/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.HomologicalComplex.Adjunction
public import Mathlib.Algebra.Homology.Localization
public import Mathlib.CategoryTheory.Localization.Adjunction

/-!
# Adjunctions on cochain homotopy categories

Localizing the original degreewise adjunction at homotopy equivalences gives
the adjunction on the actual integer cochain homotopy categories. Its original
quotient-factor squares, unit, counit and chain-adjoint Hom equation are retained.
No K-injectivity or derived-category choice is required.

Source: `Quillen/Algebra/Homology/Adjunction.lean` at frozen dirty Quillen
`6db56ddd3fdb898ef5de29d5fe51a0c61f9ba116`.
Source SHA-256: `1b633acd4a4a8f7639b1946acdfd90261736255b077c863c324777b87b16ac60`.
Selected source lines: 63–119.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v u' v' w
open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Adjunction
variable {C : Type u} [Category.{v} C] [Abelian C]
  {D : Type u'} [Category.{v'} D] [Abelian D]
  {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) [F.Additive] [G.Additive]

/-- The cochain quotient square for the left adjoint. -/
local instance leftHomotopySquare :
    CatCommSq (F.mapHomologicalComplex (.up ℤ)) (HomotopyCategory.quotient C (.up ℤ))
      (HomotopyCategory.quotient D (.up ℤ)) (F.mapHomotopyCategory (.up ℤ)) :=
  ⟨(F.mapHomotopyCategoryFactors (.up ℤ)).symm⟩

/-- The cochain quotient square for the right adjoint. -/
local instance rightHomotopySquare :
    CatCommSq (G.mapHomologicalComplex (.up ℤ)) (HomotopyCategory.quotient D (.up ℤ))
      (HomotopyCategory.quotient C (.up ℤ)) (G.mapHomotopyCategory (.up ℤ)) :=
  ⟨(G.mapHomotopyCategoryFactors (.up ℤ)).symm⟩

/-- Localization at genuine homotopy equivalences gives the original homotopy-category adjunction.
-/
def mapCochainHomotopyCategory : F.mapHomotopyCategory (.up ℤ) ⊣ G.mapHomotopyCategory (.up ℤ) :=
  (adj.mapHomologicalComplex (.up ℤ)).localization
    (HomotopyCategory.quotient C (.up ℤ)) (HomologicalComplex.homotopyEquivalences C (.up ℤ))
    (HomotopyCategory.quotient D (.up ℤ)) (HomologicalComplex.homotopyEquivalences D (.up ℤ))
    (F.mapHomotopyCategory (.up ℤ)) (G.mapHomotopyCategory (.up ℤ))

/-- The homotopy-category unit is the quotient of the original degreewise unit. -/
lemma mapCochainHomotopyCategory_unit_app (K : CochainComplex C ℤ) :
    adj.mapCochainHomotopyCategory.unit.app ((HomotopyCategory.quotient C (.up ℤ)).obj K) =
      (HomotopyCategory.quotient C (.up ℤ)).map ((adj.mapHomologicalComplex (.up ℤ)).unit.app K) :=
        by
  rw [mapCochainHomotopyCategory, Adjunction.localization_unit_app]
  change _ ≫ 𝟙 _ ≫ (G.mapHomotopyCategory (.up ℤ)).map (𝟙 _) = _
  simp

/-- The homotopy-category counit is the quotient of the original degreewise counit. -/
lemma mapCochainHomotopyCategory_counit_app (L : CochainComplex D ℤ) :
    adj.mapCochainHomotopyCategory.counit.app ((HomotopyCategory.quotient D (.up ℤ)).obj L) =
      (HomotopyCategory.quotient D (.up ℤ)).map ((adj.mapHomologicalComplex (.up ℤ)).counit.app L)
        := by
  rw [mapCochainHomotopyCategory, Adjunction.localization_counit_app]
  change (F.mapHomotopyCategory (.up ℤ)).map (𝟙 _) ≫ 𝟙 _ ≫ _ = _
  simp

/-- On original complexes the homotopy Hom equivalence has literal quotient endpoints. -/
def cochainHomotopyHomEquiv (K : CochainComplex C ℤ) (L : CochainComplex D ℤ) :
    ((HomotopyCategory.quotient D (.up ℤ)).obj ((F.mapHomologicalComplex (.up ℤ)).obj K) ⟶
      (HomotopyCategory.quotient D (.up ℤ)).obj L) ≃
    ((HomotopyCategory.quotient C (.up ℤ)).obj K ⟶
      (HomotopyCategory.quotient C (.up ℤ)).obj ((G.mapHomologicalComplex (.up ℤ)).obj L)) :=
  adj.mapCochainHomotopyCategory.homEquiv _ _

/-- The homotopy adjunction agrees exactly with the original degreewise chain adjunction. -/
@[simp]
lemma cochainHomotopyHomEquiv_map (K : CochainComplex C ℤ) (L : CochainComplex D ℤ)
    (f : (F.mapHomologicalComplex (.up ℤ)).obj K ⟶ L) :
    adj.cochainHomotopyHomEquiv K L ((HomotopyCategory.quotient D (.up ℤ)).map f) =
      (HomotopyCategory.quotient C (.up ℤ)).map
        ((adj.mapHomologicalComplex (.up ℤ)).homEquiv K L f) := by
  change adj.mapCochainHomotopyCategory.unit.app _ ≫
    (G.mapHomotopyCategory (.up ℤ)).map ((HomotopyCategory.quotient D (.up ℤ)).map f) = _
  erw [mapCochainHomotopyCategory_unit_app adj K, CategoryTheory.Functor.mapHomotopyCategory_map,
    ← CategoryTheory.Functor.map_comp]
  rfl

end CategoryTheory.Adjunction
