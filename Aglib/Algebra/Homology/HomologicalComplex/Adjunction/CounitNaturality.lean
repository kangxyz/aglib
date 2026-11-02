/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.ShortComplex.Adjunction.CounitNaturality
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-!
# Original sections-complex maps and homology counit squares

The degree components are the original natural transformation followed by the
original coefficient-complex map. Their differential compatibility is proved
before any native functors are substituted. Taking the original short complex
recovers exactly the previously constructed sections map and its whole
homology counit square.
-/

@[expose] public section
noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace CategoryTheory.Adjunction

universe u₀ v₀ u₁ v₁ u₂ v₂ u₃ v₃ uι

variable {C₀ : Type u₀} [Category.{v₀} C₀] [Abelian C₀]
  {D₀ : Type u₁} [Category.{v₁} D₀] [Abelian D₀]
  {C₁ : Type u₂} [Category.{v₂} C₁] [Abelian C₁]
  {D₁ : Type u₃} [Category.{v₃} D₁] [Abelian D₁]
  {G₀ : D₀ ⥤ C₀} {G₁ : D₁ ⥤ C₁} [G₀.Additive] [G₁.Additive]
  (A : D₀ ⥤ D₁) (T : C₁ ⥤ C₀) [A.Additive] [T.Additive]
  (η : G₀ ⟶ A ⋙ G₁ ⋙ T)
  {ι : Type uι} {c : ComplexShape ι}
  (K : HomologicalComplex D₀ c) (L : HomologicalComplex D₁ c)
  (ψ : (A.mapHomologicalComplex c).obj K ⟶ L)

/-- The original section-complex map, with its differential law constructed
from the original naturality and coefficient-complex square. -/
def counitSectionsComplexMap :
    (G₀.mapHomologicalComplex c).obj K ⟶
      (T.mapHomologicalComplex c).obj ((G₁.mapHomologicalComplex c).obj L) where
  f i := η.app (K.X i) ≫ T.map (G₁.map (ψ.f i))
  comm' i j _ := by
    change (η.app (K.X i) ≫ T.map (G₁.map (ψ.f i))) ≫ T.map (G₁.map (L.d i j)) =
      G₀.map (K.d i j) ≫ (η.app (K.X j) ≫ T.map (G₁.map (ψ.f j)))
    rw [Category.assoc, ← T.map_comp, ← G₁.map_comp]
    have hψ := ψ.comm i j
    change ψ.f i ≫ L.d i j = A.map (K.d i j) ≫ ψ.f j at hψ
    rw [hψ]
    simp only [Functor.map_comp]
    have hn := η.naturality (K.d i j)
    change G₀.map (K.d i j) ≫ η.app (K.X j) =
      η.app (K.X i) ≫ T.map (G₁.map (A.map (K.d i j))) at hn
    exact ((reassoc_of% hn) (T.map (G₁.map (ψ.f j)))).symm

/-- Taking the original short complex gives the same original sections map. -/
theorem counitSectionsComplexMap_shortComplex (n : ι) :
    (shortComplexFunctor C₀ c n).map (counitSectionsComplexMap A T η K L ψ) =
      counitSectionsMap A T η (K.sc n) (L.sc n)
        ((shortComplexFunctor D₁ c n).map ψ) := by
  ext <;> rfl

variable {F₀ : C₀ ⥤ D₀} {F₁ : C₁ ⥤ D₁}
  [F₀.Additive] [F₁.Additive] [F₀.PreservesHomology] [F₁.PreservesHomology]
  [A.PreservesHomology] [T.PreservesHomology]
  (adj₀ : F₀ ⊣ G₀) (adj₁ : F₁ ⊣ G₁)

/-- The complete original cochain construction carries the original homology
counit square. The right adjoints need not preserve homology. -/
theorem homologyCounitMate_complex_naturality (n : ι) :
    homologyMap (counitSectionsComplexMap A T η K L ψ) n ≫
        ((((G₁.mapHomologicalComplex c).obj L).sc n).mapHomologyIso T).hom ≫
          T.map (adj₁.homologyCounitMate (L.sc n)) =
      adj₀.homologyCounitMate (K.sc n) ≫ η.app (K.homology n) ≫
        T.map (G₁.map (((K.sc n).mapHomologyIso A).inv ≫ homologyMap ψ n)) := by
  change ShortComplex.homologyMap
      ((shortComplexFunctor C₀ c n).map (counitSectionsComplexMap A T η K L ψ)) ≫
        (((L.sc n).map G₁).mapHomologyIso T).hom ≫
          T.map (adj₁.homologyCounitMate (L.sc n)) = _
  rw [counitSectionsComplexMap_shortComplex]
  exact homologyCounitMate_naturality adj₀ adj₁ A T η (K.sc n) (L.sc n)
    ((shortComplexFunctor D₁ c n).map ψ)

end CategoryTheory.Adjunction
