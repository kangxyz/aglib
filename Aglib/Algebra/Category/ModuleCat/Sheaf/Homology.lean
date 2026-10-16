/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.ShortComplex.Adjunction.Reflection
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Homology.Functor

/-!
# Original presheaf homology and module-sheaf homology

Sheafification of the actual homology of the underlying module-presheaf
complex is canonically the original module-sheaf homology. The comparison
uses exact native sheafification and its original counit. Its presheaf unit
is the actual reflection unit followed by that comparison, and becomes
invertible after sheafification. Forgetting the sheaf condition is not
assumed to preserve homology. Ring, module, site and index universes are
independent.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

namespace SheafOfModules

universe r m c h w

variable {C : Type c} [Category.{h} C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{r})
    [HasSheafify J AddCommGrpCat.{m}] [J.WEqualsLocallyBijective AddCommGrpCat.{m}]

local instance sheafification_additive :
    (PresheafOfModules.sheafification.{m} (𝟙 R.obj)).Additive :=
  Functor.additive_of_preserves_binary_products _

-- Keep the literal forgetful right-adjoint head when applying the generic comparison.
-- Both maps are the original native unit and counit; only their functor type is fixed.
/-- The native sheafification adjunction with the literal forgetful right-adjoint head.
Its unit and counit are exactly the original native unit and counit. -/
def sheafificationForgetAdjunction :
    PresheafOfModules.sheafification.{m} (𝟙 R.obj) ⊣ SheafOfModules.forget.{m} R where
  unit := (PresheafOfModules.sheafificationAdjunction.{m} (𝟙 R.obj)).unit
  counit := (PresheafOfModules.sheafificationAdjunction.{m} (𝟙 R.obj)).counit
  left_triangle_components :=
    (PresheafOfModules.sheafificationAdjunction.{m} (𝟙 R.obj)).left_triangle_components
  right_triangle_components :=
    (PresheafOfModules.sheafificationAdjunction.{m} (𝟙 R.obj)).right_triangle_components

variable {ι : Type w} {d : ComplexShape ι}
    (K : HomologicalComplex (SheafOfModules.{m} R) d) (i : ι)

/-- Exact native sheafification recovers the original homology sheaf from the actual
underlying module-presheaf complex. -/
def sheafificationHomologyIso :
    (PresheafOfModules.sheafification.{m} (𝟙 R.obj)).obj
        ((((SheafOfModules.forget.{m} R).mapHomologicalComplex d).obj K).homology i) ≅
      K.homology i :=
  (sheafificationForgetAdjunction R).reflectedHomologyIso (K.sc i)

/-- The canonical unit from actual presheaf homology to the underlying original
homology sheaf, using the original sheafification unit. -/
def homologyPresheafUnit :
    (((SheafOfModules.forget.{m} R).mapHomologicalComplex d).obj K).homology i ⟶
      (SheafOfModules.forget.{m} R).obj (K.homology i) :=
  (sheafificationForgetAdjunction R).homologyReflectionUnit (K.sc i)

/-- The actual unit is normalized by the original sheafification counit. -/
@[reassoc]
theorem sheafification_map_homologyPresheafUnit_counit :
    (PresheafOfModules.sheafification.{m} (𝟙 R.obj)).map (homologyPresheafUnit R K i) ≫
        (PresheafOfModules.sheafificationAdjunction.{m} (𝟙 R.obj)).counit.app (K.homology i) =
      (sheafificationHomologyIso R K i).hom := by
  dsimp only [homologyPresheafUnit, sheafificationHomologyIso,
    CategoryTheory.Adjunction.homologyReflectionUnit]
  let adj := sheafificationForgetAdjunction R
  have he := adj.counit.naturality (adj.reflectedHomologyIso (K.sc i)).hom
  dsimp only [Functor.comp_map, Functor.id_map] at he
  rw [Functor.map_comp, Category.assoc]
  erw [he]
  rw [← Category.assoc]
  erw [adj.left_triangle_components]
  exact Category.id_comp (adj.reflectedHomologyIso (K.sc i)).hom

/-- Sheafification inverts the original presheaf-homology unit. -/
theorem sheafification_map_homologyPresheafUnit_isIso :
    IsIso ((PresheafOfModules.sheafification.{m} (𝟙 R.obj)).map (homologyPresheafUnit R K i)) := by
  have hu := sheafification_map_homologyPresheafUnit_counit R K i
  let ε := (PresheafOfModules.sheafificationAdjunction.{m} (𝟙 R.obj)).counit.app
    (K.homology i)
  have he : (PresheafOfModules.sheafification.{m} (𝟙 R.obj)).map
        (homologyPresheafUnit R K i) = (sheafificationHomologyIso R K i).hom ≫ inv ε := by
    apply (cancel_mono ε).mp
    rw [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
    exact hu
  rw [he]
  infer_instance

/-- The original presheaf-homology unit is natural for actual chain maps. -/
@[reassoc]
theorem homologyPresheafUnit_naturality
    {K L : HomologicalComplex (SheafOfModules.{m} R) d} (φ : K ⟶ L) (i : ι) :
    HomologicalComplex.homologyMap
        (((SheafOfModules.forget.{m} R).mapHomologicalComplex d).map φ) i ≫
        homologyPresheafUnit R L i =
      homologyPresheafUnit R K i ≫
        (SheafOfModules.forget.{m} R).map (HomologicalComplex.homologyMap φ i) := by
  dsimp only [homologyPresheafUnit]
  let adj := sheafificationForgetAdjunction R
  have h := adj.homologyReflectionUnit_naturality
      ((HomologicalComplex.shortComplexFunctor (SheafOfModules.{m} R) d i).map φ)
  exact h

end SheafOfModules
