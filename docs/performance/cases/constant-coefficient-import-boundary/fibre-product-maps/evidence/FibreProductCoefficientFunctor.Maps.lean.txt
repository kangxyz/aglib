/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.Grp.ResizeNaturality
public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.FibreProductPresheaf
public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.FibreProductRestrictionCoefficients

/-! # Original coefficient maps on fibre-product cohomology diagrams -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite

universe u w s e

namespace AlgebraicGeometry.Scheme.EtaleCohomology

attribute [local instance] hasSheafifyLarge

variable {X S : Scheme.{u}} (f : X ⟶ S)
  [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]
  [∀ U : S.Etale, HasExt.{s} (Sheaf ((Scheme.smallEtaleTopology X).over
    ((siteBaseChange f).obj U)) AddCommGrpCat.{u + 1})]
  [∀ U : S.Etale, HasExt.{e} (AbelianSheaf.{u, u + 1} (pullback U.hom f))]
  (q : ℕ)

/-- The original fibre-product diagrams, functorial in the unchanged abelian coefficient. -/
def Stalk.originalFibreProductCohomologyFunctor :
    AbelianSheaf.{u, u + 1} X ⥤ S.Etaleᵒᵖ ⥤ AddCommGrpCat.{e} where
  obj F := Stalk.originalFibreProductCohomologyPresheaf f F q
  map g := {
    app := fun U => AddCommGrpCat.ofHom
      (Sheaf.H.map ((inverseImage (pullback.snd U.unop.hom f)).map g) q)
    naturality := by
      intro U V a
      ext x
      exact (fibreProductCohomologyRestriction_coefficientMap f a.unop g q x).symm }
  map_id F := by
    ext U x
    change Sheaf.H.map ((inverseImage (pullback.snd U.unop.hom f)).map (𝟙 F)) q x = x
    rw [CategoryTheory.Functor.map_id, Sheaf.H.map_id_apply]
  map_comp g h := by
    ext U x
    change Sheaf.H.map ((inverseImage (pullback.snd U.unop.hom f)).map (g ≫ h)) q x =
      Sheaf.H.map ((inverseImage (pullback.snd U.unop.hom f)).map h) q
        (Sheaf.H.map ((inverseImage (pullback.snd U.unop.hom f)).map g) q x)
    rw [CategoryTheory.Functor.map_comp, Sheaf.H.map_comp_apply]

/-- The original coefficient maps are additive before any resizing. -/
instance Stalk.originalFibreProductCohomologyFunctor_additive :
    (Stalk.originalFibreProductCohomologyFunctor.{u, w, s, e} f q).Additive where
  map_add := by
    intro F G g h
    ext U x
    change Sheaf.H.map ((inverseImage (pullback.snd U.unop.hom f)).map (g + h)) q x =
      Sheaf.H.map ((inverseImage (pullback.snd U.unop.hom f)).map g) q x +
        Sheaf.H.map ((inverseImage (pullback.snd U.unop.hom f)).map h) q x
    rw [CategoryTheory.Functor.map_add, Sheaf.H.map_add_apply]

/-- Reuse the original smallness family over both coefficient and diagram indices. -/
local instance originalFibreProductCohomologyFunctor_small :
    ∀ (F : AbelianSheaf.{u, u + 1} X) (U : S.Etaleᵒᵖ),
      Small.{u + 1}
        (((Stalk.originalFibreProductCohomologyFunctor.{u, w, s, e} f q).obj F).obj U) :=
  fun F U => inferInstanceAs (Small.{u + 1}
    ((Stalk.originalFibreProductCohomologyPresheaf.{u, w, s, e} f F q).obj U))

/-- The original coefficient map on the unchanged small fibre-product presheaves. -/
def smallFibreProductCohomologyCoefficientMap
    {F G : AbelianSheaf.{u, u + 1} X} (g : F ⟶ G) :
    smallFibreProductCohomologyPresheaf f F q ⟶
      smallFibreProductCohomologyPresheaf f G q :=
  resizeAdditiveDiagramMap.{u + 1}
    ((Stalk.originalFibreProductCohomologyFunctor.{u, w, s, e} f q).map g)

/-- The coefficient map on an original class is precisely the original cohomology map. -/
theorem smallFibreProductCohomologyCoefficientMap_app_shrink
    {F G : AbelianSheaf.{u, u + 1} X} (g : F ⟶ G) (U : S.Etale)
    (x : Sheaf.H.{e} ((inverseImage (pullback.snd U.hom f)).obj F) q) :
    (smallFibreProductCohomologyCoefficientMap f q g).app (op U)
        (Shrink.addEquiv.{u + 1, e}.symm x) =
      Shrink.addEquiv.{u + 1, e}.symm
        (Sheaf.H.map ((inverseImage (pullback.snd U.hom f)).map g) q x) :=
  resizeAdditiveDiagramMapOfHom_app_shrink.{u + 1, e, e}
    (P := Stalk.originalFibreProductCohomologyPresheaf.{u, w, s, e} f F q)
    (Q := Stalk.originalFibreProductCohomologyPresheaf.{u, w, s, e} f G q)
    (fun V => Sheaf.H.map ((inverseImage (pullback.snd V.unop.hom f)).map g) q)
    (fun {V W} (a : V ⟶ W) y =>
      (fibreProductCohomologyRestriction_coefficientMap f a.unop g q y).symm)
    (op U) x

/-- The existing small presheaves, with their actual original coefficient maps. -/
def smallFibreProductCohomologyFunctor :
    AbelianSheaf.{u, u + 1} X ⥤ S.Etaleᵒᵖ ⥤ AddCommGrpCat.{u + 1} :=
  resizeAdditiveDiagramFunctor.{u + 1}
    (Stalk.originalFibreProductCohomologyFunctor.{u, w, s, e} f q)

/-- The original coefficient functor is additive on the same resized groups. -/
instance smallFibreProductCohomologyFunctor_additive :
    (smallFibreProductCohomologyFunctor f q).Additive :=
  inferInstanceAs ((resizeAdditiveDiagramFunctor.{u + 1}
    (Stalk.originalFibreProductCohomologyFunctor.{u, w, s, e} f q)).Additive)

end AlgebraicGeometry.Scheme.EtaleCohomology
