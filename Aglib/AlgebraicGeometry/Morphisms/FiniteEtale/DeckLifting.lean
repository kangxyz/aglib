/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.NonemptyRestriction

/-!
# Actual deck maps under comparison inverse and restriction

The inverse and all automorphism maps are the existing functorial `mapAut`
maps on the same chosen inverse cover. Restriction retains the original
scheme, the morphism to the displayed base and its actual covering map.
Connectedness and nonemptiness concern these literal objects. The comparison
equivalence is a pointwise input; no proper-Henselian producer is asserted.

Source: unmarked declarations of
`R5Lab.AlgebraicGeometry.Curves.LocalModels.CyclicCovers.DeckLifting:55–173`,
R5 `f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`20f8004cc161e2aac5d76d43e3b98501ed21fd77c13302b8c87108bfbe381252`.
The field-specific functor in that source is the existing composition
`FiniteEtale.forget _ ⋙ Over.map _`, used literally here over arbitrary schemes.
Marked-cycle and elliptic-group application endpoints remain downstream.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.FiniteEtale.Lifting

universe u
variable {S T U B : Scheme.{u}} (i : S ⟶ T) [(baseChange i).IsEquivalence]

/-- Exact order is retained on the same inverse object of the supplied
comparison equivalence. -/
theorem inverseAut_orderOf (C₀ : FiniteEtale S) (g : Aut C₀) :
    orderOf ((baseChange i).inv.mapAut C₀ g) = orderOf g :=
  orderOf_injective _ (baseChange i).inv.mapIso_injective g

/-- Under the actual counit comparison, the lifted map reduces to the
original automorphism. -/
@[reassoc] theorem inverseAut_compare (C₀ : FiniteEtale S) (g : Aut C₀) :
    (baseChange i).map ((baseChange i).inv.mapAut C₀ g).hom ≫
        ((baseChange i).asEquivalence.counitIso.app C₀).hom =
      ((baseChange i).asEquivalence.counitIso.app C₀).hom ≫ g.hom :=
  (baseChange i).asEquivalence.counitIso.hom.naturality g.hom

variable (j : U ⟶ T) (b : U ⟶ B)

/-- Lift by the supplied comparison inverse, restrict by the actual base
map, and retain the original morphism to the displayed base. -/
def restrictedAut (C₀ : FiniteEtale S) : Aut C₀ →*
    Aut ((forget U ⋙ Over.map b).obj
      ((baseChange j).obj ((baseChange i).inv.obj C₀))) :=
  ((forget U ⋙ Over.map b).mapAut _).comp
    (((baseChange j).mapAut _).comp ((baseChange i).inv.mapAut C₀))

/-- Every transported automorphism is over the unchanged covering map in
the original over-category. -/
@[reassoc] theorem restrictedAut_over (C₀ : FiniteEtale S) (g : Aut C₀) :
    (restrictedAut i j b C₀ g).hom ≫
        (Over.homMk ((baseChange j).obj ((baseChange i).inv.obj C₀)).obj.hom rfl :
          (forget U ⋙ Over.map b).obj ((baseChange j).obj ((baseChange i).inv.obj C₀)) ⟶
            Over.mk b) =
      Over.homMk ((baseChange j).obj ((baseChange i).inv.obj C₀)).obj.hom rfl := by
  apply Over.OverMorphism.ext
  exact Over.w ((baseChange j).mapIso ((baseChange i).inv.mapIso g)).hom.hom

/-- Restriction on these exact deck maps is injective from connectedness
and nonemptiness of the actual lifted source and its actual pullback. -/
theorem restrictedAut_injective (C₀ : FiniteEtale S)
    [ConnectedSpace ((baseChange i).inv.obj C₀).obj.left]
    [Nonempty ((baseChange j).obj ((baseChange i).inv.obj C₀)).obj.left] :
    Function.Injective (restrictedAut i j b C₀) := by
  let : (forget U ⋙ Over.map b).Faithful :=
    Functor.Faithful.of_comp_eq (G := Over.forget B) (H := forgetToScheme U) rfl
  exact (forget U ⋙ Over.map b).mapIso_injective.comp
    ((baseChange_mapAut_injective_of_connected j _).comp
      (baseChange i).inv.mapIso_injective)

/-- The original deck automorphism's exact order survives both actual
comparison lifting and restriction. -/
theorem restrictedAut_orderOf (C₀ : FiniteEtale S)
    [ConnectedSpace ((baseChange i).inv.obj C₀).obj.left]
    [Nonempty ((baseChange j).obj ((baseChange i).inv.obj C₀)).obj.left]
    (g : Aut C₀) : orderOf (restrictedAut i j b C₀ g) = orderOf g :=
  orderOf_injective _ (restrictedAut_injective i j b C₀) g

end AlgebraicGeometry.Scheme.FiniteEtale.Lifting
