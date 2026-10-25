/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Sites.OverRepresentability.BaseCover.FullSubcategory

/-!
# Consumer checks for representability local on the base, on full subcategories

The generic statement for a property `P` of test schemes over `S` and properties `Q i` over the
members `U i` of an open cover of `S` (Kleiman, *The Picard scheme*, arXiv:math/0504020v1, proof
of Thm 4.8, p. 28), instantiated at `P = ⊤`, `Q i = ⊤` and at locally Noetherian test schemes; the
glued representing object, its charts over `S` and a source-local property of its structure
morphism; axiom guards.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.LocalRepresentability

universe v u

namespace AglibTest.BaseCoverFullSubcategory

variable {S : Scheme.{u}} {ι : Type u} {U : ι → Scheme.{u}} (j : ∀ i, U i ⟶ S)
  [∀ i, IsOpenImmersion (j i)] (hcov : ∀ x : S, ∃ i, x ∈ Set.range (j i))

/-- The generic statement on the full subcategory `⊤` of `Over S`, with `Q i = ⊤`. -/
example {F : (⊤ : ObjectProperty (Over S)).FullSubcategoryᵒᵖ ⥤ Type v} (hF : IsZariskiSheaf F)
    (hrep : ∀ i, ((fullSubcategoryOverMap (P := ⊤) (Q := ⊤) (j i) fun _ _ => trivial).op ⋙
      F).IsRepresentable) :
    F.IsRepresentable :=
  isRepresentable_of_openCover_base_of_isOpenLocal hF j hcov (Q := fun _ => ⊤)
    (fun _ _ _ => trivial) (fun _ _ _ _ => trivial) hrep

/-- The locally Noetherian statement. -/
example {F : (LocallyNoetherianOver S)ᵒᵖ ⥤ Type v} (hF : IsZariskiSheaf F)
    (hrep : ∀ i, ((LocallyNoetherianOver.map (j i)).op ⋙ F).IsRepresentable) :
    F.IsRepresentable :=
  isRepresentable_of_openCover_base_of_isLocallyNoetherian hF j hcov hrep

variable {F : (LocallyNoetherianOver S)ᵒᵖ ⥤ Type v} (Y : ∀ i, LocallyNoetherianOver (U i))
  (e : ∀ i, ((LocallyNoetherianOver.map (j i)).op ⋙ F).RepresentableBy (Y i))

/-- The glued object of the locally Noetherian base cover represents `F`. -/
example (hF : IsZariskiSheaf F) :
    F.RepresentableBy (SubfunctorCover.locallyNoetherianBaseCover j hcov Y e).glued :=
  (SubfunctorCover.locallyNoetherianBaseCover j hcov Y e).representableByGlued hF

/-- The charts of the glued object are the representing objects `Y i`, viewed over `S` through
`j i`, and they are open immersions. -/
example (i : ι) :
    ((SubfunctorCover.locallyNoetherianBaseCover j hcov Y e).X i).obj =
      (Over.map (j i)).obj (Y i).obj :=
  rfl

example (i : ι) :
    IsOpenImmersion ((SubfunctorCover.locallyNoetherianBaseCover j hcov Y e).ιp i).hom.left :=
  inferInstance

/-- The subfunctor of the chart `i` is the set of sections over test schemes landing in the image
of `j i`. -/
example (i : ι) {T : LocallyNoetherianOver S} (ξ : F.obj (op T)) :
    ξ ∈ ((SubfunctorCover.locallyNoetherianBaseCover j hcov Y e).sub i).obj (op T) ↔
      T.obj.hom ⁻¹ᵁ (j i).opensRange = ⊤ :=
  mem_fullSubcategoryBaseSubfunctor_iff (j i) F ξ

/-- A property of morphisms local at the source holds for the glued object when it holds for the
structure morphisms of the `Y i` followed by the open immersions `j i`. -/
example (Pr : MorphismProperty Scheme.{u}) [IsZariskiLocalAtSource Pr]
    (h : ∀ i, Pr ((Y i).obj.hom ≫ j i)) :
    Pr (SubfunctorCover.locallyNoetherianBaseCover j hcov Y e).glued.obj.hom :=
  (SubfunctorCover.locallyNoetherianBaseCover j hcov Y e).prop_glued_hom Pr h

end AglibTest.BaseCoverFullSubcategory

/-- info: 'AlgebraicGeometry.Scheme.LocalRepresentability.fullSubcategoryBaseSubfunctor' depends
on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.LocalRepresentability.fullSubcategoryBaseSubfunctor

/-- info: 'AlgebraicGeometry.Scheme.LocalRepresentability.mem_fullSubcategoryBaseSubfunctor_iff'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.LocalRepresentability.mem_fullSubcategoryBaseSubfunctor_iff

/-- info:
'AlgebraicGeometry.Scheme.LocalRepresentability.isOpenSubfunctor_fullSubcategoryBaseSubfunctor'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  AlgebraicGeometry.Scheme.LocalRepresentability.isOpenSubfunctor_fullSubcategoryBaseSubfunctor

/-- info: 'AlgebraicGeometry.Scheme.LocalRepresentability.fullSubcategoryOverMap' depends on
axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.LocalRepresentability.fullSubcategoryOverMap

/-- info: 'AlgebraicGeometry.Scheme.LocalRepresentability.fullSubcategoryRestrictBase' depends on
axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.LocalRepresentability.fullSubcategoryRestrictBase

/-- info: 'AlgebraicGeometry.Scheme.LocalRepresentability.fullSubcategoryRestrictBaseIso' depends
on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.LocalRepresentability.fullSubcategoryRestrictBaseIso

/-- info: 'AlgebraicGeometry.Scheme.LocalRepresentability.fullSubcategoryRestrictHom' depends on
axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.LocalRepresentability.fullSubcategoryRestrictHom

/-- info: 'AlgebraicGeometry.Scheme.LocalRepresentability.fullSubcategoryBaseHomEquivFun' depends
on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.LocalRepresentability.fullSubcategoryBaseHomEquivFun

/-- info: 'AlgebraicGeometry.Scheme.LocalRepresentability.fullSubcategoryBaseHomEquivInv' depends
on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.LocalRepresentability.fullSubcategoryBaseHomEquivInv

/-- info: 'AlgebraicGeometry.Scheme.LocalRepresentability.fullSubcategoryBaseHomEquivInv_fun'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.LocalRepresentability.fullSubcategoryBaseHomEquivInv_fun

/-- info: 'AlgebraicGeometry.Scheme.LocalRepresentability.fullSubcategoryBaseHomEquivFun_inv'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.LocalRepresentability.fullSubcategoryBaseHomEquivFun_inv

/-- info: 'AlgebraicGeometry.Scheme.LocalRepresentability.fullSubcategoryBaseHomEquivFun_comp'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.LocalRepresentability.fullSubcategoryBaseHomEquivFun_comp

/-- info:
'AlgebraicGeometry.Scheme.LocalRepresentability.representableByFullSubcategoryBaseSubfunctor'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  AlgebraicGeometry.Scheme.LocalRepresentability.representableByFullSubcategoryBaseSubfunctor

/-- info: 'AlgebraicGeometry.Scheme.LocalRepresentability.SubfunctorCover.baseCover' depends on
axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.LocalRepresentability.SubfunctorCover.baseCover

/-- info:
'AlgebraicGeometry.Scheme.LocalRepresentability.isRepresentable_of_openCover_base_of_isOpenLocal'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  AlgebraicGeometry.Scheme.LocalRepresentability.isRepresentable_of_openCover_base_of_isOpenLocal

/-- info: 'AlgebraicGeometry.Scheme.LocalRepresentability.SubfunctorCover.prop_glued_hom' depends
on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.LocalRepresentability.SubfunctorCover.prop_glued_hom

/-- info:
'AlgebraicGeometry.Scheme.LocalRepresentability.SubfunctorCover.locallyNoetherianBaseCover'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  AlgebraicGeometry.Scheme.LocalRepresentability.SubfunctorCover.locallyNoetherianBaseCover

/-- info: 'AlgebraicGeometry.Scheme.LocalRepresentability.isRepresentable_of_openCover_base_of_isLocallyNoetherian'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  AlgebraicGeometry.Scheme.LocalRepresentability.isRepresentable_of_openCover_base_of_isLocallyNoetherian
