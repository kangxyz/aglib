/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.ProperHenselian.Approximation
public import Aglib.AlgebraicGeometry.Approximation.ProperSystem

/-!
# Applying an actual proper approximation system to henselian lifting

The original over-category comparison transports the conditional fixed-base
limit result. Existence of the proper approximation system is still explicit.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.FiniteEtale

universe u

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- An actual proper FP approximation system supplies essential surjectivity
for the original closed-fibre functor. -/
theorem properHenselian_baseChange_essSurj_of_properFPSystem
    {R : Type u} [CommRing R] [HenselianLocalRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of R))
    (M : Approximation.ProperFinitePresentationSystem f) :
    (baseChange (pullback.fst f (LocalRing.residueSpecMap R))).EssSurj := by
  let D := M.diagram ⋙ Over.forget (Spec (.of R))
  let a : D ⟶ (Functor.const M.index).obj (Spec (.of R)) :=
    { app := fun s ↦ (M.diagram.obj s).hom
      naturality := fun s t g ↦ by
        change (M.diagram.map g).left ≫ (M.diagram.obj t).hom =
          (M.diagram.obj s).hom ≫ 𝟙 _
        rw [(M.diagram.map g).w, Category.comp_id] }
  let c := (Over.forget (Spec (.of R))).mapCone M.cone
  have {s t : M.index} (g : s ⟶ t) : IsAffineHom (D.map g) :=
    inferInstanceAs (IsAffineHom (M.diagram.map g).left)
  have (s : M.index) : IsProper (a.app s) := M.proper s
  have (s : M.index) : LocallyOfFinitePresentation (a.app s) := M.finitePresentation s
  have hp (s : M.index) : c.π.app s ≫ a.app s = M.cone.pt.hom :=
    (M.cone.π.app s).w
  let : (baseChange (pullback.fst M.cone.pt.hom
      (LocalRing.residueSpecMap R))).EssSurj :=
    properHenselian_baseChange_essSurj_of_properFPLimit D a c M.isLimit M.cone.pt.hom hp
  exact baseChange_essSurj_of_overIso (LocalRing.residueSpecMap R)
    f M.cone.pt.hom (eqToIso M.point)

end AlgebraicGeometry.Scheme.FiniteEtale
