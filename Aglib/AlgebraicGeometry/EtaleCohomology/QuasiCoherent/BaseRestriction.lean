/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.QuasiCoherent.SectionsNaturality

/-! # Native restriction of quasi-coherent section coefficients -/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u v w z

open CategoryTheory Opposite Bicategory
open AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.EtaleCohomology.QuasiCoherent

/-- Changing the source by an actual isomorphism preserves the native Hom presheaf. -/
def presheafHomSourceIso {C : Type u} [Category.{v} C]
    (P : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{w, z}) {X : C}
    {M M' : P.obj (.mk (op X))} (e : M ≅ M') (N : P.obj (.mk (op X))) :
    P.presheafHom M N ≅ P.presheafHom M' N :=
  NatIso.ofComponents (fun T =>
    (Iso.homCongr ((P.map T.unop.hom.op.toLoc).toFunctor.mapIso e) (Iso.refl _)).toIso)
    (by
      intro T U f
      ext h
      dsimp [Pseudofunctor.presheafHom, Pseudofunctor.LocallyDiscreteOpToCat.pullHom]
      simp only [Category.comp_id, Functor.map_comp, Category.assoc]
      rw [P.mapComp'_hom_naturality_assoc])

/-- Restriction of the native Hom coefficient, including the actual pulled-back unit. -/
def homBaseRestrictionIso {X Y : Scheme.{u}} (f : Y ⟶ X)
    (F : X.Modules) [F.IsQuasicoherent] :
    (Over.map f).op ⋙ homPresheaf X F ≅ homPresheaf Y ((pullback f).obj F) :=
  quasicoherentPseudofunctor.overMapCompPresheafHomIso
      (unitObject X) (moduleObject X F) f ≪≫
    presheafHomSourceIso quasicoherentPseudofunctor
      (ObjectProperty.isoMk _ (pullbackUnitIso f)) (moduleObject Y ((pullback f).obj F))

/-- The actual pullback-section coefficient restricts to the actual pullback module. -/
def sectionsBaseRestrictionIso {X Y : Scheme.{u}} (f : Y ⟶ X)
    (F : X.Modules) [F.IsQuasicoherent] :
    (Over.map f).op ⋙ sectionsPresheaf X F ≅ sectionsPresheaf Y ((pullback f).obj F) :=
  Functor.isoWhiskerLeft (Over.map f).op (homSectionsIso X F).symm ≪≫
    homBaseRestrictionIso f F ≪≫ homSectionsIso Y ((pullback f).obj F)

end AlgebraicGeometry.Scheme.EtaleCohomology.QuasiCoherent
