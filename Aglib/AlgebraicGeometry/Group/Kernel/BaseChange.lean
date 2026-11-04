/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Group.Kernel.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal

/-! # Base change of the actual group-scheme kernel

The native pullback functor on group objects carries the actual kernel
pullback to the kernel pullback of the base-changed morphism.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.Group.Kernel

attribute [local instance] Over.cartesianMonoidalCategory

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {S T : Scheme.{u}} (b : T ⟶ S) {G E : Grp (Over S)} (q : G ⟶ E)

private theorem pullbackMapGrp_preservesFiniteLimits :
    PreservesFiniteLimits (Over.pullback b).mapGrp where
  preservesFiniteLimits J _ _ := by
    let F := (Over.pullback b).mapGrp
    have : PreservesLimitsOfShape J (F ⋙ Grp.forget (Over T)) :=
      inferInstanceAs (PreservesLimitsOfShape J (Grp.forget (Over S) ⋙ Over.pullback b))
    exact preservesLimitsOfShape_of_reflects_of_preserves F (Grp.forget (Over T))

private theorem baseChange_square :
    IsPullback ((Over.pullback b).mapGrp.map (inclusion q))
      ((Grp.isZero_trivial (Over T)).isTerminal.from ((Over.pullback b).mapGrp.obj (group q)))
      ((Over.pullback b).mapGrp.map q) (identityHom (E := (Over.pullback b).mapGrp.obj E)) := by
  let F := (Over.pullback b).mapGrp
  have : PreservesFiniteLimits F := pullbackMapGrp_preservesFiniteLimits b
  let e : F.obj (Grp.trivial (Over S)) ≅ Grp.trivial (Over T) :=
    ((Grp.isZero_trivial (Over S)).isTerminal.isTerminalObj F _).uniqueUpToIso
      (Grp.isZero_trivial (Over T)).isTerminal
  have he : F.map (identityHom (E := E)) ≫ 𝟙 (F.obj E) =
      e.hom ≫ identityHom (E := F.obj E) := by
    rw [Category.comp_id]
    calc
      _ = e.hom ≫ (e.inv ≫ F.map (identityHom (E := E))) := by
        rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
      _ = _ := congrArg (fun f : Grp.trivial (Over T) ⟶ F.obj E => e.hom ≫ f)
        (Subsingleton.elim _ _)
  have hBottom : IsPullback (F.map (identityHom (E := E))) e.hom
      (𝟙 (F.obj E)) (identityHom (E := F.obj E)) :=
    IsPullback.of_vert_isIso ⟨he⟩
  let s : group q ⟶ Grp.trivial (Over S) := pullback.snd q (identityHom (E := E))
  let t := (Grp.isZero_trivial (Over T)).isTerminal
  have h : IsPullback (F.map (inclusion q)) (F.map s) (F.map q)
      (F.map (identityHom (E := E))) :=
    (IsPullback.of_hasPullback q (identityHom (E := E))).map F
  have hs : F.map s ≫ e.hom = t.from (F.obj (group q)) := t.hom_ext _ _
  change IsPullback (F.map (inclusion q)) (t.from (F.obj (group q))) (F.map q)
    (identityHom (E := F.obj E))
  rw [← hs]
  simpa only [Category.comp_id] using h.paste_vert hBottom

/-- The native comparison between the base change of the actual kernel and
the actual kernel of the base-changed morphism. -/
@[no_expose]
def baseChangeIso :
    (Over.pullback b).mapGrp.obj (group q) ≅ group ((Over.pullback b).mapGrp.map q) :=
  (baseChange_square b q).isoPullback

/-- The comparison commutes with the actual kernel inclusion. -/
@[reassoc (attr := simp)]
theorem baseChangeIso_hom_inclusion :
    (baseChangeIso b q).hom ≫ inclusion ((Over.pullback b).mapGrp.map q) =
      (Over.pullback b).mapGrp.map (inclusion q) :=
  (baseChange_square b q).isoPullback_hom_fst

end AlgebraicGeometry.Scheme.Group.Kernel
