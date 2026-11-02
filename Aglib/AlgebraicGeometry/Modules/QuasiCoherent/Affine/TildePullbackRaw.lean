/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.TildePullback

/-! # Original tilde pullback homs at their raw scalar actions

These views retain the original native iso hom. Whole and component laws
transport the existing proofs through the same identity equations.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Functor

namespace AlgebraicGeometry.Scheme.Modules

variable {R S T : CommRingCat.{u}}

/-- The original tilde pullback hom with the literal raw scalar action as target. -/
def tildePullbackHom_ringHom (f : R →+* S) :
    tilde.functor R ⋙ pullback (Spec.map (CommRingCat.ofHom f : R ⟶ S)) ⟶
      ModuleCat.extendScalars f ⋙ tilde.functor S :=
  (tildePullbackIso (R := R) (S := S) (CommRingCat.ofHom f)).hom

/-- The raw action view is the same native iso hom, not a new comparison. -/
theorem tildePullbackHom_ringHom_eq (f : R →+* S) :
    tildePullbackHom_ringHom (R := R) (S := S) f =
      (tildePullbackIso (R := R) (S := S) (CommRingCat.ofHom f)).hom := by
  rfl

/-- The complete original natural law with the same raw-view data. -/
theorem tildePullbackHom_ringHom_comp (f : R →+* S) (g : S →+* T)
    (h : Spec.map (CommRingCat.ofHom (g.comp f) : R ⟶ T) =
      Spec.map (CommRingCat.ofHom g : S ⟶ T) ≫ Spec.map (CommRingCat.ofHom f : R ⟶ S)) :
    let φ : R ⟶ S := CommRingCat.ofHom f
    let ψ : S ⟶ T := CommRingCat.ofHom g
    whiskerLeft (tilde.functor R) ((pullbackCongr h).hom ≫
        (pullbackComp (Spec.map ψ) (Spec.map φ)).inv) ≫
      (associator _ _ _).inv ≫
        whiskerRight (tildePullbackHom_ringHom (R := R) (S := S) f) (pullback (Spec.map ψ)) ≫
      (associator _ _ _).hom ≫
        whiskerLeft (ModuleCat.extendScalars f) (tildePullbackHom_ringHom (R := S) (S := T) g) =
    (tildePullbackHom_ringHom (R := R) (S := T) (g.comp f)) ≫
      whiskerRight (ModuleCat.extendScalarsComp f g).hom (tilde.functor T) ≫
      (associator _ _ _).hom := by
  simpa only [tildePullbackHom_ringHom_eq, CommRingCat.hom_ofHom] using
    (tildePullbackIso_ringHom_comp_hom_of_triangle (R := R) (S := S) (T := T) f g h)

/-- The original component law transported through the same three raw-view identities. -/
theorem tildePullbackHom_ringHom_comp_app (f : R →+* S) (g : S →+* T)
    (h : Spec.map (CommRingCat.ofHom (g.comp f) : R ⟶ T) =
      Spec.map (CommRingCat.ofHom g : S ⟶ T) ≫ Spec.map (CommRingCat.ofHom f : R ⟶ S))
    (N : ModuleCat.{u} R) :
    let φ : R ⟶ S := CommRingCat.ofHom f
    let ψ : S ⟶ T := CommRingCat.ofHom g
    let χ : R ⟶ T := CommRingCat.ofHom (g.comp f)
    @Eq
      (@Quiver.Hom (Spec T).Modules inferInstance
        ((pullback (Spec.map χ)).obj ((tilde.functor R).obj N))
        ((tilde.functor T).obj
          ((ModuleCat.extendScalars g).obj ((ModuleCat.extendScalars f).obj N))))
      ((pullbackCongr (X := Spec T) (Y := Spec R)
          (f := Spec.map χ) (g := Spec.map ψ ≫ Spec.map φ) h).hom.app
          ((tilde.functor R).obj N) ≫
        (pullbackComp (Spec.map ψ) (Spec.map φ)).inv.app ((tilde.functor R).obj N) ≫
        (pullback (Spec.map ψ)).map ((tildePullbackHom_ringHom (R := R) (S := S) f).app N) ≫
        (tildePullbackHom_ringHom (R := S) (S := T) g).app
          ((ModuleCat.extendScalars f).obj N))
      ((tildePullbackHom_ringHom (R := R) (S := T) (g.comp f)).app N ≫
        (tilde.functor T).map ((ModuleCat.extendScalarsComp f g).hom.app N)) := by
  simpa only [tildePullbackHom_ringHom_eq] using
    (tildePullbackIso_ringHom_comp_hom_app (R := R) (S := S) (T := T) f g h N)

end AlgebraicGeometry.Scheme.Modules
