/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Modules.Sections
public import Aglib.AlgebraicGeometry.Cohomology.Modules.Scalars
public import Mathlib.Algebra.Homology.Additive

/-!
# Actual structural-ring sections of a module pushforward

The original pushforward has the original coefficient sections on the
inverse-image open. The identity on those sections is linear for the
specified structural ring. Its presheaf, coefficient and complex comparisons
retain the actual pushforward and the native inverse-image-open functor.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open AlgebraicGeometry TopologicalSpace Opposite

namespace AlgebraicGeometry.Scheme.Cohomology

universe u w

variable {R : Type u} [CommRing R] {X Y : Scheme.{u}}
  (f : X ⟶ Y) (α : R →+* Γ(Y, ⊤))

/-- Actual pushforward sections are the original sections on inverse-image opens. -/
def modulePushforwardSectionsPresheafIso (M : X.Modules) :
    moduleSectionsPresheaf Y α ((Scheme.Modules.pushforward f).obj M) ≅
      (Opens.map f.base).op ⋙ moduleSectionsPresheaf X (f.appTop.hom.comp α) M := by
  refine NatIso.ofComponents
    (fun U => ModuleCat.isoMk (AddEquiv.refl _).toAddCommGrpIso ?_) ?_
  · intro r
    ext x
    change M.val.obj (op (f ⁻¹ᵁ U.unop)) at x
    symm
    change f.app U.unop (globalRestriction Y U.unop (α r)) • x =
      globalRestriction X (f ⁻¹ᵁ U.unop) (f.appTop (α r)) • x
    have h := congrArg
      (fun q : Γ(Y, ⊤) ⟶ Γ(X, f ⁻¹ᵁ U.unop) => q.hom (α r))
      (f.naturality (homOfLE (show U.unop ≤ ⊤ from le_top)).op)
    change f.app U.unop (globalRestriction Y U.unop (α r)) =
      globalRestriction X (f ⁻¹ᵁ U.unop) (f.appTop (α r)) at h
    rw [h]
  · intro U V i
    ext x
    rfl

theorem modulePushforwardSectionsPresheafIso_hom_app_apply (M : X.Modules)
    (U : Y.Opensᵒᵖ)
    (x : (moduleSectionsPresheaf Y α ((Scheme.Modules.pushforward f).obj M)).obj U) :
    (modulePushforwardSectionsPresheafIso f α M).hom.app U x = x := rfl

theorem modulePushforwardSectionsPresheafIso_inv_app_apply (M : X.Modules)
    (U : Y.Opensᵒᵖ)
    (x : (moduleSectionsPresheaf X (f.appTop.hom.comp α) M).obj
      ((Opens.map f.base).op.obj U)) :
    (modulePushforwardSectionsPresheafIso f α M).inv.app U x = x := rfl

/-- Original pushforward-section comparison, natural in the actual module coefficient. -/
def modulePushforwardSectionsPresheafFunctorIso :
    Scheme.Modules.pushforward f ⋙ moduleSectionsPresheafFunctor Y α ≅
      moduleSectionsPresheafFunctor X (f.appTop.hom.comp α) ⋙
        (Functor.whiskeringLeft Y.Opensᵒᵖ X.Opensᵒᵖ (ModuleCat.{u} R)).obj
          (Opens.map f.base).op :=
  NatIso.ofComponents (modulePushforwardSectionsPresheafIso f α) (by
    intro M N φ
    ext U x
    rfl)

/-- The native termwise comparison for an actual module complex. -/
def modulePushforwardSectionsPresheafComplexIso {ι : Type w} (d : ComplexShape ι)
    (K : HomologicalComplex X.Modules d) :
    ((moduleSectionsPresheafFunctor Y α).mapHomologicalComplex d).obj
        (((Scheme.Modules.pushforward f).mapHomologicalComplex d).obj K) ≅
      (((Functor.whiskeringLeft Y.Opensᵒᵖ X.Opensᵒᵖ (ModuleCat.{u} R)).obj
          (Opens.map f.base).op).mapHomologicalComplex d).obj
        (((moduleSectionsPresheafFunctor X (f.appTop.hom.comp α)).mapHomologicalComplex d).obj
          K) :=
  (Functor.mapHomologicalComplexCompIso
    (modulePushforwardSectionsPresheafFunctorIso f α) d).app K

theorem modulePushforwardSectionsPresheafComplexIso_hom_f_app_apply
    {ι : Type w} (d : ComplexShape ι) (K : HomologicalComplex X.Modules d)
    (n : ι) (U : Y.Opensᵒᵖ)
    (x : ((((moduleSectionsPresheafFunctor Y α).mapHomologicalComplex d).obj
      (((Scheme.Modules.pushforward f).mapHomologicalComplex d).obj K)).X n).obj U) :
    ((modulePushforwardSectionsPresheafComplexIso f α d K).hom.f n).app U x = x := rfl

end AlgebraicGeometry.Scheme.Cohomology
