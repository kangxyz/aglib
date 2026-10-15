/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.Pushforward
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
/-!
# Actual sheaf pullback, open restriction, and affine extension of scalars

The comparison is obtained from the actual pushforward/global-sections
square by uniqueness of left adjoints. In particular it concerns the genuine
scheme-module pullback, including its adjunction unit. The generic open
restriction square is the ordered composition of the actual pullback comparisons.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct

namespace AlgebraicGeometry.Scheme.Modules

/-- Actual geometric pullback commutes with restriction across a commuting
square with open horizontal maps. -/
def pullbackOpenSquare {W X V Y : Scheme.{u}}
    (p : W ⟶ X) (q : W ⟶ V) (f : X ⟶ Y) (a : V ⟶ Y)
    [IsOpenImmersion p] [IsOpenImmersion a] (h : p ≫ f = q ≫ a) :
    Scheme.Modules.pullback f ⋙ Scheme.Modules.restrictFunctor p ≅
      Scheme.Modules.restrictFunctor a ⋙ Scheme.Modules.pullback q :=
  Functor.isoWhiskerLeft _ (Scheme.Modules.restrictFunctorIsoPullback p) ≪≫
    Scheme.Modules.pullbackComp p f ≪≫ Scheme.Modules.pullbackCongr h ≪≫
    (Scheme.Modules.pullbackComp q a).symm ≪≫
    Functor.isoWhiskerRight (Scheme.Modules.restrictFunctorIsoPullback a).symm _

variable {R S : CommRingCat.{u}} (φ : R ⟶ S)

/-- Actual affine sheaf pullback of an associated sheaf is associated to
ordinary extension of scalars. -/
def tildePullbackIso :
    tilde.functor R ⋙ Scheme.Modules.pullback (Spec.map φ) ≅
      ModuleCat.extendScalars φ.hom ⋙ tilde.functor S :=
  (((tilde.adjunction (R := R)).comp
      (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ))).ofNatIsoRight
        (pushforwardGlobalSectionsIso φ)).leftAdjointUniq
    ((ModuleCat.extendRestrictScalarsAdj φ.hom).comp (tilde.adjunction (R := S)))

/-- The pullback of every actual affine quasicoherent sheaf is quasicoherent. -/
theorem isQuasicoherent_pullback (M : (Spec R).Modules) [M.IsQuasicoherent] :
    ((Scheme.Modules.pullback (Spec.map φ)).obj M).IsQuasicoherent := by
  let e := (Scheme.Modules.pullback (Spec.map φ)).mapIso (asIso M.fromTildeΓ).symm ≪≫
    (tildePullbackIso φ).app (moduleSpecΓFunctor.obj M)
  apply (SheafOfModules.isQuasicoherent (Spec S).ringCatSheaf).prop_of_iso e.symm
  exact inferInstanceAs (tilde ((ModuleCat.extendScalars φ.hom).obj
    (moduleSpecΓFunctor.obj M))).IsQuasicoherent

end AlgebraicGeometry.Scheme.Modules
