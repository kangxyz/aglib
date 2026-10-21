/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.RestrictionSections

/-! # Naturality of the original affine localization comparisons -/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u
open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Modules

variable {R S : CommRingCat.{u}} (φ : R ⟶ S)
  {M N : (Spec R).Modules} [M.IsQuasicoherent] [N.IsQuasicoherent]

/-- Original affine pullback section comparisons preserve actual coefficient maps. -/
@[reassoc]
theorem affinePullbackGlobalSectionsIso_naturality (q : M ⟶ N) :
    (ModuleCat.extendScalars φ.hom).map (moduleSpecΓFunctor.map q) ≫
      (affinePullbackGlobalSectionsIso φ N).hom =
    (affinePullbackGlobalSectionsIso φ M).hom ≫
      moduleSpecΓFunctor.map ((pullback (Spec.map φ)).map q) := by
  let E := ModuleCat.extendScalars φ.hom
  let P := pullback (Spec.map φ)
  let sM := (tildePullbackIso φ).inv.app (moduleSpecΓFunctor.obj M) ≫ P.map M.fromTildeΓ
  let sN := (tildePullbackIso φ).inv.app (moduleSpecΓFunctor.obj N) ≫ P.map N.fromTildeΓ
  have ht : (tilde.functor S).map (E.map (moduleSpecΓFunctor.map q)) ≫ sN =
      sM ≫ P.map q := by
    have hn := (tildePullbackIso φ).inv.naturality (moduleSpecΓFunctor.map q)
    have hc := fromTildeΓNatTrans.naturality q
    change (tilde.functor S).map (E.map (moduleSpecΓFunctor.map q)) ≫
      (tildePullbackIso φ).inv.app (moduleSpecΓFunctor.obj N) =
      (tildePullbackIso φ).inv.app (moduleSpecΓFunctor.obj M) ≫
        P.map (tilde.map (moduleSpecΓFunctor.map q)) at hn
    dsimp only [sM, sN]
    rw [← Category.assoc, hn, Category.assoc, ← P.map_comp]
    rw [show tilde.map (moduleSpecΓFunctor.map q) ≫ N.fromTildeΓ =
      M.fromTildeΓ ≫ q from hc, P.map_comp, Category.assoc]
  have hu := tilde.toTildeΓNatIso.hom.naturality (E.map (moduleSpecΓFunctor.map q))
  change E.map (moduleSpecΓFunctor.map q) ≫
      (tilde.toTildeΓNatIso.app (E.obj (moduleSpecΓFunctor.obj N))).hom =
    (tilde.toTildeΓNatIso.app (E.obj (moduleSpecΓFunctor.obj M))).hom ≫
      moduleSpecΓFunctor.map ((tilde.functor S).map
        (E.map (moduleSpecΓFunctor.map q))) at hu
  change E.map (moduleSpecΓFunctor.map q) ≫
      ((tilde.toTildeΓNatIso.app (E.obj (moduleSpecΓFunctor.obj N))).hom ≫
        moduleSpecΓFunctor.map sN) =
    ((tilde.toTildeΓNatIso.app (E.obj (moduleSpecΓFunctor.obj M))).hom ≫
      moduleSpecΓFunctor.map sM) ≫ moduleSpecΓFunctor.map (P.map q)
  rw [← Category.assoc, hu, Category.assoc, ← Functor.map_comp, ht,
    Functor.map_comp, Category.assoc]

/-- Original affine open localization preserves actual coefficient maps. -/
@[reassoc]
theorem affineRestrictGlobalSectionsIso_naturality [IsOpenImmersion (Spec.map φ)]
    (q : M ⟶ N) :
    (ModuleCat.extendScalars φ.hom).map (moduleSpecΓFunctor.map q) ≫
      (affineRestrictGlobalSectionsIso φ N).hom =
    (affineRestrictGlobalSectionsIso φ M).hom ≫
      moduleSpecΓFunctor.map ((restrictFunctor (Spec.map φ)).map q) := by
  have hn := (restrictFunctorIsoPullback (Spec.map φ)).inv.naturality q
  simp only [affineRestrictGlobalSectionsIso, Iso.trans_hom, Functor.mapIso_hom,
    Iso.symm_hom, Iso.app_hom]
  rw [← Category.assoc, affinePullbackGlobalSectionsIso_naturality, Category.assoc,
    ← Functor.map_comp, hn, Functor.map_comp, Category.assoc]

end AlgebraicGeometry.Scheme.Modules
