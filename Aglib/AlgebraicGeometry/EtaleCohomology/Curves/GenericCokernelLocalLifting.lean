/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Curves.GenericLocalUnitExtension
public import Aglib.AlgebraicGeometry.Sites.EtaleOpenRestriction

/-!
# Actual local lifting for the original generic-unit cokernel

Every original generic direct-image section lifts to an original Gm section
on an affine open neighborhood of each generic image point. The conclusion
uses the literal small-etale restriction and original coefficient unit.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open GroupCohomology.Kummer.Coefficients GroupCohomology.Kummer.CoefficientBaseChange

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Curves

universe u

variable {X : Scheme.{u}} [IsNoetherian X] (U : X.Etale) [QuasiCompact U.hom]

/-- Literal affine local lifting of an original generic direct-image section. -/
theorem exists_genericUnit_local_lift
    (a : ((directImage (genericArtinMap X)).obj (gm (genericArtinLocus X))).obj.obj (op U))
    (p : (pullback U.hom (genericArtinMap X) : Scheme.{u})) :
    ∃ (W : U.left.Opens) (_ : IsAffineOpen W)
      (_hpW : (pullback.fst U.hom (genericArtinMap X)) p ∈ W)
      (b : (gm X).obj.obj (op (Etale.openChart U W))),
      (genericArtinUnit X).hom.app (op (Etale.openChart U W)) b =
        (((directImage (genericArtinMap X)).obj (gm (genericArtinLocus X))).obj.map
          (Etale.openChartHom U W).op) a := by
  let : IsNoetherian U.left := {
    toIsLocallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian (X := U.left) (Y := X) U.hom
    toCompactSpace := QuasiCompact.compactSpace_of_compactSpace (X := U.left) (Y := X) U.hom }
  let t := (unitsSections (genericArtinLocus X)
    ((siteBaseChange (genericArtinMap X)).op.obj (op U)) a).toMul
  obtain ⟨W, hW, hpW, s, hs⟩ := exists_generic_local_unit_extension U t p
  let : QuasiCompact (W.ι ≫ U.hom) := inferInstance
  let : IsArtinianScheme (pullback (W.ι ≫ U.hom) (genericArtinMap X)) :=
    genericArtinBaseChange_isArtinian (X := X) (U := W.toScheme) (W.ι ≫ U.hom)
  let b := (unitsSections X (op (Etale.openChart U W))).symm
    (Additive.ofMul (Units.map (Etale.openChartSections U W).hom.toMonoidHom s))
  refine ⟨W, hW, hpW, b, ?_⟩
  have hl := hs (pullback (W.ι ≫ U.hom) (genericArtinMap X))
    (Etale.openChartBaseChangeMap U W (genericArtinMap X))
    (Etale.openChartBaseChangeMap_mem U W (genericArtinMap X))
  have hc : Units.map
      ((Etale.openChartBaseChangeMap U W (genericArtinMap X) ≫
        pullback.fst U.hom (genericArtinMap X)).appLE W ⊤
        (fun q _ => Etale.openChartBaseChangeMap_mem U W (genericArtinMap X) q)).hom.toMonoidHom s =
      Units.map (pullback.fst (W.ι ≫ U.hom) (genericArtinMap X)).appTop.hom.toMonoidHom
        (Units.map (Etale.openChartSections U W).hom.toMonoidHom s) := by
    apply Units.ext
    exact ConcreteCategory.congr_hom
      (Etale.openChartBaseChangeMap_appLE U W (genericArtinMap X)) (s : Γ(U.left, W))
  have ha := unitsSections_naturality (genericArtinLocus X)
    (((siteBaseChange (genericArtinMap X)).map (Etale.openChartHom U W)).op) a
  have hb := gmUnit_sections (genericArtinMap X) (op (Etale.openChart U W)) b
  simp only [b, AddEquiv.apply_symm_apply, toMul_ofMul] at hb
  apply (unitsSections (genericArtinLocus X)
    ((siteBaseChange (genericArtinMap X)).op.obj (op (Etale.openChart U W)))).injective
  exact congrArg Additive.ofMul (hb.trans (hc.symm.trans (hl.symm.trans ha.symm)))

end AlgebraicGeometry.Scheme.EtaleCohomology.Curves
