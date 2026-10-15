/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Stalk.Basic
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian

/-!
Source: `Quillen/AlgebraicGeometry/Scheme/Sheaf/GodementStalkReflection.lean` at LOCAL Quillen
`189a8e779f0c68b2dfc6f8195daebb3e684a5905`. Selection: whole_general;
source ranges [[1, 74]]. Actual objects, maps and hypotheses are preserved.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace AlgebraicGeometry.Scheme.Modules

/-- Actual module stalks jointly detect epimorphisms of arbitrary module sheaves. -/
theorem epi_of_moduleStalk {X : Scheme.{u}} {M N : X.Modules} (p : M ⟶ N)
    (hp : ∀ x, Epi ((moduleStalk X x).map p)) : Epi p := by
  apply Preadditive.epi_of_isZero_cokernel
  apply (isZero_iff_stalks _).mpr
  intro x
  have := hp x
  have hc : IsZero ((moduleStalk X x).obj (cokernel p)) :=
    (isZero_cokernel_of_epi ((moduleStalk X x).map p)).of_iso
      (PreservesCokernel.iso (moduleStalk X x) p)
  exact ((forget₂ (ModuleCat (X.presheaf.stalk x)) AddCommGrpCat.{u}).map_isZero hc).of_iso
    ((moduleStalkForgetIso X x).app (cokernel p)).symm

theorem isIso_of_moduleStalk {X : Scheme.{u}} {M N : X.Modules} (p : M ⟶ N)
    (hp : ∀ x, IsIso ((moduleStalk X x).map p)) : IsIso p := by
  let : Mono p := mono_of_moduleStalk p (fun x => by let := hp x; infer_instance)
  let : Epi p := epi_of_moduleStalk p (fun x => by let := hp x; infer_instance)
  exact isIso_of_mono_of_epi p

theorem godement_isZero_of_moduleStalks {X : Scheme.{u}} (M : X.Modules)
    (h : ∀ x, IsZero ((moduleStalk X x).obj M)) : IsZero M := by
  apply (isZero_iff_stalks _).mpr
  intro x
  exact ((forget₂ (ModuleCat (X.presheaf.stalk x)) AddCommGrpCat.{u}).map_isZero (h x)).of_iso
    ((moduleStalkForgetIso X x).app M).symm

theorem godement_quasiIso_of_moduleStalks {X : Scheme.{u}}
    {K L : CochainComplex X.Modules ℤ} (f : K ⟶ L)
    (h : ∀ x, QuasiIso (((moduleStalk X x).mapHomologicalComplex (.up ℤ)).map f)) :
    QuasiIso f where
  quasiIsoAt n := by
    rw [quasiIsoAt_iff_isIso_homologyMap]
    apply isIso_of_moduleStalk
    intro x
    let F := moduleStalk X x
    let t := (HomologicalComplex.shortComplexFunctor X.Modules (.up ℤ) n).map f
    have hq : ShortComplex.QuasiIso (F.mapShortComplex.map t) :=
      (quasiIsoAt_iff _ n).mp ((h x).quasiIsoAt n)
    have : IsIso (ShortComplex.homologyMap (F.mapShortComplex.map t)) :=
      (ShortComplex.quasiIso_iff _).mp hq
    have he : F.map (HomologicalComplex.homologyMap f n) =
        ((K.sc n).mapHomologyIso F).inv ≫
          ShortComplex.homologyMap (F.mapShortComplex.map t) ≫
            ((L.sc n).mapHomologyIso F).hom := by
      symm
      change ((K.sc n).mapHomologyIso F).inv ≫
          ShortComplex.homologyMap (F.mapShortComplex.map t) ≫ ((L.sc n).mapHomologyIso F).hom =
            F.map (ShortComplex.homologyMap t)
      rw [ShortComplex.mapHomologyIso_hom_naturality t F]
      simp only [Iso.inv_hom_id_assoc]
    rw [he]
    infer_instance

end AlgebraicGeometry.Scheme.Modules
