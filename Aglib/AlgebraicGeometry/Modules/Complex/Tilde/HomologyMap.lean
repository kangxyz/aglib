/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Complex.Tilde
public import Aglib.Algebra.Homology.HomologicalComplex.Adjunction

/-!
# Homology of the original affine counit mate

The native tilde–sections complex adjunction has the original termwise
counit. Exact tilde computes homology of its actual mate through that
counit, whenever the latter is a quasi-isomorphism. The section formula
retains the original tilde unit and does not require global sections to
preserve homology.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules.Complex

universe u w

variable (R : CommRingCat.{u}) {ι : Type w} (d : ComplexShape ι)

/-- The original actual counit chain map is the native complex adjunction counit. -/
theorem tildeGlobalSectionsCounit_eq_nativeCounit (K : HomologicalComplex (Spec R).Modules d) :
    tildeGlobalSectionsCounit R d K =
      ((tilde.adjunction (R := R)).mapHomologicalComplex d).counit.app K := by
  ext i : 1
  rw [tildeGlobalSectionsCounit_f]
  rfl

/-- The original native complex adjunction mate, followed by the actual counit, is the
specified original sheaf-complex map. -/
theorem tildeComplexHomEquiv_counit (C : HomologicalComplex (ModuleCat.{u} R) d)
    (K : HomologicalComplex (Spec R).Modules d)
    (ψ : ((tilde.functor R).mapHomologicalComplex d).obj C ⟶ K) :
    ((tilde.functor R).mapHomologicalComplex d).map
        (((tilde.adjunction (R := R)).mapHomologicalComplex d).homEquiv C K ψ) ≫
        tildeGlobalSectionsCounit R d K = ψ := by
  rw [tildeGlobalSectionsCounit_eq_nativeCounit, ← Adjunction.homEquiv_symm_apply]
  exact Equiv.symm_apply_apply _ _

/-- Homology of an actual module-complex map retains exact tilde's native comparison and
homology of the original counit, without exactness of global sections. -/
theorem tildeGlobalSectionsHomologyIso_map
    (C : HomologicalComplex (ModuleCat.{u} R) d) (K : HomologicalComplex (Spec R).Modules d)
    [QuasiIso (tildeGlobalSectionsCounit R d K)]
    (q : C ⟶ (moduleSpecΓFunctor.mapHomologicalComplex d).obj K) (i : ι) :
    (tilde.functor R).map (homologyMap q i) ≫ (tildeGlobalSectionsHomologyIso R d K i).hom =
      ((C.sc i).mapHomologyIso (tilde.functor R)).inv ≫
        homologyMap (((tilde.functor R).mapHomologicalComplex d).map q ≫
          tildeGlobalSectionsCounit R d K) i := by
  have hn := ShortComplex.mapHomologyIso_inv_naturality
    ((HomologicalComplex.shortComplexFunctor (ModuleCat.{u} R) d i).map q) (tilde.functor R)
  change (tilde.functor R).map (homologyMap q i) ≫
      ((((moduleSpecΓFunctor.mapHomologicalComplex d).obj K).sc i).mapHomologyIso
        (tilde.functor R)).inv =
    ((C.sc i).mapHomologyIso (tilde.functor R)).inv ≫
      homologyMap (((tilde.functor R).mapHomologicalComplex d).map q) i at hn
  simp only [tildeGlobalSectionsHomologyIso_hom, homologyMap_comp]
  rw [← Category.assoc, hn]
  exact Category.assoc _ _ _

/-- The actual native complex mate computes the homology map of the original sheaf-complex
arrow through the original affine counit comparison. -/
theorem tildeGlobalSectionsHomologyIso_mate
    (C : HomologicalComplex (ModuleCat.{u} R) d) (K : HomologicalComplex (Spec R).Modules d)
    [QuasiIso (tildeGlobalSectionsCounit R d K)]
    (ψ : ((tilde.functor R).mapHomologicalComplex d).obj C ⟶ K) (i : ι) :
    (tilde.functor R).map (homologyMap
        (((tilde.adjunction (R := R)).mapHomologicalComplex d).homEquiv C K ψ) i) ≫
        (tildeGlobalSectionsHomologyIso R d K i).hom =
      ((C.sc i).mapHomologyIso (tilde.functor R)).inv ≫ homologyMap ψ i := by
  rw [tildeGlobalSectionsHomologyIso_map, tildeComplexHomEquiv_counit]

/-- The section coordinate of actual counit-mate homology retains the original tilde units. -/
theorem tildeGlobalSectionsHomologyIso_mate_sections_unit
    (C : HomologicalComplex (ModuleCat.{u} R) d) (K : HomologicalComplex (Spec R).Modules d)
    [QuasiIso (tildeGlobalSectionsCounit R d K)]
    (ψ : ((tilde.functor R).mapHomologicalComplex d).obj C ⟶ K) (i : ι) :
    (tilde.toTildeΓNatIso (R := R)).hom.app (C.homology i) ≫
        moduleSpecΓFunctor.map ((C.sc i).mapHomologyIso (tilde.functor R)).inv ≫
        moduleSpecΓFunctor.map (homologyMap ψ i) =
      homologyMap (((tilde.adjunction (R := R)).mapHomologicalComplex d).homEquiv C K ψ) i ≫
        (tilde.toTildeΓNatIso (R := R)).hom.app
          (((moduleSpecΓFunctor.mapHomologicalComplex d).obj K).homology i) ≫
        moduleSpecΓFunctor.map (tildeGlobalSectionsHomologyIso R d K i).hom := by
  let q := ((tilde.adjunction (R := R)).mapHomologicalComplex d).homEquiv C K ψ
  have hm := congrArg moduleSpecΓFunctor.map
    (tildeGlobalSectionsHomologyIso_mate R d C K ψ i)
  simp only [Functor.map_comp] at hm
  have hu := ((tilde.toTildeΓNatIso (R := R)).hom.naturality (homologyMap q i)).symm
  change (tilde.toTildeΓNatIso (R := R)).hom.app (C.homology i) ≫
      moduleSpecΓFunctor.map ((tilde.functor R).map (homologyMap q i)) =
    homologyMap q i ≫ (tilde.toTildeΓNatIso (R := R)).hom.app
      (((moduleSpecΓFunctor.mapHomologicalComplex d).obj K).homology i) at hu
  rw [← hm]
  rw [← Category.assoc, hu, Category.assoc]

/-- In the original affine section coordinates, homology of the original native counit mate
is exactly homology of its module-complex mate. -/
theorem tildeGlobalSectionsHomologyIso_mate_sections
    (C : HomologicalComplex (ModuleCat.{u} R) d) (K : HomologicalComplex (Spec R).Modules d)
    [QuasiIso (tildeGlobalSectionsCounit R d K)]
    (ψ : ((tilde.functor R).mapHomologicalComplex d).obj C ⟶ K) (i : ι) :
    (tilde.toTildeΓNatIso (R := R)).hom.app (C.homology i) ≫
        moduleSpecΓFunctor.map ((C.sc i).mapHomologyIso (tilde.functor R)).inv ≫
        moduleSpecΓFunctor.map (homologyMap ψ i) ≫
        moduleSpecΓFunctor.map (tildeGlobalSectionsHomologyIso R d K i).inv ≫
        (tilde.toTildeΓNatIso (R := R)).inv.app
          (((moduleSpecΓFunctor.mapHomologicalComplex d).obj K).homology i) =
      homologyMap (((tilde.adjunction (R := R)).mapHomologicalComplex d).homEquiv C K ψ) i := by
  let E := moduleSpecΓFunctor.mapIso (tildeGlobalSectionsHomologyIso R d K i)
  let η := (tilde.toTildeΓNatIso (R := R)).app
    (((moduleSpecΓFunctor.mapHomologicalComplex d).obj K).homology i)
  let a := (tilde.toTildeΓNatIso (R := R)).hom.app (C.homology i) ≫
    moduleSpecΓFunctor.map ((C.sc i).mapHomologyIso (tilde.functor R)).inv ≫
    moduleSpecΓFunctor.map (homologyMap ψ i)
  have h := congrArg (fun z => z ≫ E.inv ≫ η.inv)
    (tildeGlobalSectionsHomologyIso_mate_sections_unit R d C K ψ i)
  change a ≫ E.inv ≫ η.inv =
    homologyMap (((tilde.adjunction (R := R)).mapHomologicalComplex d).homEquiv C K ψ) i ≫
      η.hom ≫ E.hom ≫ E.inv ≫ η.inv at h
  simp only [Iso.hom_inv_id_assoc, Iso.hom_inv_id, Category.comp_id] at h
  simpa only [a, E, η, Functor.mapIso_inv, Iso.app_inv, Category.assoc] using h

end AlgebraicGeometry.Scheme.Modules.Complex
