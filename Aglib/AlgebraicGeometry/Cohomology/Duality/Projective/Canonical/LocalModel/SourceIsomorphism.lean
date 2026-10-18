/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.ClosedImmersion.RightAdjoint.Affine.SourceIsomorphism
public import Aglib.AlgebraicGeometry.Cohomology.ClosedImmersion.RightAdjoint.RegularList.Sheaf.Localization

/-!
# Source isomorphisms on the original closed-adjoint resolution

The actual open comparison over the identity ambient chart induces native
Yoneda precomposition by the source ring isomorphism. Both the geometric
resolution and its affine coinduction comparison remain the original ones.
-/

@[expose] public section
noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open HomologicalComplex CochainComplex CochainComplex.HomComplex

universe u w
namespace AlgebraicGeometry.Scheme.Modules

section Coinduction
variable {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
  (σ : R →+* S) (τ : R →+* T) (ρ : S →+* T)
  (ν : (ModuleCat.restrictScalars τ).obj (ModuleCat.of T T) ⟶
    (ModuleCat.restrictScalars σ).obj (ModuleCat.of S S))
  {M : ModuleCat.{u} R} (I : InjectiveResolution M)

private abbrev coinducedResolution (φ : R →+* S) :=
  ((ModuleCat.coextendScalars φ).mapHomologicalComplex (.up ℤ)).obj I.cochainComplex

private theorem sourceCycles_precomp
    (F : coinducedResolution I σ ⟶
      ((ModuleCat.restrictScalars ρ).mapHomologicalComplex (.up ℤ)).obj
        (coinducedResolution I τ)) (n : ℤ)
    (hF : ∀ (x : (coinducedResolution I σ).X n) (t : T),
      ModuleCat.CoextendScalars.equiv τ _ (F.f n x) t =
        ModuleCat.CoextendScalars.equiv σ _ x (ν t))
    (z : (coinducedResolution I σ).cycles n) :
    (ModuleCat.coextendScalarsCyclesIso τ I.cochainComplex n).hom
        ((((coinducedResolution I τ).sc n).mapCyclesIso
          (ModuleCat.restrictScalars ρ)).hom (cyclesMap F n z)) =
      ((ModuleCat.coextendScalarsCyclesIso σ I.cochainComplex n).hom z).precomp
        ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).map ν) := by
  let K := coinducedResolution I σ
  let L := coinducedResolution I τ
  let U := ModuleCat.restrictScalars ρ
  let z' := ((L.sc n).mapCyclesIso U).hom (cyclesMap F n z)
  have hi : L.iCycles n z' = F.f n (K.iCycles n z) := by
    have h := congrArg (fun f : K.cycles n ⟶ U.obj (L.X n) => f.hom z)
      (show cyclesMap F n ≫ ((L.sc n).mapCyclesIso U).hom ≫ U.map (L.iCycles n) =
        K.iCycles n ≫ F.f n by
        erw [ShortComplex.mapCyclesIso_hom_iCycles]
        exact cyclesMap_i F n)
    exact h
  apply Subtype.ext
  change ((ModuleCat.coextendScalarsCyclesIso τ I.cochainComplex n).hom z').1 =
    (Cochain.ofHom ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).map ν)).comp
      ((ModuleCat.coextendScalarsCyclesIso σ I.cochainComplex n).hom z).1 (zero_add n)
  rw [ModuleCat.coextendScalarsCyclesIso_coe, hi,
    ModuleCat.coextendScalarsCochainEquiv_apply,
    ModuleCat.coextendScalarsCyclesIso_coe,
    ModuleCat.coextendScalarsCochainEquiv_apply, ← Cochain.fromSingleMk_precomp]
  congr 1
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro t
  exact hF (K.iCycles n z) t

set_option maxHeartbeats 800000 in
-- The native cycles and scalar-restriction comparisons elaborate across three module categories.
private theorem sourceHomology_precomp [HasExt.{w} (ModuleCat.{u} R)]
    (F : coinducedResolution I σ ⟶
      ((ModuleCat.restrictScalars ρ).mapHomologicalComplex (.up ℤ)).obj
        (coinducedResolution I τ)) (n : ℕ)
    (hF : ∀ (x : (coinducedResolution I σ).X (n : ℤ)) (t : T),
      ModuleCat.CoextendScalars.equiv τ _ (F.f (n : ℤ) x) t =
        ModuleCat.CoextendScalars.equiv σ _ x (ν t))
    (x : (coinducedResolution I σ).homology (n : ℤ)) :
    ModuleCat.coextendScalarsResolutionExtAddEquiv τ I n
        ((((coinducedResolution I τ).sc (n : ℤ)).mapHomologyIso
          (ModuleCat.restrictScalars ρ)).hom (homologyMap F (n : ℤ) x)) =
      (Ext.mk₀ ν).comp (ModuleCat.coextendScalarsResolutionExtAddEquiv σ I n x)
        (zero_add n) := by
  let A := (ModuleCat.restrictScalars σ).obj (ModuleCat.of S S)
  let K := coinducedResolution I σ
  let L := coinducedResolution I τ
  let U := ModuleCat.restrictScalars ρ
  let E := ModuleCat.coextendScalarsResolutionExtAddEquiv σ I n
  let C := ModuleCat.coextendScalarsCyclesIso σ I.cochainComplex (n : ℤ)
  obtain ⟨f, hf, hfx⟩ := I.extMk_surjective (E x) (n + 1) rfl
  let c : Cocycle ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj A)
      I.cochainComplex (n : ℤ) :=
    Cocycle.fromSingleMk (f ≫ (I.cochainComplexXIso n n rfl).inv)
      (zero_add _) ((n + 1 : ℕ) : ℤ) (by lia)
      (by
        erw [I.cochainComplex_d (n : ℤ) ((n + 1 : ℕ) : ℤ) n (n + 1) rfl rfl]
        simp only [Category.assoc, Iso.inv_hom_id_assoc, reassoc_of% hf, zero_comp])
  let z : K.cycles (n : ℤ) := C.inv c
  have hc : C.hom z = c := Iso.inv_hom_id_apply C c
  have hz : E (K.homologyπ (n : ℤ) z) = I.extMk f (n + 1) rfl hf := by
    rw [ModuleCat.coextendScalarsResolutionExtAddEquiv_homologyπ, hc]
    rfl
  have hzx : K.homologyπ (n : ℤ) z = x := E.injective (hz.trans hfx)
  let z' := ((L.sc (n : ℤ)).mapCyclesIso U).hom (cyclesMap F (n : ℤ) z)
  have hp : ((L.sc (n : ℤ)).mapHomologyIso U).hom
      (homologyMap F (n : ℤ) (K.homologyπ (n : ℤ) z)) = L.homologyπ (n : ℤ) z' := by
    exact congrArg (fun f : K.cycles (n : ℤ) ⟶ U.obj (L.homology (n : ℤ)) => f.hom z)
      (show K.homologyπ (n : ℤ) ≫ homologyMap F (n : ℤ) ≫
          ((L.sc (n : ℤ)).mapHomologyIso U).hom =
        cyclesMap F (n : ℤ) ≫ ((L.sc (n : ℤ)).mapCyclesIso U).hom ≫
          U.map (L.homologyπ (n : ℤ)) by
        rw [homologyπ_naturality_assoc]
        exact congrArg (fun f => cyclesMap F (n : ℤ) ≫ f)
          (ShortComplex.homologyπ_mapHomologyIso_hom U (L.sc (n : ℤ))))
  have hcs : (ModuleCat.coextendScalarsCyclesIso τ I.cochainComplex (n : ℤ)).hom z' =
      c.precomp ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).map ν) := by
    rw [sourceCycles_precomp σ τ ρ ν I F (n : ℤ) hF z, hc]
  have hclass : I.extAddEquivCohomologyClass.symm
      (CohomologyClass.mk (c.precomp
        ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).map ν))) =
      (Ext.mk₀ ν).comp (I.extMk f (n + 1) rfl hf) (zero_add n) := by
    rw [I.mk₀_comp_extMk]
    change I.extEquivCohomologyClass.symm _ = _
    apply I.extEquivCohomologyClass.injective
    simp only [Equiv.apply_symm_apply, I.extEquivCohomologyClass_extMk]
    apply congrArg CohomologyClass.mk
    dsimp only [c]
    rw [← Cocycle.fromSingleMk_precomp]
    simp only [Category.assoc]
  rw [← hzx, hp, ModuleCat.coextendScalarsResolutionExtAddEquiv_homologyπ, hcs]
  exact hclass.trans (congrArg (fun e => (Ext.mk₀ ν).comp e (zero_add n)) hz.symm)
end Coinduction

section AffineCycles
variable {A B : CommRingCat.{u}}

/-- The original affine sections of the supplied closed-adjoint resolution. -/
abbrev closedImmersionSourceResolutionComplex {L : (Spec A).Modules}
    (J : InjectiveResolution L) (φ : A ⟶ B) [IsClosedImmersion (Spec.map φ)] :=
  ((moduleSpecΓFunctor (R := B)).mapHomologicalComplex (.up ℤ)).obj
    (((closedImmersionRightAdjoint (Spec.map φ)).mapHomologicalComplex (.up ℤ)).obj
      J.cochainComplex)

variable (φ : A ⟶ B) [IsClosedImmersion (Spec.map φ)]
  {L : (Spec A).Modules} [L.IsQuasicoherent] (J : InjectiveResolution L)

/-- The original sections comparison acts by the ordinary affine Hom formula and
then the unchanged resolution-extension component. -/
theorem affineClosedRightAdjointResolutionSectionsIso_hom_f_apply (n : ℤ)
    (x : (closedImmersionSourceResolutionComplex J φ).X n) (b : B) :
    ModuleCat.CoextendScalars.equiv φ.hom _
        ((affineClosedRightAdjointResolutionSectionsIso φ J).hom.f n x) b =
      (J.cocomplex.mapExtendIso (moduleSpecΓFunctor (R := A))
        ComplexShape.embeddingUpNat).hom.f n
          (closedImmersionRightAdjointSectionsLinearEquiv φ (J.cochainComplex.X n) x b) := rfl

variable [HasExt.{w} (ModuleCat.{u} A)]

/-- Projecting an original geometric cycle gives its unchanged native resolution
Ext class through the actual affine sections comparison. -/
theorem affineClosedRightAdjointResolutionExtAddEquiv_homologyπ (n : ℕ)
    (z : (closedImmersionSourceResolutionComplex J φ).cycles (n : ℤ)) :
    affineClosedRightAdjointResolutionExtAddEquiv φ J n
        ((closedImmersionSourceResolutionComplex J φ).homologyπ (n : ℤ) z) =
      (AffineDerived.globalSectionsInjectiveResolution J).extAddEquivCohomologyClass.symm
        (CohomologyClass.mk
          ((ModuleCat.coextendScalarsCyclesIso φ.hom
            (AffineDerived.globalSectionsInjectiveResolution J).cochainComplex (n : ℤ)).hom
            (cyclesMap (affineClosedRightAdjointResolutionSectionsIso φ J).hom (n : ℤ) z))) := by
  change ModuleCat.coextendScalarsResolutionExtAddEquiv φ.hom
    (AffineDerived.globalSectionsInjectiveResolution J) n
      (homologyMap (affineClosedRightAdjointResolutionSectionsIso φ J).hom (n : ℤ)
        ((closedImmersionSourceResolutionComplex J φ).homologyπ (n : ℤ) z)) = _
  exact (congrArg (ModuleCat.coextendScalarsResolutionExtAddEquiv φ.hom
      (AffineDerived.globalSectionsInjectiveResolution J) n)
    (ConcreteCategory.congr_hom
      (homologyπ_naturality
        (affineClosedRightAdjointResolutionSectionsIso φ J).hom (n : ℤ)) z)).trans
    (ModuleCat.coextendScalarsResolutionExtAddEquiv_homologyπ φ.hom
      (AffineDerived.globalSectionsInjectiveResolution J) n _)

end AffineCycles

section Geometry
variable {A B C : CommRingCat.{u}} (σ : A ⟶ B) (τ : A ⟶ C) (e : C ≃+* B)
  [IsClosedImmersion (Spec.map σ)] [IsClosedImmersion (Spec.map τ)]
  (h : IsPullback (Spec.map e.toCommRingCatIso.inv) (Spec.map τ)
    (Spec.map σ) (𝟙 (Spec A)))

include h in
omit [IsClosedImmersion (Spec.map σ)] [IsClosedImmersion (Spec.map τ)] in
theorem closedImmersionSourceRingSquare : τ ≫ e.toCommRingCatIso.hom = σ := by
  have hh : σ ≫ e.toCommRingCatIso.inv = τ := by
    apply Spec.map_injective
    simpa only [Spec.map_comp, Category.comp_id] using h.w
  rw [← hh, Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- The original source equivalence, linear over the unchanged ambient ring. -/
def closedImmersionSourceModuleIso :
    (ModuleCat.restrictScalars τ.hom).obj (ModuleCat.of C C) ≅
      (ModuleCat.restrictScalars σ.hom).obj (ModuleCat.of B B) :=
  by
    refine ModuleCat.isoMk e.toAddEquiv.toAddCommGrpIso ?_
    intro a
    ext c
    change σ.hom a * e (show C from c) = e (τ.hom a * (show C from c))
    rw [map_mul]
    congr 1
    exact (congrArg (fun f : A ⟶ B => f.hom a) (closedImmersionSourceRingSquare σ τ e h)).symm

omit [IsClosedImmersion (Spec.map σ)] [IsClosedImmersion (Spec.map τ)] in
@[simp] theorem closedImmersionSourceModuleIso_hom_apply (c : C) :
    (closedImmersionSourceModuleIso σ τ e h).hom c = e c := rfl

private theorem sectionsLinearEquiv_naturality {D E : (Spec A).Modules} (f : D ⟶ E)
    (x : moduleSpecΓFunctor.obj ((closedImmersionRightAdjoint (Spec.map σ)).obj D)) (b : B) :
    closedImmersionRightAdjointSectionsLinearEquiv σ E
        (moduleSpecΓFunctor.map ((closedImmersionRightAdjoint (Spec.map σ)).map f) x) b =
      moduleSpecΓFunctor.map f (closedImmersionRightAdjointSectionsLinearEquiv σ D x b) := by
  exact congrArg (fun y => ModuleCat.CoextendScalars.equiv σ.hom _ y b)
    (ConcreteCategory.congr_hom ((closedImmersionRightAdjointAffineIso σ).hom.naturality f) x)

/-- The degreewise native source comparison commutes with every coefficient arrow. -/
@[reassoc] theorem closedImmersionRightAdjointSourceIsoSections_naturality
    {D E : (Spec A).Modules} (f : D ⟶ E) :
    moduleSpecΓFunctor.map ((closedImmersionRightAdjoint (Spec.map σ)).map f) ≫
        closedImmersionRightAdjointSourceIsoSections σ τ e h E =
      closedImmersionRightAdjointSourceIsoSections σ τ e h D ≫
        (ModuleCat.restrictScalars e.toCommRingCatIso.inv.hom).map
          (moduleSpecΓFunctor.map ((closedImmersionRightAdjoint (Spec.map τ)).map f)) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply (closedImmersionRightAdjointSectionsLinearEquiv τ E).injective
  apply LinearMap.ext
  intro c
  change closedImmersionRightAdjointSectionsLinearEquiv τ E
      (closedImmersionRightAdjointSourceIsoSections σ τ e h E
        (moduleSpecΓFunctor.map ((closedImmersionRightAdjoint (Spec.map σ)).map f) x)) c =
    closedImmersionRightAdjointSectionsLinearEquiv τ E
      (moduleSpecΓFunctor.map ((closedImmersionRightAdjoint (Spec.map τ)).map f)
        (closedImmersionRightAdjointSourceIsoSections σ τ e h D x)) c
  rw [closedImmersionRightAdjointSourceIsoSections_apply,
    sectionsLinearEquiv_naturality, sectionsLinearEquiv_naturality,
    closedImmersionRightAdjointSourceIsoSections_apply]

/-- The actual geometric source comparison on the same coefficient resolution. -/
def closedImmersionSourceResolutionMap {L : (Spec A).Modules} (J : InjectiveResolution L) :
    closedImmersionSourceResolutionComplex J σ ⟶
      ((ModuleCat.restrictScalars e.toCommRingCatIso.inv.hom).mapHomologicalComplex (.up ℤ)).obj
        (closedImmersionSourceResolutionComplex J τ) where
  f n := closedImmersionRightAdjointSourceIsoSections σ τ e h (J.cochainComplex.X n)
  comm' i j _hij := (closedImmersionRightAdjointSourceIsoSections_naturality σ τ e h
    (J.cochainComplex.d i j)).symm

/-- The original homology comparison, followed by the native scalar-restriction comparison. -/
def closedImmersionSourceHomologyMap {L : (Spec A).Modules} (J : InjectiveResolution L) (n : ℤ) :
    (closedImmersionSourceResolutionComplex J σ).homology n ⟶
      (ModuleCat.restrictScalars e.toCommRingCatIso.inv.hom).obj
        ((closedImmersionSourceResolutionComplex J τ).homology n) :=
  homologyMap (closedImmersionSourceResolutionMap σ τ e h J) n ≫
    (((closedImmersionSourceResolutionComplex J τ).sc n).mapHomologyIso
      (ModuleCat.restrictScalars e.toCommRingCatIso.inv.hom)).hom

variable {L : (Spec A).Modules} [L.IsQuasicoherent] (J : InjectiveResolution L)

private theorem sourceResolutionSections_apply (n : ℤ)
    (x : (closedImmersionSourceResolutionComplex J σ).X n) (c : C) :
    ModuleCat.CoextendScalars.equiv τ.hom _
        ((affineClosedRightAdjointResolutionSectionsIso τ J).hom.f n
          ((closedImmersionSourceResolutionMap σ τ e h J).f n x)) c =
      ModuleCat.CoextendScalars.equiv σ.hom _
        ((affineClosedRightAdjointResolutionSectionsIso σ J).hom.f n x) (e c) := by
  rw [affineClosedRightAdjointResolutionSectionsIso_hom_f_apply,
    affineClosedRightAdjointResolutionSectionsIso_hom_f_apply]
  exact congrArg ((J.cocomplex.mapExtendIso (moduleSpecΓFunctor (R := A))
    ComplexShape.embeddingUpNat).hom.f n)
      (closedImmersionRightAdjointSourceIsoSections_apply σ τ e h (J.cochainComplex.X n) x c)

variable [HasExt.{w} (ModuleCat.{u} A)]

set_option maxHeartbeats 800000 in
-- The proof retains both original affine homology comparisons and their scalar-restriction maps.
/-- The actual geometric source-isomorphism map on the original fixed resolution
is native Yoneda precomposition by the same source module isomorphism. -/
theorem closedImmersionSourceHomologyMap_ext (n : ℕ)
    (x : (closedImmersionSourceResolutionComplex J σ).homology (n : ℤ)) :
    affineClosedRightAdjointResolutionExtAddEquiv τ J n
        (closedImmersionSourceHomologyMap σ τ e h J (n : ℤ) x) =
      (Ext.mk₀ (closedImmersionSourceModuleIso σ τ e h).hom).comp
        (affineClosedRightAdjointResolutionExtAddEquiv σ J n x) (zero_add n) := by
  let I := AffineDerived.globalSectionsInjectiveResolution J
  let K := closedImmersionSourceResolutionComplex J σ
  let L := closedImmersionSourceResolutionComplex J τ
  let U := ModuleCat.restrictScalars e.toCommRingCatIso.inv.hom
  let Q := coinducedResolution I τ.hom
  let Eσ := affineClosedRightAdjointResolutionSectionsIso σ J
  let Eτ := affineClosedRightAdjointResolutionSectionsIso τ J
  let G := closedImmersionSourceResolutionMap σ τ e h J
  let F := Eσ.inv ≫ G ≫ (U.mapHomologicalComplex (.up ℤ)).map Eτ.hom
  have hF : ∀ (y : (coinducedResolution I σ.hom).X (n : ℤ)) (c : C),
      ModuleCat.CoextendScalars.equiv τ.hom _ (F.f (n : ℤ) y) c =
        ModuleCat.CoextendScalars.equiv σ.hom _ y
          ((closedImmersionSourceModuleIso σ τ e h).hom c) := by
    intro y c
    have hh := sourceResolutionSections_apply σ τ e h J (n : ℤ) (Eσ.inv.f (n : ℤ) y) c
    have hy : Eσ.hom.f (n : ℤ) (Eσ.inv.f (n : ℤ) y) = y :=
      Iso.inv_hom_id_apply
        ((HomologicalComplex.eval (ModuleCat.{u} B) (.up ℤ) (n : ℤ)).mapIso Eσ) y
    change ModuleCat.CoextendScalars.equiv τ.hom _
      (Eτ.hom.f (n : ℤ) (G.f (n : ℤ) (Eσ.inv.f (n : ℤ) y))) c = _
    rw [hh, hy]
    rfl
  have hcomp : Eσ.hom ≫ F = G ≫ (U.mapHomologicalComplex (.up ℤ)).map Eτ.hom := by
    simp only [F, Iso.hom_inv_id_assoc]
  have hcompH := congrArg ((homologyFunctor (ModuleCat.{u} B) (.up ℤ) (n : ℤ)).map) hcomp
  simp only [Functor.map_comp] at hcompH
  change homologyMap Eσ.hom (n : ℤ) ≫ homologyMap F (n : ℤ) =
    homologyMap G (n : ℤ) ≫
      homologyMap ((U.mapHomologicalComplex (.up ℤ)).map Eτ.hom) (n : ℤ) at hcompH
  have hnat : homologyMap ((U.mapHomologicalComplex (.up ℤ)).map Eτ.hom) (n : ℤ) ≫
      ((Q.sc (n : ℤ)).mapHomologyIso U).hom =
    ((L.sc (n : ℤ)).mapHomologyIso U).hom ≫ U.map (homologyMap Eτ.hom (n : ℤ)) := by
    exact ShortComplex.mapHomologyIso_hom_naturality
      ((HomologicalComplex.shortComplexFunctor (ModuleCat.{u} C) (.up ℤ) (n : ℤ)).map Eτ.hom) U
  have hh : homologyMap Eσ.hom (n : ℤ) ≫ homologyMap F (n : ℤ) ≫
        ((Q.sc (n : ℤ)).mapHomologyIso U).hom =
      closedImmersionSourceHomologyMap σ τ e h J (n : ℤ) ≫
        U.map (homologyMap Eτ.hom (n : ℤ)) := by
    calc
      _ = homologyMap G (n : ℤ) ≫
          homologyMap ((U.mapHomologicalComplex (.up ℤ)).map Eτ.hom) (n : ℤ) ≫
          ((Q.sc (n : ℤ)).mapHomologyIso U).hom := by
        simpa only [Category.assoc] using congrArg
          (fun f => f ≫ ((Q.sc (n : ℤ)).mapHomologyIso U).hom) hcompH
      _ = _ := by
        erw [hnat]
        rfl
  have hx := ConcreteCategory.congr_hom hh x
  have hExt := sourceHomology_precomp σ.hom τ.hom e.toCommRingCatIso.inv.hom
    (closedImmersionSourceModuleIso σ τ e h).hom I F n hF
      (homologyMap Eσ.hom (n : ℤ) x)
  change ModuleCat.coextendScalarsResolutionExtAddEquiv τ.hom I n
      (homologyMap Eτ.hom (n : ℤ)
        (closedImmersionSourceHomologyMap σ τ e h J (n : ℤ) x)) =
    (Ext.mk₀ (closedImmersionSourceModuleIso σ τ e h).hom).comp
      (ModuleCat.coextendScalarsResolutionExtAddEquiv σ.hom I n
        (homologyMap Eσ.hom (n : ℤ) x)) (zero_add n)
  exact (congrArg (ModuleCat.coextendScalarsResolutionExtAddEquiv τ.hom I n) hx).symm.trans hExt

/-- The inverse source factor of the original principal-localization class is
cancelled by this same native source-isomorphism comparison. -/
theorem closedImmersionSourceHomologyMap_ext_cancel (n : ℕ)
    (ξ : Ext.{w} ((ModuleCat.restrictScalars τ.hom).obj (ModuleCat.of C C))
      (moduleSpecΓFunctor.obj L) n) :
    affineClosedRightAdjointResolutionExtAddEquiv τ J n
      (closedImmersionSourceHomologyMap σ τ e h J (n : ℤ)
        ((affineClosedRightAdjointResolutionExtAddEquiv σ J n).symm
          ((Ext.mk₀ (closedImmersionSourceModuleIso σ τ e h).inv).comp ξ (zero_add n)))) = ξ := by
  rw [closedImmersionSourceHomologyMap_ext, AddEquiv.apply_symm_apply,
    Ext.mk₀_comp_mk₀_assoc, Iso.hom_inv_id, Ext.mk₀_id_comp]

end Geometry
end AlgebraicGeometry.Scheme.Modules
