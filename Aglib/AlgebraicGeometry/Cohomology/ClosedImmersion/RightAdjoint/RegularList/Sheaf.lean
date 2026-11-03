/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import
  Aglib.AlgebraicGeometry.Cohomology.ClosedImmersion.RightAdjoint.RegularList.Sheaf.Counit

/-!
# Installed affine sheaf purity for a regular quotient

For an ordered finite weakly regular list in an arbitrary commutative ring, the actual
installed bounded-below closed right adjoint sends a quasicoherent ring-framed
coefficient to the original quotient structure sheaf in the list-length degree.
The native single-homology reconstruction retains the original ordered Koszul top
class and the actual resolution unit. The result is independent of the supplied
sheaf resolution. The Ext size and both sheaf derived-category sizes are independent;
empty lists, unit quotients and zero rings are included.
-/

universe u w z u1 v1 w1 r1 a b

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Modules
open scoped TensorProduct ChangeOfRings

open CategoryTheory.Abelian HomologicalComplex CochainComplex
private def extIsoTransport {C : Type u1} [Category.{v1} C] [Abelian C] [HasExt.{w1} C]
    (R : Type r1) [CommRing R] [Linear R C] {X X' Y Y' : C}
    (eX : X' ≅ X) (eY : Y ≅ Y') (n : ℕ) : Ext X Y n ≃ₗ[R] Ext X' Y' n where
  toFun x := ((Ext.mk₀ eX.hom).comp x (zero_add n)).comp (Ext.mk₀ eY.hom) (add_zero n)
  invFun y := ((Ext.mk₀ eX.inv).comp y (zero_add n)).comp (Ext.mk₀ eY.inv) (add_zero n)
  left_inv x := by
    simp only [Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀,
      Iso.hom_inv_id, Ext.comp_mk₀_id, Ext.mk₀_comp_mk₀_assoc,
      Iso.inv_hom_id, Ext.mk₀_id_comp]
  right_inv x := by
    simp only [Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀,
      Iso.inv_hom_id, Ext.comp_mk₀_id, Ext.mk₀_comp_mk₀_assoc,
      Iso.hom_inv_id, Ext.mk₀_id_comp]
  map_add' x y := by simp only [Ext.comp_add, Ext.add_comp]
  map_smul' a x := by
    simp only [Ext.comp_smul, Ext.smul_comp]
    rfl

namespace AlgebraicGeometry.Scheme.Modules
section NativeModelAliases
local instance (B : CommRingCat.{u}) : (moduleSpecΓFunctor (R := B)).Additive :=
  moduleSpecΓFunctor_additive B
variable {R : CommRingCat.{u}}
private abbrev quotientSpecRing (I : Ideal R) : CommRingCat.{u} := .of (R ⧸ I)
private abbrev quotientSpecMap (I : Ideal R) : R ⟶ quotientSpecRing I :=
  CommRingCat.ofHom (Ideal.Quotient.mk I)
variable {S : CommRingCat.{u}}
private abbrev closedΓResolutionIso (q : R ⟶ S) [IsClosedImmersion (Spec.map q)]
    {L : (Spec R).Modules} [L.IsQuasicoherent] (J : InjectiveResolution L) :=
  affineClosedRightAdjointResolutionSectionsIso q J
private abbrev closedΓResolutionExtAddEquiv [HasExt.{w} (ModuleCat.{u} R)]
    (q : R ⟶ S) [IsClosedImmersion (Spec.map q)] {L : (Spec R).Modules} [L.IsQuasicoherent]
    (J : InjectiveResolution L) (n : ℕ) := affineClosedRightAdjointResolutionExtAddEquiv q J n
private abbrev closedΓResolutionComplex (q : R ⟶ S) [IsClosedImmersion (Spec.map q)]
    {L : (Spec R).Modules} (J : InjectiveResolution L) :=
  ((moduleSpecΓFunctor (R := S)).mapHomologicalComplex (.up ℤ)).obj
    (((closedImmersionRightAdjoint (Spec.map q)).mapHomologicalComplex (.up ℤ)).obj
      J.cochainComplex)

variable (s : List R) {L : (Spec R).Modules}
private abbrev regularClosedResolutionComplex (J : InjectiveResolution L) :=
  closedImmersionRightAdjointRegularListResolutionComplex s J
variable (hs : RingTheory.Sequence.IsWeaklyRegular R s) [L.IsQuasicoherent]
  (J : InjectiveResolution L) (e : moduleSpecΓFunctor.obj L ≅ ModuleCat.of R R)
private abbrev regularClosedResolutionTildeCounit_quasiIso :=
  closedImmersionRightAdjointRegularListResolutionTildeCounit_quasiIso s hs J e
private abbrev regularClosedResolutionHomology_isZero (n : ℤ) (hn : n ≠ (s.length : ℤ)) :=
  closedImmersionRightAdjointRegularListResolutionHomology_isZero s hs J e n hn
variable [HasExt.{w} (ModuleCat.{u} R)]
private abbrev regularClosedTopSectionsLinearEquiv :=
  closedImmersionRightAdjointRegularListResolutionTopSectionsLinearEquiv s hs J e
private abbrev regularClosedResolutionTopHomologyIso :=
  closedImmersionRightAdjointRegularListResolutionTopHomologyIso s hs J e
end NativeModelAliases
end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Modules
section InstalledDerived
variable {R : CommRingCat.{u}} [HasExt.{w} (ModuleCat.{u} R)]
  (s : List R) (hs : RingTheory.Sequence.IsWeaklyRegular R s)
  {L : (Spec R).Modules} [L.IsQuasicoherent] (J : InjectiveResolution L)
  (e : (moduleSpecΓFunctor (R := R)).obj L ≅ ModuleCat.of R R)
  [HasDerivedCategory.{a} (Spec R).Modules]
  [HasDerivedCategory.{b} (Spec (quotientSpecRing (Ideal.ofList s))).Modules]

private def regularClosedDerivedModelHomologyIso (n : ℤ) :
    (DerivedCategory.Plus.homologyFunctor (Spec (quotientSpecRing (Ideal.ofList s))).Modules n).obj
        ((closedImmersionRightAdjoint (Spec.map (quotientSpecMap (Ideal.ofList
          s)))).rightDerivedFunctorPlus.obj
          ((DerivedCategory.Plus.singleFunctor (Spec R).Modules 0).obj L)) ≅
      (regularClosedResolutionComplex s J).homology n :=
  ((DerivedCategory.Plus.homologyFunctor (Spec (quotientSpecRing (Ideal.ofList s))).Modules
    n).mapIso
      (J.rightDerivedFunctorPlusIso
        (closedImmersionRightAdjoint (Spec.map (quotientSpecMap (Ideal.ofList s)))))).symm ≪≫
    (DerivedCategory.Plus.homologyFunctorFactors
      (A := (Spec (quotientSpecRing (Ideal.ofList s))).Modules) (n := n)).app
      ((closedImmersionRightAdjoint (Spec.map (quotientSpecMap (Ideal.ofList
        s)))).mapCochainComplexPlus.obj
        J.cochainComplexPlus)

omit [HasExt.{w} (ModuleCat.{u} R)] in
include hs e J in
private theorem regularClosedDerived_isGE :
    ((closedImmersionRightAdjoint (Spec.map (quotientSpecMap (Ideal.ofList
      s)))).rightDerivedFunctorPlus.obj
      ((DerivedCategory.Plus.singleFunctor (Spec R).Modules 0).obj L)).IsGE (s.length : ℤ) := by
  rw [← DerivedCategory.Plus.isGE_ι_obj_iff, DerivedCategory.isGE_iff]
  intro n hn
  exact (regularClosedResolutionHomology_isZero s hs J e n (ne_of_lt hn)).of_iso
    (regularClosedDerivedModelHomologyIso s J n)

omit [HasExt.{w} (ModuleCat.{u} R)] in
include hs e J in
private theorem regularClosedDerived_isLE :
    ((closedImmersionRightAdjoint (Spec.map (quotientSpecMap (Ideal.ofList
      s)))).rightDerivedFunctorPlus.obj
      ((DerivedCategory.Plus.singleFunctor (Spec R).Modules 0).obj L)).IsLE (s.length : ℤ) := by
  rw [← DerivedCategory.Plus.isLE_ι_obj_iff, DerivedCategory.isLE_iff]
  intro n hn
  exact (regularClosedResolutionHomology_isZero s hs J e n (ne_of_gt hn)).of_iso
    (regularClosedDerivedModelHomologyIso s J n)

private def regularClosedDerivedTopHomologyIso :
    (DerivedCategory.Plus.homologyFunctor (Spec (quotientSpecRing (Ideal.ofList s))).Modules
      (s.length : ℤ)).obj
        ((closedImmersionRightAdjoint (Spec.map (quotientSpecMap (Ideal.ofList
          s)))).rightDerivedFunctorPlus.obj
          ((DerivedCategory.Plus.singleFunctor (Spec R).Modules 0).obj L)) ≅
      SheafOfModules.unit (Spec (quotientSpecRing (Ideal.ofList s))).ringCatSheaf :=
  regularClosedDerivedModelHomologyIso s J (s.length : ℤ) ≪≫
    regularClosedResolutionTopHomologyIso s hs J e

private def regularClosedDerivedIso :
    (closedImmersionRightAdjoint (Spec.map (quotientSpecMap (Ideal.ofList
      s)))).rightDerivedFunctorPlus.obj
        ((DerivedCategory.Plus.singleFunctor (Spec R).Modules 0).obj L) ≅
      (DerivedCategory.Plus.singleFunctor (Spec (quotientSpecRing (Ideal.ofList s))).Modules
        (s.length : ℤ)).obj
        (SheafOfModules.unit (Spec (quotientSpecRing (Ideal.ofList s))).ringCatSheaf) := by
  let K := (closedImmersionRightAdjoint (Spec.map (quotientSpecMap (Ideal.ofList
    s)))).rightDerivedFunctorPlus.obj
    ((DerivedCategory.Plus.singleFunctor (Spec R).Modules 0).obj L)
  let := regularClosedDerived_isGE s hs J e
  let := regularClosedDerived_isLE s hs J e
  exact DerivedCategory.Plus.isoSingleHomology K (s.length : ℤ) ≪≫
    (DerivedCategory.Plus.singleFunctor (Spec (quotientSpecRing (Ideal.ofList s))).Modules
      (s.length : ℤ)).mapIso (regularClosedDerivedTopHomologyIso s hs J e)

private theorem regularClosedDerivedIso_homology :
    (DerivedCategory.Plus.homologyFunctor (Spec (quotientSpecRing (Ideal.ofList s))).Modules
        (s.length : ℤ)).map (regularClosedDerivedIso s hs J e).hom ≫
      (DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso
        (C := (Spec (quotientSpecRing (Ideal.ofList s))).Modules) (s.length : ℤ)).hom.app
        (SheafOfModules.unit (Spec (quotientSpecRing (Ideal.ofList s))).ringCatSheaf) =
      (regularClosedDerivedTopHomologyIso s hs J e).hom := by
  let K := (closedImmersionRightAdjoint (Spec.map (quotientSpecMap (Ideal.ofList
    s)))).rightDerivedFunctorPlus.obj
    ((DerivedCategory.Plus.singleFunctor (Spec R).Modules 0).obj L)
  let := regularClosedDerived_isGE s hs J e
  let := regularClosedDerived_isLE s hs J e
  let H := DerivedCategory.Plus.homologyFunctor (Spec (quotientSpecRing (Ideal.ofList s))).Modules
    (s.length : ℤ)
  let S := DerivedCategory.Plus.singleFunctor (Spec (quotientSpecRing (Ideal.ofList s))).Modules
    (s.length : ℤ)
  let E := DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso
    (C := (Spec (quotientSpecRing (Ideal.ofList s))).Modules) (s.length : ℤ)
  let eH := regularClosedDerivedTopHomologyIso s hs J e
  have hn : H.map (DerivedCategory.Plus.isoSingleHomology K (s.length : ℤ)).hom ≫
      E.hom.app (H.obj K) = 𝟙 _ := by
    change (DerivedCategory.homologyFunctor (Spec (quotientSpecRing (Ideal.ofList s))).Modules
      (s.length : ℤ)).map
        ((DerivedCategory.Plus.ι : _ ⥤ DerivedCategory
          (Spec (quotientSpecRing (Ideal.ofList s))).Modules).map
          (DerivedCategory.Plus.isoSingleHomology K (s.length : ℤ)).hom) ≫ _ = _
    rw [DerivedCategory.Plus.ι_map_isoSingleHomology_hom]
    exact DerivedCategory.isoSingleHomology_homology _ (s.length : ℤ)
  change H.map ((DerivedCategory.Plus.isoSingleHomology K (s.length : ℤ)).hom ≫
    S.map eH.hom) ≫ E.hom.app _ = eH.hom
  have he : H.map (S.map eH.hom) ≫ E.hom.app _ =
      E.hom.app (H.obj K) ≫ eH.hom := E.hom.naturality eH.hom
  rw [Functor.map_comp, Category.assoc, he, ← Category.assoc, hn, Category.id_comp]

end InstalledDerived
end AlgebraicGeometry.Scheme.Modules

open CategoryTheory.Abelian HomologicalComplex CochainComplex
namespace AlgebraicGeometry.Scheme.Modules
section ResolutionNaturality
variable {R S : CommRingCat.{u}} (q : R ⟶ S) [IsClosedImmersion (Spec.map q)]
  {L L' : (Spec R).Modules} [L.IsQuasicoherent] [L'.IsQuasicoherent]
  {I : InjectiveResolution L} {J : InjectiveResolution L'} {g : L ⟶ L'}
  (φ : InjectiveResolution.Hom I J g)

private def sectionsResolutionHom :
    InjectiveResolution.Hom (AffineDerived.globalSectionsInjectiveResolution I)
      (AffineDerived.globalSectionsInjectiveResolution J) (moduleSpecΓFunctor.map g) where
  hom := ((moduleSpecΓFunctor (R := R)).mapHomologicalComplex (.up ℕ)).map φ.hom
  ι_f_zero_comp_hom_f_zero := by
    have h := congrArg (moduleSpecΓFunctor (R := R)).map φ.ι_f_zero_comp_hom_f_zero
    simp only [Functor.map_comp, CochainComplex.single₀_map_f_zero] at h
    exact h

private def closedΓResolutionMap :
    closedΓResolutionComplex q I ⟶ closedΓResolutionComplex q J :=
  ((moduleSpecΓFunctor (R := S)).mapHomologicalComplex (.up ℤ)).map
    (((closedImmersionRightAdjoint (Spec.map q)).mapHomologicalComplex (.up ℤ)).map φ.hom')

private theorem closedΓResolutionIso_naturality :
    closedΓResolutionMap q φ ≫ (closedΓResolutionIso q J).hom =
      (closedΓResolutionIso q I).hom ≫
        ((ModuleCat.coextendScalars q.hom).mapHomologicalComplex (.up ℤ)).map
          (sectionsResolutionHom φ).hom' := by
  let C := ModuleCat.coextendScalars q.hom
  let E := Functor.mapHomologicalComplexCompIso (closedImmersionRightAdjointAffineIso q) (.up ℤ) ≪≫
    (Functor.mapHomologicalComplexCompIso
      (Iso.refl (moduleSpecΓFunctor (R := R) ⋙ C)) (.up ℤ)).symm
  let XI := I.cocomplex.mapExtendIso (moduleSpecΓFunctor (R := R)) ComplexShape.embeddingUpNat
  let XJ := J.cocomplex.mapExtendIso (moduleSpecΓFunctor (R := R)) ComplexShape.embeddingUpNat
  have hE := E.hom.naturality φ.hom'
  change closedΓResolutionMap q φ ≫ E.hom.app J.cochainComplex =
    E.hom.app I.cochainComplex ≫ (C.mapHomologicalComplex (.up ℤ)).map
      (((moduleSpecΓFunctor (R := R)).mapHomologicalComplex (.up ℤ)).map φ.hom') at hE
  have hX := I.cocomplex.mapExtendIso_hom_naturality (moduleSpecΓFunctor (R := R))
    ComplexShape.embeddingUpNat φ.hom
  have hX' := congrArg ((C.mapHomologicalComplex (.up ℤ)).map) hX
  simp only [Functor.map_comp] at hX'
  change (C.mapHomologicalComplex (.up ℤ)).map
      (((moduleSpecΓFunctor (R := R)).mapHomologicalComplex (.up ℤ)).map φ.hom') ≫
      (C.mapHomologicalComplex (.up ℤ)).map XJ.hom =
    (C.mapHomologicalComplex (.up ℤ)).map XI.hom ≫
      (C.mapHomologicalComplex (.up ℤ)).map (sectionsResolutionHom φ).hom' at hX'
  change closedΓResolutionMap q φ ≫ E.hom.app J.cochainComplex ≫
      (C.mapHomologicalComplex (.up ℤ)).map XJ.hom =
    E.hom.app I.cochainComplex ≫ (C.mapHomologicalComplex (.up ℤ)).map XI.hom ≫
      (C.mapHomologicalComplex (.up ℤ)).map (sectionsResolutionHom φ).hom'
  calc
    _ = E.hom.app I.cochainComplex ≫
        (C.mapHomologicalComplex (.up ℤ)).map
          (((moduleSpecΓFunctor (R := R)).mapHomologicalComplex (.up ℤ)).map φ.hom') ≫
        (C.mapHomologicalComplex (.up ℤ)).map XJ.hom := by
      simpa only [Category.assoc] using
        congrArg (fun p => p ≫ (C.mapHomologicalComplex (.up ℤ)).map XJ.hom) hE
    _ = _ := by
      simpa only [Category.assoc] using
        congrArg (fun p => E.hom.app I.cochainComplex ≫ p) hX'

variable [HasExt.{w} (ModuleCat.{u} R)]

private theorem closedΓResolutionExtAddEquiv_naturality (n : ℕ)
    (x : (closedΓResolutionComplex q I).homology (n : ℤ)) :
    closedΓResolutionExtAddEquiv q J n
        (homologyMap (closedΓResolutionMap q φ) (n : ℤ) x) =
      (closedΓResolutionExtAddEquiv q I n x).comp
        (Ext.mk₀ (moduleSpecΓFunctor.map g)) (Nat.add_zero n) := by
  have h := congrArg
    ((homologyFunctor (ModuleCat.{u} S) (.up ℤ) (n : ℤ)).map)
    (closedΓResolutionIso_naturality q φ)
  simp only [Functor.map_comp] at h
  have hh := ConcreteCategory.congr_hom h x
  change homologyMap (closedΓResolutionIso q J).hom (n : ℤ)
      (homologyMap (closedΓResolutionMap q φ) (n : ℤ) x) =
    homologyMap
      (((ModuleCat.coextendScalars q.hom).mapHomologicalComplex (.up ℤ)).map
        (sectionsResolutionHom φ).hom') (n : ℤ)
      (homologyMap (closedΓResolutionIso q I).hom (n : ℤ) x) at hh
  change ModuleCat.coextendScalarsResolutionExtAddEquiv q.hom
    (AffineDerived.globalSectionsInjectiveResolution J) n
      (homologyMap (closedΓResolutionIso q J).hom (n : ℤ)
        (homologyMap (closedΓResolutionMap q φ) (n : ℤ) x)) = _
  rw [hh]
  exact ModuleCat.coextendScalarsResolutionExtAddEquiv_naturality q.hom
    (sectionsResolutionHom φ) n (homologyMap (closedΓResolutionIso q I).hom (n : ℤ) x)

end ResolutionNaturality
end AlgebraicGeometry.Scheme.Modules

open CategoryTheory.Abelian HomologicalComplex CochainComplex
namespace AlgebraicGeometry.Scheme.Modules
section ActualCounitNaturality
variable (B : CommRingCat.{u})
local instance : (moduleSpecΓFunctor (R := B)).Additive := moduleSpecΓFunctor_additive B
local instance : PreservesFiniteLimits (tilde.functor B) := tilde_preservesFiniteLimits B
local instance : (tilde.functor B).Additive :=
  CategoryTheory.Functor.additive_of_preserves_binary_products _

private theorem actualTildeHomologyIso_naturality
    {K K' : CochainComplex (Spec B).Modules ℤ}
    [QuasiIso (Complex.tildeGlobalSectionsCounit B (.up ℤ) K)]
    [QuasiIso (Complex.tildeGlobalSectionsCounit B (.up ℤ) K')]
    (ψ : K ⟶ K') (n : ℤ) :
    (tilde.functor B).map
        (homologyMap (((moduleSpecΓFunctor (R := B)).mapHomologicalComplex (.up ℤ)).map ψ) n) ≫
        (Complex.tildeGlobalSectionsHomologyIso B (.up ℤ) K' n).hom =
      (Complex.tildeGlobalSectionsHomologyIso B (.up ℤ) K n).hom ≫ homologyMap ψ n := by
  let G := moduleSpecΓFunctor (R := B)
  let T := tilde.functor B
  let C := (G.mapHomologicalComplex (.up ℤ)).obj K
  let D := (G.mapHomologicalComplex (.up ℤ)).obj K'
  let u := (G.mapHomologicalComplex (.up ℤ)).map ψ
  let v := (T.mapHomologicalComplex (.up ℤ)).map u
  have ht := ShortComplex.mapHomologyIso_inv_naturality
    ((shortComplexFunctor (ModuleCat.{u} B) (.up ℤ) n).map u) T
  change T.map (homologyMap u n) ≫ ((D.sc n).mapHomologyIso T).inv =
    ((C.sc n).mapHomologyIso T).inv ≫ homologyMap v n at ht
  have hc := congrArg
    ((homologyFunctor (Spec B).Modules (.up ℤ) n).map)
    (Complex.tildeGlobalSectionsCounit_naturality B (.up ℤ) ψ)
  simp only [Functor.map_comp] at hc
  change homologyMap v n ≫ homologyMap (Complex.tildeGlobalSectionsCounit B (.up ℤ) K') n =
    homologyMap (Complex.tildeGlobalSectionsCounit B (.up ℤ) K) n ≫ homologyMap ψ n at hc
  change T.map (homologyMap u n) ≫ ((D.sc n).mapHomologyIso T).inv ≫
      homologyMap (Complex.tildeGlobalSectionsCounit B (.up ℤ) K') n =
    ((C.sc n).mapHomologyIso T).inv ≫
      homologyMap (Complex.tildeGlobalSectionsCounit B (.up ℤ) K) n ≫ homologyMap ψ n
  rw [← Category.assoc, ht, Category.assoc, hc]

end ActualCounitNaturality
end AlgebraicGeometry.Scheme.Modules

open CategoryTheory.Abelian HomologicalComplex CochainComplex
namespace AlgebraicGeometry.Scheme.Modules
section ResolutionIndependence
variable {R : CommRingCat.{u}} [HasExt.{w} (ModuleCat.{u} R)]
  (s : List R) (hs : RingTheory.Sequence.IsWeaklyRegular R s)
  {L : (Spec R).Modules} [L.IsQuasicoherent]
  {I J : InjectiveResolution L}
  (e : (moduleSpecΓFunctor (R := R)).obj L ≅ ModuleCat.of R R)
  (φ : InjectiveResolution.Hom I J (𝟙 L))

private theorem regularClosedTopSectionsLinearEquiv_naturality
    (x : (closedΓResolutionComplex (quotientSpecMap (Ideal.ofList s)) I).homology (s.length : ℤ)) :
    regularClosedTopSectionsLinearEquiv s hs J e
        (homologyMap (closedΓResolutionMap (quotientSpecMap (Ideal.ofList s)) φ) (s.length : ℤ) x) =
      regularClosedTopSectionsLinearEquiv s hs I e x := by
  let E_I := closedImmersionRightAdjointRegularListResolutionSectionsExtAddEquiv s I s.length
  let E_J := closedImmersionRightAdjointRegularListResolutionSectionsExtAddEquiv s J s.length
  let P_I := regularClosedTopSectionsLinearEquiv s hs I e
  let P_J := regularClosedTopSectionsLinearEquiv s hs J e
  have h : E_J (homologyMap (closedΓResolutionMap (quotientSpecMap (Ideal.ofList s)) φ)
      (s.length : ℤ) x) = E_I x := by
    have hh := closedΓResolutionExtAddEquiv_naturality
      (quotientSpecMap (Ideal.ofList s)) φ s.length x
    simp only [CategoryTheory.Functor.map_id, Ext.comp_mk₀_id] at hh
    dsimp only [E_I, E_J]
    rw [closedImmersionRightAdjointRegularListResolutionSectionsExtAddEquiv_eq_affine,
      closedImmersionRightAdjointRegularListResolutionSectionsExtAddEquiv_eq_affine]
    convert! hh using 1
  apply P_J.symm.injective
  change P_J.symm (P_J (homologyMap
      (closedΓResolutionMap (quotientSpecMap (Ideal.ofList s)) φ) (s.length : ℤ) x)) =
    P_J.symm (P_I x)
  rw [P_J.symm_apply_apply]
  obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (P_I x)
  rw [← hr]
  apply E_J.injective
  calc
    _ = E_I x := h
    _ = E_I (P_I.symm (Ideal.Quotient.mk (Ideal.ofList s) r)) := by
      rw [hr, P_I.symm_apply_apply]
    _ = (ChainComplex.Koszul.topExtClass s hs (ModuleCat.of R R) r).comp
        (Ext.mk₀ e.inv) (Nat.add_zero s.length) :=
      by simpa only [E_I, E_J, P_I, P_J, regularClosedTopSectionsLinearEquiv] using
        closedImmersionRightAdjointRegularListResolutionTopSectionsLinearEquiv_class s hs I e r
    _ = E_J (P_J.symm (Ideal.Quotient.mk (Ideal.ofList s) r)) :=
      by simpa only [E_I, E_J, P_I, P_J, regularClosedTopSectionsLinearEquiv] using
        (closedImmersionRightAdjointRegularListResolutionTopSectionsLinearEquiv_class s hs J e
          r).symm

private theorem regularClosedTopSectionsLinearEquiv_naturality_hom :
    homologyMap (closedΓResolutionMap (quotientSpecMap (Ideal.ofList s)) φ) (s.length : ℤ) ≫
        (regularClosedTopSectionsLinearEquiv s hs J e).toModuleIso.hom =
      (regularClosedTopSectionsLinearEquiv s hs I e).toModuleIso.hom := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact regularClosedTopSectionsLinearEquiv_naturality s hs e φ x

private theorem regularClosedResolutionTopHomologyIso_naturality :
    homologyMap
        (((closedImmersionRightAdjoint (Spec.map (quotientSpecMap (Ideal.ofList
          s)))).mapHomologicalComplex
          (.up ℤ)).map φ.hom') (s.length : ℤ) ≫
        (regularClosedResolutionTopHomologyIso s hs J e).hom =
      (regularClosedResolutionTopHomologyIso s hs I e).hom := by
  let S := quotientSpecRing (Ideal.ofList s)
  let : QuasiIso (Complex.tildeGlobalSectionsCounit S (.up ℤ)
    (regularClosedResolutionComplex s I)) := regularClosedResolutionTildeCounit_quasiIso s hs I e
  let : QuasiIso (Complex.tildeGlobalSectionsCounit S (.up ℤ)
    (regularClosedResolutionComplex s J)) := regularClosedResolutionTildeCounit_quasiIso s hs J e
  let ψ : regularClosedResolutionComplex s I ⟶ regularClosedResolutionComplex s J :=
    ((closedImmersionRightAdjoint (Spec.map (quotientSpecMap (Ideal.ofList
      s)))).mapHomologicalComplex
      (.up ℤ)).map φ.hom'
  let cI := Complex.tildeGlobalSectionsHomologyIso S (.up ℤ)
    (regularClosedResolutionComplex s I) (s.length : ℤ)
  let cJ := Complex.tildeGlobalSectionsHomologyIso S (.up ℤ)
    (regularClosedResolutionComplex s J) (s.length : ℤ)
  have hc := actualTildeHomologyIso_naturality S ψ (s.length : ℤ)
  change (tilde.functor S).map
      (homologyMap (closedΓResolutionMap (quotientSpecMap (Ideal.ofList s)) φ) (s.length : ℤ)) ≫
      cJ.hom = cI.hom ≫ homologyMap ψ (s.length : ℤ) at hc
  have ht := congrArg (tilde.functor S).map
    (regularClosedTopSectionsLinearEquiv_naturality_hom s hs e φ)
  simp only [Functor.map_comp] at ht
  apply (cancel_epi cI.hom).mp
  dsimp only [regularClosedResolutionTopHomologyIso]
  rw [closedImmersionRightAdjointRegularListResolutionTopHomologyIso_hom s hs J e,
    closedImmersionRightAdjointRegularListResolutionTopHomologyIso_hom s hs I e]
  change cI.hom ≫ homologyMap ψ (s.length : ℤ) ≫ cJ.inv ≫
      (tilde.functor S).map (regularClosedTopSectionsLinearEquiv s hs J e).toModuleIso.hom ≫
      (tildeSelf (R := S)).hom =
    cI.hom ≫ cI.inv ≫
      (tilde.functor S).map (regularClosedTopSectionsLinearEquiv s hs I e).toModuleIso.hom ≫
      (tildeSelf (R := S)).hom
  have hleft := congrArg (fun p => p ≫ cJ.inv ≫
    (tilde.functor S).map (regularClosedTopSectionsLinearEquiv s hs J e).toModuleIso.hom ≫
      (tildeSelf (R := S)).hom) hc.symm
  have hright := congrArg (fun p => p ≫ (tildeSelf (R := S)).hom) ht
  have hleft' := hleft
  simp only [Category.assoc, Iso.hom_inv_id_assoc] at hleft'
  simpa only [Category.assoc, Iso.hom_inv_id_assoc] using
    hleft'.trans (by simpa only [Category.assoc] using hright)

variable [HasDerivedCategory.{a} (Spec R).Modules]
  [HasDerivedCategory.{b} (Spec (quotientSpecRing (Ideal.ofList s))).Modules]

omit [HasExt.{w} (ModuleCat.{u} R)] [L.IsQuasicoherent] in
private theorem regularClosedDerivedModelHomologyIso_naturality (n : ℤ) :
    (regularClosedDerivedModelHomologyIso s I n).hom ≫
        homologyMap
          (((closedImmersionRightAdjoint (Spec.map (quotientSpecMap (Ideal.ofList
            s)))).mapHomologicalComplex
            (.up ℤ)).map φ.hom') n =
      (regularClosedDerivedModelHomologyIso s J n).hom := by
  let F := closedImmersionRightAdjoint (Spec.map (quotientSpecMap (Ideal.ofList s)))
  let H := DerivedCategory.Plus.homologyFunctor (Spec (quotientSpecRing (Ideal.ofList s))).Modules n
  let p := DerivedCategory.Plus.Q.map (F.mapCochainComplexPlus.map φ.mapPlus)
  let eI := H.mapIso (I.rightDerivedFunctorPlusIso F)
  let eJ := H.mapIso (J.rightDerivedFunctorPlusIso F)
  let PI := (DerivedCategory.Plus.homologyFunctorFactors
    (A := (Spec (quotientSpecRing (Ideal.ofList s))).Modules) (n := n)).app
      (F.mapCochainComplexPlus.obj I.cochainComplexPlus)
  let PJ := (DerivedCategory.Plus.homologyFunctorFactors
    (A := (Spec (quotientSpecRing (Ideal.ofList s))).Modules) (n := n)).app
      (F.mapCochainComplexPlus.obj J.cochainComplexPlus)
  have hR := congrArg H.map (I.rightDerivedFunctorPlusIso_naturality F φ)
  simp only [Functor.map_comp, CategoryTheory.Functor.map_id, Category.comp_id] at hR
  change H.map p ≫ eJ.hom = eI.hom at hR
  have hP := (DerivedCategory.Plus.homologyFunctorFactors
    (A := (Spec (quotientSpecRing (Ideal.ofList s))).Modules) (n := n)).hom.naturality
      (F.mapCochainComplexPlus.map φ.mapPlus)
  change H.map p ≫ PJ.hom = PI.hom ≫
    homologyMap ((F.mapHomologicalComplex (.up ℤ)).map φ.hom') n at hP
  have hIJ : eI.inv ≫ H.map p = eJ.inv := by
    apply (cancel_mono eJ.hom).mp
    rw [Category.assoc, hR, Iso.inv_hom_id, Iso.inv_hom_id]
  change eI.inv ≫ PI.hom ≫
      homologyMap ((F.mapHomologicalComplex (.up ℤ)).map φ.hom') n = eJ.inv ≫ PJ.hom
  rw [← hP, ← Category.assoc, hIJ]

private theorem regularClosedDerivedTopHomologyIso_independent
    (I J : InjectiveResolution L) :
    regularClosedDerivedTopHomologyIso s hs I e = regularClosedDerivedTopHomologyIso s hs J e := by
  let φ : InjectiveResolution.Hom I J (𝟙 L) :=
    ⟨InjectiveResolution.desc (𝟙 L) J I, by
      simpa only [CochainComplex.single₀_map_f_zero] using
        InjectiveResolution.desc_commutes_zero (𝟙 L) J I⟩
  apply Iso.ext
  change (regularClosedDerivedModelHomologyIso s I (s.length : ℤ)).hom ≫
      (regularClosedResolutionTopHomologyIso s hs I e).hom =
    (regularClosedDerivedModelHomologyIso s J (s.length : ℤ)).hom ≫
      (regularClosedResolutionTopHomologyIso s hs J e).hom
  rw [← regularClosedResolutionTopHomologyIso_naturality s hs e φ,
    ← Category.assoc, regularClosedDerivedModelHomologyIso_naturality s φ]

private theorem regularClosedDerivedIso_independent (I J : InjectiveResolution L) :
    regularClosedDerivedIso s hs I e = regularClosedDerivedIso s hs J e := by
  dsimp only [regularClosedDerivedIso]
  rw [regularClosedDerivedTopHomologyIso_independent s hs e I J]

end ResolutionIndependence
end AlgebraicGeometry.Scheme.Modules

public section
namespace AlgebraicGeometry.Scheme.Modules
section PublicDerived
variable {R : CommRingCat.{u}} (s : List R) {L : (Spec R).Modules}
  [HasDerivedCategory.{a} (Spec R).Modules]
  [HasDerivedCategory.{b} (Spec (.of (R ⧸ Ideal.ofList s))).Modules]

/-- Original installed resolution unit and native localization/homology factorization. -/
def derivedClosedImmersionRightAdjointRegularListModelHomologyIso
    (J : InjectiveResolution L) (n : ℤ) :
    (DerivedCategory.Plus.homologyFunctor (Spec (.of (R ⧸ Ideal.ofList s))).Modules n).obj
        ((closedImmersionRightAdjoint (Spec.map (CommRingCat.ofHom
          (Ideal.Quotient.mk (Ideal.ofList s))))).rightDerivedFunctorPlus.obj
          ((DerivedCategory.Plus.singleFunctor (Spec R).Modules 0).obj L)) ≅
      (closedImmersionRightAdjointRegularListResolutionComplex s J).homology n :=
  regularClosedDerivedModelHomologyIso s J n

variable [HasExt.{w} (ModuleCat.{u} R)] [L.IsQuasicoherent]

/-- The top homology sheaf of the actual installed Ri! has its original ordered quotient frame. -/
def derivedClosedImmersionRightAdjointRegularListTopHomologyIso
    (hs : RingTheory.Sequence.IsWeaklyRegular R s) (J : InjectiveResolution L)
    (e : moduleSpecΓFunctor.obj L ≅ ModuleCat.of R R) :
    (DerivedCategory.Plus.homologyFunctor (Spec (.of (R ⧸ Ideal.ofList s))).Modules
      (s.length : ℤ)).obj
        ((closedImmersionRightAdjoint (Spec.map (CommRingCat.ofHom
          (Ideal.Quotient.mk (Ideal.ofList s))))).rightDerivedFunctorPlus.obj
          ((DerivedCategory.Plus.singleFunctor (Spec R).Modules 0).obj L)) ≅
      SheafOfModules.unit (Spec (.of (R ⧸ Ideal.ofList s))).ringCatSheaf :=
  regularClosedDerivedTopHomologyIso s hs J e

/-- Actual affine sheaf purity, normalized by the original ordered Koszul class.

Both derived-category sizes and the supported Ext size are independent. The coefficient is
quasicoherent with the supplied original sections frame; no Noetherian or flatness premise is
  used. -/
def derivedClosedImmersionRightAdjointRegularListIso
    (hs : RingTheory.Sequence.IsWeaklyRegular R s) (J : InjectiveResolution L)
    (e : moduleSpecΓFunctor.obj L ≅ ModuleCat.of R R) :
    (closedImmersionRightAdjoint (Spec.map (CommRingCat.ofHom
        (Ideal.Quotient.mk (Ideal.ofList s))))).rightDerivedFunctorPlus.obj
        ((DerivedCategory.Plus.singleFunctor (Spec R).Modules 0).obj L) ≅
      (DerivedCategory.Plus.singleFunctor (Spec (.of (R ⧸ Ideal.ofList s))).Modules
        (s.length : ℤ)).obj
        (SheafOfModules.unit (Spec (.of (R ⧸ Ideal.ofList s))).ringCatSheaf) :=
  regularClosedDerivedIso s hs J e

end PublicDerived
section PrivatePublicModelFormula
variable {R : CommRingCat.{u}} (s : List R) {L : (Spec R).Modules}
  [HasDerivedCategory.{a} (Spec R).Modules]
  [HasDerivedCategory.{b} (Spec (.of (R ⧸ Ideal.ofList s))).Modules]
private theorem derivedClosedImmersionRightAdjointRegularListModelHomologyIso_hom_aux
    (J : InjectiveResolution L) (n : ℤ) :
    (derivedClosedImmersionRightAdjointRegularListModelHomologyIso s J n).hom =
      (DerivedCategory.Plus.homologyFunctor (Spec (.of (R ⧸ Ideal.ofList s))).Modules n).map
          (J.rightDerivedFunctorPlusIso (closedImmersionRightAdjoint (Spec.map
            (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.ofList s)))))).inv ≫
        (DerivedCategory.Plus.homologyFunctorFactors
          (A := (Spec (.of (R ⧸ Ideal.ofList s))).Modules) (n := n)).hom.app
          ((closedImmersionRightAdjoint (Spec.map (CommRingCat.ofHom
            (Ideal.Quotient.mk (Ideal.ofList s))))).mapCochainComplexPlus.obj
              J.cochainComplexPlus) := rfl
end PrivatePublicModelFormula
section PrivatePublicTopFormula
variable {R : CommRingCat.{u}} (s : List R) {L : (Spec R).Modules} [L.IsQuasicoherent]
  [HasExt.{w} (ModuleCat.{u} R)]
  [HasDerivedCategory.{a} (Spec R).Modules]
  [HasDerivedCategory.{b} (Spec (.of (R ⧸ Ideal.ofList s))).Modules]
private theorem derivedClosedImmersionRightAdjointRegularListTopHomologyIso_hom_aux
    (hs : RingTheory.Sequence.IsWeaklyRegular R s) (J : InjectiveResolution L)
    (e : moduleSpecΓFunctor.obj L ≅ ModuleCat.of R R) :
    (derivedClosedImmersionRightAdjointRegularListTopHomologyIso s hs J e).hom =
      (derivedClosedImmersionRightAdjointRegularListModelHomologyIso s J (s.length : ℤ)).hom ≫
        (closedImmersionRightAdjointRegularListResolutionTopHomologyIso s hs J e).hom := rfl
end PrivatePublicTopFormula
end AlgebraicGeometry.Scheme.Modules
@[expose] public section
namespace AlgebraicGeometry.Scheme.Modules
section PublicDerivedLaws
variable {R : CommRingCat.{u}} (s : List R) {L : (Spec R).Modules} [L.IsQuasicoherent]
  [HasDerivedCategory.{a} (Spec R).Modules]
  [HasDerivedCategory.{b} (Spec (.of (R ⧸ Ideal.ofList s))).Modules]

omit [L.IsQuasicoherent] in
/-- The model homology map retains the installed original resolution unit and native
  factorization. -/
theorem derivedClosedImmersionRightAdjointRegularListModelHomologyIso_hom
    (J : InjectiveResolution L) (n : ℤ) :
    (derivedClosedImmersionRightAdjointRegularListModelHomologyIso s J n).hom =
      (DerivedCategory.Plus.homologyFunctor (Spec (.of (R ⧸ Ideal.ofList s))).Modules n).map
          (J.rightDerivedFunctorPlusIso (closedImmersionRightAdjoint (Spec.map
            (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.ofList s)))))).inv ≫
        (DerivedCategory.Plus.homologyFunctorFactors
          (A := (Spec (.of (R ⧸ Ideal.ofList s))).Modules) (n := n)).hom.app
          ((closedImmersionRightAdjoint (Spec.map (CommRingCat.ofHom
            (Ideal.Quotient.mk (Ideal.ofList s))))).mapCochainComplexPlus.obj
              J.cochainComplexPlus) :=
  derivedClosedImmersionRightAdjointRegularListModelHomologyIso_hom_aux s J n

/-- The actual installed Ri! has the lower list-length cohomological bound. -/
theorem derivedClosedImmersionRightAdjointRegularList_isGE
    (hs : RingTheory.Sequence.IsWeaklyRegular R s) (J : InjectiveResolution L)
    (e : moduleSpecΓFunctor.obj L ≅ ModuleCat.of R R) :
    ((closedImmersionRightAdjoint (Spec.map (CommRingCat.ofHom
      (Ideal.Quotient.mk (Ideal.ofList s))))).rightDerivedFunctorPlus.obj
      ((DerivedCategory.Plus.singleFunctor (Spec R).Modules 0).obj L)).IsGE (s.length : ℤ) :=
  regularClosedDerived_isGE s hs J e

/-- The actual installed Ri! has the upper list-length cohomological bound. -/
theorem derivedClosedImmersionRightAdjointRegularList_isLE
    (hs : RingTheory.Sequence.IsWeaklyRegular R s) (J : InjectiveResolution L)
    (e : moduleSpecΓFunctor.obj L ≅ ModuleCat.of R R) :
    ((closedImmersionRightAdjoint (Spec.map (CommRingCat.ofHom
      (Ideal.Quotient.mk (Ideal.ofList s))))).rightDerivedFunctorPlus.obj
      ((DerivedCategory.Plus.singleFunctor (Spec R).Modules 0).obj L)).IsLE (s.length : ℤ) :=
  regularClosedDerived_isLE s hs J e

variable [HasExt.{w} (ModuleCat.{u} R)]

/-- The installed top frame uses the original model homology and original counit-normalized frame.
-/
theorem derivedClosedImmersionRightAdjointRegularListTopHomologyIso_hom
    (hs : RingTheory.Sequence.IsWeaklyRegular R s) (J : InjectiveResolution L)
    (e : moduleSpecΓFunctor.obj L ≅ ModuleCat.of R R) :
    (derivedClosedImmersionRightAdjointRegularListTopHomologyIso s hs J e).hom =
      (derivedClosedImmersionRightAdjointRegularListModelHomologyIso s J (s.length : ℤ)).hom ≫
        (closedImmersionRightAdjointRegularListResolutionTopHomologyIso s hs J e).hom :=
  derivedClosedImmersionRightAdjointRegularListTopHomologyIso_hom_aux s hs J e

/-- The installed purity map retains exactly the original single-homology normalization. -/
theorem derivedClosedImmersionRightAdjointRegularListIso_homology
    (hs : RingTheory.Sequence.IsWeaklyRegular R s) (J : InjectiveResolution L)
    (e : moduleSpecΓFunctor.obj L ≅ ModuleCat.of R R) :
    (DerivedCategory.Plus.homologyFunctor (Spec (.of (R ⧸ Ideal.ofList s))).Modules
        (s.length : ℤ)).map (derivedClosedImmersionRightAdjointRegularListIso s hs J e).hom ≫
      (DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso
        (C := (Spec (.of (R ⧸ Ideal.ofList s))).Modules) (s.length : ℤ)).hom.app
        (SheafOfModules.unit (Spec (.of (R ⧸ Ideal.ofList s))).ringCatSheaf) =
      (derivedClosedImmersionRightAdjointRegularListTopHomologyIso s hs J e).hom :=
  regularClosedDerivedIso_homology s hs J e

/-- The installed purity isomorphism is independent of the supplied original sheaf resolution. -/
theorem derivedClosedImmersionRightAdjointRegularListIso_independent
    (hs : RingTheory.Sequence.IsWeaklyRegular R s) (I J : InjectiveResolution L)
    (e : moduleSpecΓFunctor.obj L ≅ ModuleCat.of R R) :
    derivedClosedImmersionRightAdjointRegularListIso s hs I e =
      derivedClosedImmersionRightAdjointRegularListIso s hs J e :=
  regularClosedDerivedIso_independent s hs e I J

end PublicDerivedLaws
end AlgebraicGeometry.Scheme.Modules
