/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Canonical.LocalModel
public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Canonical.Model.Naturality

/-!
# Coefficient transport on the original regular-list model

An actual lift between the supplied coefficient resolutions gives native
Yoneda postcomposition. Compatible coefficient frames therefore give the
same quotient coordinate under the original ordered top class. This keeps
the coefficient restriction isomorphism in common-resolution refinements.
-/

@[expose] public section
noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Abelian AlgebraicGeometry HomologicalComplex

universe u w
namespace AlgebraicGeometry.Scheme.Modules

section AffineNaturality
variable {A B : CommRingCat.{u}} (σ : A ⟶ B) [IsClosedImmersion (Spec.map σ)]
  {L N : (Spec A).Modules} [L.IsQuasicoherent] [N.IsQuasicoherent]
  {I : InjectiveResolution L} {J : InjectiveResolution N} {f : L ⟶ N}
  (φ : InjectiveResolution.Hom I J f)

/-- The actual coefficient lift on the original affine sections resolution. -/
def canonicalSectionsResolutionLift :
    InjectiveResolution.Hom (AffineDerived.globalSectionsInjectiveResolution I)
      (AffineDerived.globalSectionsInjectiveResolution J) (moduleSpecΓFunctor.map f) where
  hom := ((moduleSpecΓFunctor (R := A)).mapHomologicalComplex (.up ℕ)).map φ.hom
  ι_f_zero_comp_hom_f_zero := by
    have h := congrArg (moduleSpecΓFunctor (R := A)).map φ.ι_f_zero_comp_hom_f_zero
    simp only [Functor.map_comp, CochainComplex.single₀_map_f_zero] at h
    exact h

/-- Original affine coinduction and retained-degree extension commute with the same lift. -/
theorem canonicalAffineResolutionSectionsIso_naturality :
    ((moduleSpecΓFunctor (R := B)).mapHomologicalComplex (.up ℤ)).map
        (((closedImmersionRightAdjoint (Spec.map σ)).mapHomologicalComplex (.up ℤ)).map
          φ.hom') ≫ (affineClosedRightAdjointResolutionSectionsIso σ J).hom =
      (affineClosedRightAdjointResolutionSectionsIso σ I).hom ≫
        ((ModuleCat.coextendScalars σ.hom).mapHomologicalComplex (.up ℤ)).map
          (canonicalSectionsResolutionLift φ).hom' := by
  let C := ModuleCat.coextendScalars σ.hom
  let E := Functor.mapHomologicalComplexCompIso (closedImmersionRightAdjointAffineIso σ)
      (.up ℤ) ≪≫
    (Functor.mapHomologicalComplexCompIso
      (Iso.refl (moduleSpecΓFunctor (R := A) ⋙ C)) (.up ℤ)).symm
  let XI := I.cocomplex.mapExtendIso (moduleSpecΓFunctor (R := A)) ComplexShape.embeddingUpNat
  let XJ := J.cocomplex.mapExtendIso (moduleSpecΓFunctor (R := A)) ComplexShape.embeddingUpNat
  let ψ := ((moduleSpecΓFunctor (R := B)).mapHomologicalComplex (.up ℤ)).map
    (((closedImmersionRightAdjoint (Spec.map σ)).mapHomologicalComplex (.up ℤ)).map φ.hom')
  have hE := E.hom.naturality φ.hom'
  change ψ ≫ E.hom.app J.cochainComplex = E.hom.app I.cochainComplex ≫
    (C.mapHomologicalComplex (.up ℤ)).map
      (((moduleSpecΓFunctor (R := A)).mapHomologicalComplex (.up ℤ)).map φ.hom') at hE
  have hX := I.cocomplex.mapExtendIso_hom_naturality (moduleSpecΓFunctor (R := A))
    ComplexShape.embeddingUpNat φ.hom
  have hX' := congrArg ((C.mapHomologicalComplex (.up ℤ)).map) hX
  simp only [Functor.map_comp] at hX'
  change (C.mapHomologicalComplex (.up ℤ)).map
      (((moduleSpecΓFunctor (R := A)).mapHomologicalComplex (.up ℤ)).map φ.hom') ≫
      (C.mapHomologicalComplex (.up ℤ)).map XJ.hom =
    (C.mapHomologicalComplex (.up ℤ)).map XI.hom ≫
      (C.mapHomologicalComplex (.up ℤ)).map (canonicalSectionsResolutionLift φ).hom' at hX'
  change ψ ≫ E.hom.app J.cochainComplex ≫
      (C.mapHomologicalComplex (.up ℤ)).map XJ.hom =
    E.hom.app I.cochainComplex ≫ (C.mapHomologicalComplex (.up ℤ)).map XI.hom ≫
      (C.mapHomologicalComplex (.up ℤ)).map (canonicalSectionsResolutionLift φ).hom'
  calc
    _ = E.hom.app I.cochainComplex ≫
        (C.mapHomologicalComplex (.up ℤ)).map
          (((moduleSpecΓFunctor (R := A)).mapHomologicalComplex (.up ℤ)).map φ.hom') ≫
        (C.mapHomologicalComplex (.up ℤ)).map XJ.hom := by
      simpa only [Category.assoc] using congrArg (fun z =>
        z ≫ (C.mapHomologicalComplex (.up ℤ)).map XJ.hom) hE
    _ = _ := by
      simpa only [Category.assoc] using congrArg (fun z =>
        E.hom.app I.cochainComplex ≫ z) hX'

variable [HasExt.{w} (ModuleCat.{u} A)]

/-- The actual affine model lift is native postcomposition in the coefficient. -/
theorem canonicalAffineResolutionExt_naturality (n : ℕ)
    (x : (((moduleSpecΓFunctor (R := B)).mapHomologicalComplex (.up ℤ)).obj
      (((closedImmersionRightAdjoint (Spec.map σ)).mapHomologicalComplex (.up ℤ)).obj
        I.cochainComplex)).homology (n : ℤ)) :
    affineClosedRightAdjointResolutionExtAddEquiv σ J n
        (homologyMap (((moduleSpecΓFunctor (R := B)).mapHomologicalComplex (.up ℤ)).map
          (((closedImmersionRightAdjoint (Spec.map σ)).mapHomologicalComplex (.up ℤ)).map
            φ.hom')) (n : ℤ) x) =
      (affineClosedRightAdjointResolutionExtAddEquiv σ I n x).comp
        (Ext.mk₀ (moduleSpecΓFunctor.map f)) (add_zero n) := by
  have h := congrArg ((homologyFunctor (ModuleCat.{u} B) (.up ℤ) (n : ℤ)).map)
    (canonicalAffineResolutionSectionsIso_naturality σ φ)
  simp only [Functor.map_comp] at h
  have hh := ConcreteCategory.congr_hom h x
  change homologyMap (affineClosedRightAdjointResolutionSectionsIso σ J).hom (n : ℤ)
      (homologyMap (((moduleSpecΓFunctor (R := B)).mapHomologicalComplex (.up ℤ)).map
        (((closedImmersionRightAdjoint (Spec.map σ)).mapHomologicalComplex (.up ℤ)).map
          φ.hom')) (n : ℤ) x) =
    homologyMap (((ModuleCat.coextendScalars σ.hom).mapHomologicalComplex (.up ℤ)).map
      (canonicalSectionsResolutionLift φ).hom') (n : ℤ)
      (homologyMap (affineClosedRightAdjointResolutionSectionsIso σ I).hom (n : ℤ) x) at hh
  change ModuleCat.coextendScalarsResolutionExtAddEquiv σ.hom
    (AffineDerived.globalSectionsInjectiveResolution J) n
      (homologyMap (affineClosedRightAdjointResolutionSectionsIso σ J).hom (n : ℤ)
        (homologyMap (((moduleSpecΓFunctor (R := B)).mapHomologicalComplex (.up ℤ)).map
          (((closedImmersionRightAdjoint (Spec.map σ)).mapHomologicalComplex (.up ℤ)).map
            φ.hom')) (n : ℤ) x)) = _
  rw [hh]
  exact ModuleCat.coextendScalarsResolutionExtAddEquiv_naturality σ.hom
    (canonicalSectionsResolutionLift φ) n
    (homologyMap (affineClosedRightAdjointResolutionSectionsIso σ I).hom (n : ℤ) x)

end AffineNaturality

section TildeNaturality
variable (B : CommRingCat.{u})
local instance : (moduleSpecΓFunctor (R := B)).Additive := moduleSpecΓFunctor_additive B
local instance : CategoryTheory.Limits.PreservesFiniteLimits (tilde.functor B) :=
  tilde_preservesFiniteLimits B
local instance : (tilde.functor B).Additive :=
  CategoryTheory.Functor.additive_of_preserves_binary_products _

private theorem canonicalTildeHomologyIso_naturality
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
  have hc := congrArg ((homologyFunctor (Spec B).Modules (.up ℤ) n).map)
    (Complex.tildeGlobalSectionsCounit_naturality B (.up ℤ) ψ)
  simp only [Functor.map_comp] at hc
  change homologyMap v n ≫ homologyMap (Complex.tildeGlobalSectionsCounit B (.up ℤ) K') n =
    homologyMap (Complex.tildeGlobalSectionsCounit B (.up ℤ) K) n ≫ homologyMap ψ n at hc
  change T.map (homologyMap u n) ≫ ((D.sc n).mapHomologyIso T).inv ≫
      homologyMap (Complex.tildeGlobalSectionsCounit B (.up ℤ) K') n =
    ((C.sc n).mapHomologyIso T).inv ≫
      homologyMap (Complex.tildeGlobalSectionsCounit B (.up ℤ) K) n ≫ homologyMap ψ n
  rw [← Category.assoc, ht, Category.assoc, hc]

end TildeNaturality

section RegularList
variable {A : CommRingCat.{u}} [HasExt.{w} (ModuleCat.{u} A)]
  (s : List A) (hs : RingTheory.Sequence.IsWeaklyRegular A s)
  {L N : (Spec A).Modules} [L.IsQuasicoherent] [N.IsQuasicoherent]
  {I : InjectiveResolution L} {J : InjectiveResolution N} {f : L ⟶ N}
  (φ : InjectiveResolution.Hom I J f)
  (eL : moduleSpecΓFunctor.obj L ≅ ModuleCat.of A A)
  (eN : moduleSpecΓFunctor.obj N ≅ ModuleCat.of A A)
  (he : eL.inv ≫ moduleSpecΓFunctor.map f = eN.inv)

local instance : (moduleSpecΓFunctor (R := regularListQuotientRing s)).Additive :=
  moduleSpecΓFunctor_additive _

include he in
/-- Compatible original coefficient frames retain the same actual quotient coordinate. -/
theorem regularListModelTopSectionsLinearEquiv_coefficient
    (x : (((moduleSpecΓFunctor (R := regularListQuotientRing s)).mapHomologicalComplex
      (.up ℤ)).obj (closedImmersionRightAdjointRegularListResolutionComplex s I)).homology
        (s.length : ℤ)) :
    closedImmersionRightAdjointRegularListResolutionTopSectionsLinearEquiv s hs J eN
        (homologyMap
          (((moduleSpecΓFunctor (R := regularListQuotientRing s)).mapHomologicalComplex
            (.up ℤ)).map
            (((closedImmersionRightAdjoint
              (Spec.map (regularListQuotientMap s))).mapHomologicalComplex (.up ℤ)).map
                φ.hom')) (s.length : ℤ) x) =
      closedImmersionRightAdjointRegularListResolutionTopSectionsLinearEquiv s hs I eL x := by
  let E_I := closedImmersionRightAdjointRegularListResolutionSectionsExtAddEquiv s I s.length
  let E_J := closedImmersionRightAdjointRegularListResolutionSectionsExtAddEquiv s J s.length
  let P_I := closedImmersionRightAdjointRegularListResolutionTopSectionsLinearEquiv s hs I eL
  let P_J := closedImmersionRightAdjointRegularListResolutionTopSectionsLinearEquiv s hs J eN
  let ψ := (((moduleSpecΓFunctor (R := regularListQuotientRing s)).mapHomologicalComplex
    (.up ℤ)).map
    (((closedImmersionRightAdjoint (Spec.map (regularListQuotientMap s))).mapHomologicalComplex
      (.up ℤ)).map φ.hom'))
  have h : E_J (homologyMap ψ (s.length : ℤ) x) =
      (E_I x).comp (Ext.mk₀ (moduleSpecΓFunctor.map f)) (add_zero s.length) := by
    dsimp only [E_I, E_J]
    rw [closedImmersionRightAdjointRegularListResolutionSectionsExtAddEquiv_eq_affine,
      closedImmersionRightAdjointRegularListResolutionSectionsExtAddEquiv_eq_affine]
    exact canonicalAffineResolutionExt_naturality (regularListQuotientMap s) φ s.length x
  apply P_J.symm.injective
  rw [P_J.symm_apply_apply]
  obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (P_I x)
  rw [← hr]
  apply E_J.injective
  rw [h]
  have hc : E_I x = (ChainComplex.Koszul.topExtClass s hs (ModuleCat.of A A) r).comp
      (Ext.mk₀ eL.inv) (add_zero s.length) := by
    have hh := closedImmersionRightAdjointRegularListResolutionTopSectionsLinearEquiv_class
      s hs I eL r
    change E_I (P_I.symm (Ideal.Quotient.mk (Ideal.ofList s) r)) = _ at hh
    rw [hr, P_I.symm_apply_apply] at hh
    exact hh
  rw [hc, Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀, he]
  exact (closedImmersionRightAdjointRegularListResolutionTopSectionsLinearEquiv_class
    s hs J eN r).symm

include he in
/-- Compatible coefficient transport preserves the original actual top-homology sheaf frame. -/
theorem regularListModelTopHomologyIso_coefficient :
    homologyMap
        (((closedImmersionRightAdjoint
          (Spec.map (regularListQuotientMap s))).mapHomologicalComplex (.up ℤ)).map φ.hom')
        (s.length : ℤ) ≫
      (closedImmersionRightAdjointRegularListResolutionTopHomologyIso s hs J eN).hom =
    (closedImmersionRightAdjointRegularListResolutionTopHomologyIso s hs I eL).hom := by
  let B := regularListQuotientRing s
  let K := closedImmersionRightAdjointRegularListResolutionComplex s I
  let K' := closedImmersionRightAdjointRegularListResolutionComplex s J
  let ψ : K ⟶ K' :=
    (((closedImmersionRightAdjoint
      (Spec.map (regularListQuotientMap s))).mapHomologicalComplex (.up ℤ)).map φ.hom')
  let : QuasiIso (Complex.tildeGlobalSectionsCounit B (.up ℤ) K) :=
    closedImmersionRightAdjointRegularListResolutionTildeCounit_quasiIso s hs I eL
  let : QuasiIso (Complex.tildeGlobalSectionsCounit B (.up ℤ) K') :=
    closedImmersionRightAdjointRegularListResolutionTildeCounit_quasiIso s hs J eN
  let cI := Complex.tildeGlobalSectionsHomologyIso B (.up ℤ) K (s.length : ℤ)
  let cJ := Complex.tildeGlobalSectionsHomologyIso B (.up ℤ) K' (s.length : ℤ)
  let P_I := closedImmersionRightAdjointRegularListResolutionTopSectionsLinearEquiv s hs I eL
  let P_J := closedImmersionRightAdjointRegularListResolutionTopSectionsLinearEquiv s hs J eN
  let ψΓ := ((moduleSpecΓFunctor (R := B)).mapHomologicalComplex (.up ℤ)).map ψ
  have hc := canonicalTildeHomologyIso_naturality B ψ (s.length : ℤ)
  change (tilde.functor B).map (homologyMap ψΓ (s.length : ℤ)) ≫ cJ.hom =
    cI.hom ≫ homologyMap ψ (s.length : ℤ) at hc
  have hP : homologyMap ψΓ (s.length : ℤ) ≫ P_J.toModuleIso.hom = P_I.toModuleIso.hom := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact regularListModelTopSectionsLinearEquiv_coefficient s hs φ eL eN he x
  have ht := congrArg (tilde.functor B).map hP
  simp only [Functor.map_comp] at ht
  apply (cancel_epi cI.hom).mp
  rw [closedImmersionRightAdjointRegularListResolutionTopHomologyIso_hom s hs J eN,
    closedImmersionRightAdjointRegularListResolutionTopHomologyIso_hom s hs I eL]
  change cI.hom ≫ homologyMap ψ (s.length : ℤ) ≫ cJ.inv ≫
      (tilde.functor B).map P_J.toModuleIso.hom ≫ (tildeSelf (R := B)).hom =
    cI.hom ≫ cI.inv ≫ (tilde.functor B).map P_I.toModuleIso.hom ≫ (tildeSelf (R := B)).hom
  have hl := congrArg (fun z => z ≫ cJ.inv ≫
    (tilde.functor B).map P_J.toModuleIso.hom ≫ (tildeSelf (R := B)).hom) hc.symm
  have hr := congrArg (fun z => z ≫ (tildeSelf (R := B)).hom) ht
  simp only [Category.assoc, Iso.hom_inv_id_assoc] at hl
  simpa only [Category.assoc, Iso.hom_inv_id_assoc] using
    hl.trans (by simpa only [Category.assoc] using hr)

end RegularList
end AlgebraicGeometry.Scheme.Modules
