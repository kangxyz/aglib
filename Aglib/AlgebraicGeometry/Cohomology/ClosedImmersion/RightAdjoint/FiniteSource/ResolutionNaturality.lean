/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.ClosedImmersion.RightAdjoint.FiniteSource.Derived
public import Aglib.AlgebraicGeometry.Modules.Complex.TildeNaturality
public import Aglib.AlgebraicGeometry.Modules.DerivedCategory.Basic

/-!
# Original closed-adjoint homology and resolution maps

The original derived-unit model and exact-tilde counit preserve coefficient
maps and arbitrary supplied resolution lifts. No new derived model is chosen.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian HomologicalComplex

universe u

namespace AlgebraicGeometry.Scheme.Modules

attribute [local instance] standardHasDerivedCategory

/-- Every supplied resolution lift computes the original derived coefficient map. -/
@[reassoc]
theorem derivedClosedImmersionRightAdjointModelHomologyIso_naturality
    {X Y : Scheme.{u}} (i : X ⟶ Y) [IsClosedImmersion i]
    {L L' : Y.Modules} {J : InjectiveResolution L} {J' : InjectiveResolution L'}
    {μ : L ⟶ L'} (φ : InjectiveResolution.Hom J J' μ) (n : ℤ) :
    (derivedClosedImmersionRightAdjointModelHomologyIso i J n).hom ≫
        homologyMap (((closedImmersionRightAdjoint i).mapHomologicalComplex (.up ℤ)).map
          φ.hom') n =
      (DerivedCategory.Plus.homologyFunctor X.Modules n).map
        ((derivedClosedImmersionRightAdjointPlus i).map
          ((DerivedCategory.Plus.singleFunctor Y.Modules 0).map μ)) ≫
        (derivedClosedImmersionRightAdjointModelHomologyIso i J' n).hom := by
  let F := closedImmersionRightAdjoint i
  let H := DerivedCategory.Plus.homologyFunctor X.Modules n
  let p := DerivedCategory.Plus.Q.map (F.mapCochainComplexPlus.map φ.mapPlus)
  let d := H.map (F.rightDerivedFunctorPlus.map
    ((DerivedCategory.Plus.singleFunctor Y.Modules 0).map μ))
  let eJ := H.mapIso (J.rightDerivedFunctorPlusIso F)
  let eJ' := H.mapIso (J'.rightDerivedFunctorPlusIso F)
  let PJ := (DerivedCategory.Plus.homologyFunctorFactors (A := X.Modules) n).app
    (F.mapCochainComplexPlus.obj J.cochainComplexPlus)
  let PJ' := (DerivedCategory.Plus.homologyFunctorFactors (A := X.Modules) n).app
    (F.mapCochainComplexPlus.obj J'.cochainComplexPlus)
  have hR := congrArg H.map (J.rightDerivedFunctorPlusIso_naturality F φ)
  simp only [Functor.map_comp] at hR
  change H.map p ≫ eJ'.hom = eJ.hom ≫ d at hR
  let a : H.obj (DerivedCategory.Plus.Q.obj (F.mapCochainComplexPlus.obj J.cochainComplexPlus)) ⟶
      ((F.mapHomologicalComplex (.up ℤ)).obj J.cochainComplex).homology n := PJ.hom
  let a' : H.obj (DerivedCategory.Plus.Q.obj (F.mapCochainComplexPlus.obj J'.cochainComplexPlus)) ⟶
      ((F.mapHomologicalComplex (.up ℤ)).obj J'.cochainComplex).homology n := PJ'.hom
  let v : ((F.mapHomologicalComplex (.up ℤ)).obj J.cochainComplex).homology n ⟶
      ((F.mapHomologicalComplex (.up ℤ)).obj J'.cochainComplex).homology n :=
    homologyMap ((F.mapHomologicalComplex (.up ℤ)).map φ.hom') n
  have hP : H.map p ≫ a' = a ≫ v :=
    (DerivedCategory.Plus.homologyFunctorFactors
      (A := X.Modules) (n := n)).hom.naturality (F.mapCochainComplexPlus.map φ.mapPlus)
  have hJJ : eJ.inv ≫ H.map p = d ≫ eJ'.inv := by
    apply (cancel_mono eJ'.hom).mp
    rw [Category.assoc, hR]
    simp only [Iso.inv_hom_id_assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have h₁ : eJ.inv ≫ a ≫ v = eJ.inv ≫ (H.map p ≫ a') :=
    congrArg (fun k : H.obj (DerivedCategory.Plus.Q.obj
      (F.mapCochainComplexPlus.obj J.cochainComplexPlus)) ⟶
        ((F.mapHomologicalComplex (.up ℤ)).obj J'.cochainComplex).homology n =>
          eJ.inv ≫ k) hP.symm
  have h₂ : eJ.inv ≫ (H.map p ≫ a') = (eJ.inv ≫ H.map p) ≫ a' :=
    (Category.assoc eJ.inv (H.map p) a').symm
  have h₃ : (eJ.inv ≫ H.map p) ≫ a' = (d ≫ eJ'.inv) ≫ a' :=
    congrArg (fun k : H.obj (F.rightDerivedFunctorPlus.obj
      ((DerivedCategory.Plus.singleFunctor Y.Modules 0).obj L)) ⟶
        H.obj (DerivedCategory.Plus.Q.obj (F.mapCochainComplexPlus.obj J'.cochainComplexPlus)) =>
          k ≫ a') hJJ
  have h₄ : (d ≫ eJ'.inv) ≫ a' = d ≫ eJ'.inv ≫ a' := Category.assoc d eJ'.inv a'
  exact Eq.trans h₁ (Eq.trans h₂ (Eq.trans h₃ h₄))

/-- The original exact-tilde quotient model preserves every coefficient-resolution lift. -/
@[reassoc]
theorem closedImmersionRightAdjointQuotientResolutionHomologyIso_naturality
    {R : CommRingCat.{u}} [IsNoetherianRing R] (I : Ideal R)
    {L L' : (Spec R).Modules} [L.IsQuasicoherent] [L'.IsQuasicoherent]
    {J : InjectiveResolution L} {J' : InjectiveResolution L'} {μ : L ⟶ L'}
    (φ : InjectiveResolution.Hom J J' μ) (n : ℤ) :
    let F := closedImmersionRightAdjoint (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))
    let ψ := (F.mapHomologicalComplex (.up ℤ)).map φ.hom'
    (tilde.functor (.of (R ⧸ I))).map
        (homologyMap (((moduleSpecΓFunctor (R := .of (R ⧸ I))).mapHomologicalComplex
          (.up ℤ)).map ψ) n) ≫
        (closedImmersionRightAdjointQuotientResolutionHomologyIso I J' n).hom =
      (closedImmersionRightAdjointQuotientResolutionHomologyIso I J n).hom ≫
        homologyMap ψ n := by
  let : QuasiIso (Complex.tildeGlobalSectionsCounit (.of (R ⧸ I)) (.up ℤ)
      (closedImmersionRightAdjointQuotientResolutionComplex I J)) :=
    closedImmersionRightAdjointQuotientResolutionTildeCounit_quasiIso I J
  let : QuasiIso (Complex.tildeGlobalSectionsCounit (.of (R ⧸ I)) (.up ℤ)
      (closedImmersionRightAdjointQuotientResolutionComplex I J')) :=
    closedImmersionRightAdjointQuotientResolutionTildeCounit_quasiIso I J'
  let ψ : closedImmersionRightAdjointQuotientResolutionComplex I J ⟶
      closedImmersionRightAdjointQuotientResolutionComplex I J' :=
    (((closedImmersionRightAdjoint (Spec.map
      (CommRingCat.ofHom (Ideal.Quotient.mk I)))).mapHomologicalComplex (.up ℤ)).map φ.hom')
  exact Complex.tildeGlobalSectionsHomologyIso_naturality (.of (R ⧸ I)) (.up ℤ)
    (K := closedImmersionRightAdjointQuotientResolutionComplex I J)
    (L := closedImmersionRightAdjointQuotientResolutionComplex I J') ψ n

end AlgebraicGeometry.Scheme.Modules
