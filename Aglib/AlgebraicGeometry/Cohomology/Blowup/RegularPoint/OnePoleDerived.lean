/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Blowup.Differentials.RegularPoint.OnePole
public import Aglib.AlgebraicGeometry.Cohomology.Blowup.RegularPoint.ExceptionalPositive
public import Aglib.AlgebraicGeometry.Modules.Differentials.Relative.ExteriorCoefficient
public import Aglib.AlgebraicGeometry.Modules.Invertible.Affine
public import Aglib.AlgebraicGeometry.Modules.Pullback.Tensor.Section.Basic
public import Aglib.AlgebraicGeometry.Modules.Tensor.Section


/-!
# The original one-point derived coefficient map

The existing one-pole map and coefficient-tensored exceptional rho define the
original derived map. Its coefficient normalization starts from raw exterior
forms on the parent, not their bidual. The ordinary adjunction square and
native derived single-unit naturality prove the normalization; neither
bidual evaluation nor a general derived single unit is inverted.
-/

@[expose] public noncomputable section

open CategoryTheory
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Differentials
open AlgebraicGeometry.Scheme.Modules.Invertible AlgebraicGeometry.Scheme.Hom
open AlgebraicGeometry.Scheme.Blowup.RegularPoint AlgebraicGeometry.Scheme.Cohomology

universe u vK uC vC wC uD vD wD


open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.Differentials

namespace AlgebraicGeometry.Scheme.Blowup.RegularPoint

/-- Close the original coefficient square using the original single unit and a
retraction at its target, before specializing either category to module sheaves. -/
private theorem singleUnit_coefficient_retraction
    {C : Type uC} [Category.{vC} C] [Abelian C] [HasDerivedCategory.{wC} C]
    [EnoughInjectives C]
    {D : Type uD} [Category.{vD} D] [Abelian D] [HasDerivedCategory.{wD} D]
    (G : C ⥤ D) [G.Additive]
    {M E : D} {N T : C}
    (c : M ⟶ G.obj N) (d : E ⟶ G.obj T) (f : M ⟶ E) (k : N ⟶ T)
    (r : G.rightDerivedFunctorPlus.obj
      ((DerivedCategory.Plus.singleFunctor C 0).obj T) ⟶
        (DerivedCategory.Plus.singleFunctor D 0).obj E)
    (ψ : G.rightDerivedFunctorPlus.obj
      ((DerivedCategory.Plus.singleFunctor C 0).obj N) ⟶
        (DerivedCategory.Plus.singleFunctor D 0).obj E)
    (hc : f ≫ d = c ≫ G.map k)
    (hr : (DerivedCategory.Plus.singleFunctor D 0).map d ≫
      G.rightDerivedSingleUnit T ≫ r = 𝟙 _)
    (hψ : ψ = G.rightDerivedFunctorPlus.map
      ((DerivedCategory.Plus.singleFunctor C 0).map k) ≫ r) :
    (DerivedCategory.Plus.singleFunctor D 0).map c ≫ G.rightDerivedSingleUnit N ≫ ψ =
      (DerivedCategory.Plus.singleFunctor D 0).map f := by
  rw [hψ]
  have hn := G.rightDerivedSingleUnit_coefficient_naturality c d f k hc
  calc
    _ = (((DerivedCategory.Plus.singleFunctor D 0).map c ≫ G.rightDerivedSingleUnit N) ≫
        G.rightDerivedFunctorPlus.map ((DerivedCategory.Plus.singleFunctor C 0).map k)) ≫ r := by
      simp only [Category.assoc]
    _ = ((DerivedCategory.Plus.singleFunctor D 0).map f ≫
        ((DerivedCategory.Plus.singleFunctor D 0).map d ≫ G.rightDerivedSingleUnit T)) ≫ r :=
      congrArg (fun z => z ≫ r) hn.symm
    _ = (DerivedCategory.Plus.singleFunctor D 0).map f := by
      simp only [Category.assoc, hr, Category.comp_id]

/-- The same standard derived-category realization used by the original tensor-rho. -/
local instance pointOnePoleDerivedCategory (Z : Scheme.{u}) :
    HasDerivedCategory.{u + 1} Z.Modules := HasDerivedCategory.standard _

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
  {Λ A : CommRingCat.{u}} [IsDomain A]
  (ρ : Λ ⟶ A) (β : X ⟶ Spec A) [IsDominant β]
  (K : Type vK) [Field K] [Algebra A K] [IsFractionRing A K]
  (hβ : IsIso (CommRingCat.ofHom (Scheme.functionFieldMap β)))
  (hX : RegularStalks X) (p : X) (hp : IsClosed ({p} : Set X))
  (hd : ringKrullDim (X.presheaf.stalk p) = 2)
  (n : ℕ) (L : LineBundle X)
  (φ : moduleExteriorPower X (relativeDifferentialSheaf (β ≫ Spec.map ρ)) n ⟶ L.val)

local notation "a" => β ≫ Spec.map ρ
local notation "Y" => pointBlowup X p
local notation "b" => pointBlowdown X p
local notation "MX" => moduleExteriorPower X (relativeDifferentialSheaf a) n
local notation "MY" => moduleExteriorPower Y (relativeDifferentialSheaf (b ≫ a)) n
local notation "DY" => dualSheaf Y (dualSheaf Y MY)
local notation "P" => CategoryTheory.Functor.obj (pullback b) L.val
local notation "Q" => exceptionalPositiveModule X p
local notation "T" => CategoryTheory.Functor.obj (moduleTensorLeftFunctor Y P) Q
local notation "H" => pushforward b
local notation "SX" => DerivedCategory.Plus.singleFunctor X.Modules 0
local notation "SY" => DerivedCategory.Plus.singleFunctor (Scheme.Modules Y) 0

section Ordinary

variable [IsRegularLocalRing (X.presheaf.stalk p)]

/-- The original one-pole unit gives the ordinary coefficient square. Its source
is the raw exterior module, and its only evaluation is the original forward map. -/
theorem modelPointOnePoleMap_coefficient :
    let P₀ : Scheme.Modules Y := (pullback b).obj L.val
    let Q₀ : Scheme.Modules Y := (dualLineBundle Y (pointIdealLine X p hp)).val
    let T₀ : Scheme.Modules Y :=
      (tensorLineBundle Y (pullbackLineBundle b L)
        (dualLineBundle Y (pointIdealLine X p hp))).val
    let κ : DY ⟶ T₀ := modelPointOnePoleMap ρ β K hβ p hp hd n L φ
    let s : SheafOfModules.unit (Y).ringCatSheaf ⟶ Q₀ := exceptionalPositiveSection X p
    let RY : tensorSheaf Y P₀ (SheafOfModules.unit (Y).ringCatSheaf) ≅ P₀ :=
      (SheafOfModulesOfCommRing.tensorRightUnitIso (Y).sheaf).app P₀
    let v : P₀ ⟶ T₀ := RY.inv ≫ tensorSheafMap Y (𝟙 P₀) s
    bidualFormsCoefficient a b n ≫ (H).map κ =
      φ ≫ ((pullbackPushforwardAdjunction b).unit.app L.val ≫ (H).map v) := by
  let adj := pullbackPushforwardAdjunction b
  let P₀ : Scheme.Modules Y := (pullback b).obj L.val
  let Q₀ : Scheme.Modules Y := (dualLineBundle Y (pointIdealLine X p hp)).val
  let T₀ : Scheme.Modules Y :=
    (tensorLineBundle Y (pullbackLineBundle b L)
      (dualLineBundle Y (pointIdealLine X p hp))).val
  let κ : DY ⟶ T₀ := modelPointOnePoleMap ρ β K hβ p hp hd n L φ
  let s : SheafOfModules.unit (Y).ringCatSheaf ⟶ Q₀ := exceptionalPositiveSection X p
  let RY : tensorSheaf Y P₀ (SheafOfModules.unit (Y).ringCatSheaf) ≅ P₀ :=
    (SheafOfModulesOfCommRing.tensorRightUnitIso (Y).sheaf).app P₀
  let v : P₀ ⟶ T₀ := RY.inv ≫ tensorSheafMap Y (𝟙 P₀) s
  have hκ : rawFormsPullback a b n ≫ bidualMap Y MY ≫ κ =
      (pullback b).map φ ≫ (positiveCartierTensorSection Y Q₀ s).app P₀ ≫
        (tensorSheafBraiding Y Q₀ P₀).hom :=
    modelPointOnePoleMap_unit ρ β K hβ p hp hd n L φ
  have hv : (positiveCartierTensorSection Y Q₀ s).app P₀ ≫
      (tensorSheafBraiding Y Q₀ P₀).hom = v := by
    have hRY : (MonoidalCategoryStruct.rightUnitor P₀ :
        tensorSheaf Y P₀ (SheafOfModules.unit (Y).ringCatSheaf) ≅ P₀) = RY :=
      SheafOfModulesOfCommRing.rightUnitor_eq_tensorRightUnitIso (Y).sheaf P₀
    exact (positiveSection_eq_rightInsertion Y P₀ Q₀ s).trans
      (congrArg (fun e : tensorSheaf Y P₀ (SheafOfModules.unit (Y).ringCatSheaf) ≅ P₀ =>
        e.inv ≫ tensorSheafMap Y (𝟙 P₀) s) hRY)
  have hunit : (pullback b).map φ ≫ v =
      (rawFormsPullback a b n ≫ bidualMap Y MY) ≫ κ :=
    ((Category.assoc (rawFormsPullback a b n) (bidualMap Y MY) κ).trans
      (hκ.trans (congrArg (fun z : P₀ ⟶ T₀ => (pullback b).map φ ≫ z) hv))).symm
  have hc : adj.homEquiv MX DY (rawFormsPullback a b n ≫ bidualMap Y MY) =
      bidualFormsCoefficient a b n :=
    (adj.homEquiv_naturality_right (rawFormsPullback a b n) (bidualMap Y MY)).trans
      (congrArg (fun z => z ≫ (H).map (bidualMap Y MY)) (rawFormsPullback_adjoint a b n))
  have hs := adj.homEquiv_naturality_left_square φ v
    (rawFormsPullback a b n ≫ bidualMap Y MY) κ hunit
  calc
    _ = adj.homEquiv MX DY (rawFormsPullback a b n ≫ bidualMap Y MY) ≫ (H).map κ :=
      congrArg (fun z => z ≫ (H).map κ) hc.symm
    _ = φ ≫ adj.homEquiv L.val T₀ v := hs.symm
    _ = _ := congrArg (fun z => φ ≫ z) (adj.homEquiv_unit L.val T₀ v)

end Ordinary

section Derived

/-- The original one-pole arrow followed by the accepted coefficient-tensored rho. -/
def modelPointOnePoleDerivedMap :
    (derivedPushforwardPlus b).obj ((SY).obj DY) ⟶ (SX).obj L.val := by
  let : IsRegularLocalRing (X.presheaf.stalk p) := hX p
  exact (derivedPushforwardPlus b).map
      ((SY).map (modelPointOnePoleMap ρ β K hβ p hp hd n L φ)) ≫
    exceptionalPositiveTensorRho X hX p hp hd L.val

/-- The original derived producer has its literal defining composite. The local
regularity instance is exactly the one installed by that producer. -/
private theorem modelPointOnePoleDerivedMap_eq :
    letI : IsRegularLocalRing (X.presheaf.stalk p) := hX p
    modelPointOnePoleDerivedMap ρ β K hβ hX p hp hd n L φ =
      (derivedPushforwardPlus b).map
        ((SY).map (modelPointOnePoleMap ρ β K hβ p hp hd n L φ)) ≫
          exceptionalPositiveTensorRho X hX p hp hd L.val := by
  rfl

/-- The original raw exterior coefficient is normalized by the same derived map.
No pullback-bidual comparison or cancellation of bidual evaluation is used. -/
theorem modelPointOnePoleDerivedMap_coefficient :
    let A₀ : DerivedCategory.Plus X.Modules := (SX).obj MX
    let B₀ : DerivedCategory.Plus X.Modules := (SX).obj ((H).obj DY)
    let D₀ : DerivedCategory.Plus X.Modules :=
      (derivedPushforwardPlus b).obj ((SY).obj DY)
    let E₀ : DerivedCategory.Plus X.Modules := (SX).obj L.val
    let c : A₀ ⟶ B₀ := (SX).map (bidualFormsCoefficient a b n)
    let u : B₀ ⟶ D₀ := (H).rightDerivedSingleUnit DY
    let ψ : D₀ ⟶ E₀ := modelPointOnePoleDerivedMap ρ β K hβ hX p hp hd n L φ
    let f : A₀ ⟶ E₀ := (SX).map φ
    (show A₀ ⟶ E₀ from c ≫ u ≫ ψ) = f := by
  let : IsRegularLocalRing (X.presheaf.stalk p) := hX p
  have hc := modelPointOnePoleMap_coefficient ρ β K hβ p hp hd n L φ
  have hr := exceptionalPositiveTensorRho_unit X hX p hp hd L.val
  have hψ := modelPointOnePoleDerivedMap_eq ρ β K hβ hX p hp hd n L φ
  exact singleUnit_coefficient_retraction (H) (bidualFormsCoefficient a b n) _ φ _ _
    (modelPointOnePoleDerivedMap ρ β K hβ hX p hp hd n L φ) hc.symm hr hψ

end Derived

end AlgebraicGeometry.Scheme.Blowup.RegularPoint
