/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Pullback.Tensor.Section.Basic
public import Aglib.AlgebraicGeometry.Modules.Tensor.Section


/-!
# Naturality of the original braided section insertion

The original tensor-section natural transformation and native braiding
compare the same section under a change of its other tensor factor.
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory BraidedCategory

universe u

namespace AlgebraicGeometry.Scheme.Modules

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The actual braided positive-section insertion is natural in its other factor. -/
theorem positiveSection_otherFactor {X : Scheme.{u}} (M M' N : X.Modules)
    (s : SheafOfModules.unit X.ringCatSheaf ⟶ N) (h : M ⟶ M') :
    (positiveCartierTensorSection X N s).app M ≫ (tensorSheafBraiding X N M).hom ≫
        tensorSheafMap X h (𝟙 N) =
      h ≫ (positiveCartierTensorSection X N s).app M' ≫
        (tensorSheafBraiding X N M').hom := by
  have hb := braiding_naturality (C := X.Modules) (𝟙 N) h
  have hn := (positiveCartierTensorSection X N s).naturality h
  change h ≫ (positiveCartierTensorSection X N s).app M' =
    (positiveCartierTensorSection X N s).app M ≫ tensorSheafMap X (𝟙 N) h at hn
  calc
    _ = (positiveCartierTensorSection X N s).app M ≫
        tensorSheafMap X (𝟙 N) h ≫ (tensorSheafBraiding X N M').hom :=
      congrArg (fun z => (positiveCartierTensorSection X N s).app M ≫ z) hb.symm
    _ = _ := (Category.assoc _ _ _).symm.trans
      ((congrArg (fun z => z ≫ (tensorSheafBraiding X N M').hom) hn.symm).trans
        (Category.assoc _ _ _))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Original coefficient, section and target-factor transport form one actual pullback square. -/
theorem pullback_positiveSection_otherFactor {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M P N : Y.Modules) (Q : X.Modules) (ψ : M ⟶ P)
    (s : SheafOfModules.unit Y.ringCatSheaf ⟶ N) (h : (pullback f).obj P ⟶ Q) :
    (pullback f).map (ψ ≫ (positiveCartierTensorSection Y N s).app P ≫
        (tensorSheafBraiding Y N P).hom) ≫ pullbackTensorMap f P N ≫
        tensorSheafMap X h (𝟙 ((pullback f).obj N)) =
      (pullback f).map ψ ≫ h ≫
        (positiveCartierTensorSection X ((pullback f).obj N)
          ((pullbackUnitIso f).inv ≫ (pullback f).map s)).app Q ≫
          (tensorSheafBraiding X ((pullback f).obj N) Q).hom := by
  have hp := congrArg (fun z => (pullback f).map ψ ≫ z ≫
    tensorSheafMap X h (𝟙 ((pullback f).obj N))) (pullback_positiveSection f P N s)
  simp only [Category.assoc] at hp
  have hn := positiveSection_otherFactor ((pullback f).obj P) Q ((pullback f).obj N)
    ((pullbackUnitIso f).inv ≫ (pullback f).map s) h
  have he := congrArg (fun z => (pullback f).map ψ ≫ z) hn
  simpa only [CategoryTheory.Functor.map_comp, Category.assoc] using hp.trans he

end AlgebraicGeometry.Scheme.Modules
