/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Complex.TensorToUnit

/-! Public tensor-to-unit interfaces on actual modules and ordinary complexes, without
local-freeness, boundedness or perfect-complex assumptions. -/
@[expose] public section
noncomputable section
universe u
open CategoryTheory AlgebraicGeometry SheafOfModulesOfCommRing

namespace AglibTest.TensorToUnit

variable {X : Scheme.{u}} {L : X.Modules}
  (f : L ⟶ SheafOfModules.unit X.ringCatSheaf)

example : Scheme.Modules.tensorToUnit f =
    Scheme.Modules.moduleTensorCoefficientMap X f ≫ (tensorLeftUnitIso X.sheaf).hom := rfl

example (M : X.Modules) (U : X.Opens) (a : Γ(L, U)) (m : Γ(M, U)) :
    ((Scheme.Modules.tensorToUnit f).app M).app U
        (Scheme.Modules.moduleTensorSection X L M U a m) =
      (show Γ(X, U) from f.app U a) • m :=
  Scheme.Modules.tensorToUnit_section f M U a m

example {U : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] (M : X.Modules) :
    (Scheme.Modules.tensorRestrictionIso j L M).hom ≫
        (Scheme.Modules.restrictFunctor j).map ((Scheme.Modules.tensorToUnit f).app M) =
      (Scheme.Modules.tensorToUnit ((Scheme.Modules.restrictFunctor j).map f ≫
        (Scheme.Modules.restrictUnitIso j).hom)).app (M.restrict j) :=
  Scheme.Modules.tensorToUnit_restrict j f M

example : (Scheme.Modules.tensorToUnit f).app (SheafOfModules.unit X.ringCatSheaf) =
    (tensorRightUnitIso X.sheaf).hom.app L ≫ f :=
  Scheme.Modules.tensorToUnit_unit f

example (K : CochainComplex X.Modules ℤ) (n : ℤ) :
    ((Scheme.Modules.Complex.tensorToUnit f).app K).f n =
      (Scheme.Modules.tensorToUnit f).app (K.X n) :=
  Scheme.Modules.Complex.tensorToUnit_f f K n

example (n : ℤ) :
    (Scheme.Modules.Complex.tensorToUnit f).app
        ((CochainComplex.singleFunctor X.Modules n).obj
          (SheafOfModules.unit X.ringCatSheaf)) =
      (Scheme.Modules.Complex.tensorLeftSingleUnitIso X L n).hom ≫
        (CochainComplex.singleFunctor X.Modules n).map f :=
  Scheme.Modules.Complex.tensorToUnit_single f n

end AglibTest.TensorToUnit
