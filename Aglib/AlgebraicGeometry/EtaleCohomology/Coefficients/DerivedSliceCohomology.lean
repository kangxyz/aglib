/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Coefficients.DerivedCohomology
public import Aglib.CategoryTheory.Sites.SheafCohomology.ModuleCoefficients.DerivedScalarSlice
public import Aglib.CategoryTheory.Sites.SheafCohomology.Large.Injectives

/-!
# Derived coefficient sections on actual etale slices

The original slice site and ring restriction are retained. All sheafification,
injective-existence and Ext hypotheses are discharged at the actual sizes.
The scalar action is an honest ring map; a constant coefficient action can be
restricted using `sliceScalarAction` and its proved coherence.
-/

@[expose] public noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry Opposite
open CategoryTheory.Sheaf.ModuleCoefficients

namespace AlgebraicGeometry.Scheme.EtaleCohomology

variable (X : Scheme.{u})

local instance (U : X.Etale) :
    HasSheafify ((Scheme.smallEtaleTopology X).over U) AddCommGrpCat.{u + 1} := by
  infer_instance

local instance (U : X.Etale) :
    EnoughInjectives (Sheaf ((Scheme.smallEtaleTopology X).over U) AddCommGrpCat.{u + 1}) :=
  Sheaf.LargeCohomology.enoughInjectivesLarge.{u + 1, u} _

local instance (U : X.Etale) :
    HasExt.{u + 2} (Sheaf ((Scheme.smallEtaleTopology X).over U) AddCommGrpCat.{u + 1}) :=
  HasExt.standard _

local instance (U : X.Etale)
    (R : Sheaf ((Scheme.smallEtaleTopology X).over U) RingCat.{u}) :
    HasExt.{u + 2} (SheafOfModules.{u + 1} R) := SheafOfModules.hasExt R

local instance (U : X.Etale)
    (R : Sheaf ((Scheme.smallEtaleTopology X).over U) RingCat.{u}) :
    EnoughInjectives (SheafOfModules.{u + 1} R) :=
  SheafOfModules.enoughInjectivesLargeOverSmallScalars.{u + 1, u, 0, u} R

/-- Actual scalar-valued derived sections on an original small-etale slice. -/
def etaleSliceDerivedCohomologyAddEquiv
    (R : Sheaf (Scheme.smallEtaleTopology X) RingCat.{u}) (U : X.Etale)
    (Λ : RingCat.{u}) (α : Λ →+* (R.over U).obj.obj (op (Over.mk (𝟙 U))))
    (M : SheafOfModules.{u + 1} (R.over U)) (n : ℕ) :
    ((scalarTerminalSections.{u + 1, u, u, 0} (R.over U) Λ α).rightDerived n).obj M ≃+
      Sheaf.H.{u + 2} ((SheafOfModules.toSheaf (R.over U)).obj M) n :=
  derivedScalarCohomologyAddEquiv.{u + 1, u, u + 2, u + 2, u}
    Over.mkIdTerminal (R.over U) Λ α M n

end AlgebraicGeometry.Scheme.EtaleCohomology
