/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Godement.TotalComplex.QuasiIso
public import Aglib.AlgebraicGeometry.Cohomology.ProjectionFormula.TensorPushforward
public import Aglib.CategoryTheory.NatTrans.Unit

/-!
Source: `Quillen/AlgebraicGeometry/Scheme/Sheaf/GodementTensorUnit.lean` at LOCAL Quillen
`189a8e779f0c68b2dfc6f8195daebb3e684a5905`. Selection: whole_general;
source ranges [[1, 100]]. Actual objects, maps and hypotheses are preserved.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.NatTrans

namespace AlgebraicGeometry.Scheme.Modules.Godement

lemma exactPlus_map_quasiIso {X : Scheme.{u}} (F : X.Modules ⥤ X.Modules)
    [F.Additive] [F.PreservesHomology] {K C : CochainComplex.Plus X.Modules}
    (f : K ⟶ C) [QuasiIso f.hom] :
    QuasiIso (F.mapCochainComplexPlus.map f).hom :=
  inferInstanceAs (QuasiIso ((F.mapHomologicalComplex (.up ℤ)).map f.hom))

/-- The tensor image of the original Godement total augmentation on bounded-below complexes. -/
def godementTensorUnit (X : Scheme.{u}) (E : X.Modules) :
    (moduleTensorLeftFunctor X E).mapCochainComplexPlus ⟶
      godementTotalPlus X ⋙ (moduleTensorLeftFunctor X E).mapCochainComplexPlus :=
  CategoryTheory.NatTrans.unitPostcompose (godementTotalPlus X)
    (moduleTensorLeftFunctor X E).mapCochainComplexPlus (godementTotalPlusUnit X)

lemma godementTensorUnit_app (X : Scheme.{u}) (E : X.Modules)
    (C : CochainComplex.Plus X.Modules) :
    (godementTensorUnit X E).app C =
      (moduleTensorLeftFunctor X E).mapCochainComplexPlus.map
          ((godementTotalPlusUnit X).app C) := rfl

theorem godementTensorUnit_quasiIso {X : Scheme.{u}} (E : X.Modules)
    [IsFiniteLocallyFree X E] (C : CochainComplex.Plus X.Modules) :
    QuasiIso ((godementTensorUnit X E).app C).hom := by
  rw [godementTensorUnit_app]
  exact exactPlus_map_quasiIso _ ((godementTotalPlusUnit X).app C)

/-- The Godement-total image of the tensor augmentation map on bounded-below complexes. -/
def godementTensorTotalUnit (X : Scheme.{u}) (E : X.Modules) :
    (moduleTensorLeftFunctor X E).mapCochainComplexPlus ⋙ godementTotalPlus X ⟶
      (godementTotalPlus X ⋙ (moduleTensorLeftFunctor X E).mapCochainComplexPlus) ⋙
        godementTotalPlus X :=
  Functor.whiskerRight (godementTensorUnit X E) (godementTotalPlus X)

/-- The component retains the original augmentation before the outer total.

The typed component proof is taken from the delivered source
`Quillen/AlgebraicGeometry/Scheme/Sheaf/GodementTensorUnit.lean`, lines 80–96,
SHA256 `f6ab606ffa121800baf06ecddf3a4ac410763587916a19ca6f25a7bd4f8b18ab`.
The composite codomain preserves the aligned canonical map arguments. -/
lemma godementTensorTotalUnit_app (X : Scheme.{u}) (E : X.Modules)
    (C : CochainComplex.Plus X.Modules) :
    @Eq
      ((godementTotalPlus X).obj
          ((moduleTensorLeftFunctor X E).mapCochainComplexPlus.obj C) ⟶
        (godementTotalPlus X).obj
          ((godementTotalPlus X ⋙
            (moduleTensorLeftFunctor X E).mapCochainComplexPlus).obj C))
      ((godementTensorTotalUnit X E).app C)
      ((godementTotalPlus X).map
        (X := (moduleTensorLeftFunctor X E).mapCochainComplexPlus.obj C)
        (Y := (godementTotalPlus X ⋙
          (moduleTensorLeftFunctor X E).mapCochainComplexPlus).obj C)
        ((moduleTensorLeftFunctor X E).mapCochainComplexPlus.map
          (X := C) (Y := (godementTotalPlus X).obj C)
          ((godementTotalPlusUnit X).app C))) := by
  exact CategoryTheory.NatTrans.unitPostcompose_whiskerRight_app_of_eq
    (godementTotalPlus X) (moduleTensorLeftFunctor X E).mapCochainComplexPlus
    (godementTotalPlus X) (godementTotalPlusUnit X) (godementTensorTotalUnit X E) rfl C

/-- Check the whiskered component before specializing its object-valued functors. -/
private theorem total_whiskerRight_quasiIso {X : Scheme.{u}}
    {F G : CochainComplex.Plus X.Modules ⥤ CochainComplex.Plus X.Modules}
    (η : F ⟶ G)
    (τ : F ⋙ godementTotalPlus X ⟶ G ⋙ godementTotalPlus X)
    (hτ : τ = Functor.whiskerRight η (godementTotalPlus X))
    (C : CochainComplex.Plus X.Modules) [QuasiIso (η.app C).hom] :
    QuasiIso (τ.app C).hom := by
  subst τ
  exact godementTotalPlus_map_quasiIso (η.app C)

theorem godementTensorTotalUnit_quasiIso {X : Scheme.{u}} (E : X.Modules)
    [IsFiniteLocallyFree X E] (C : CochainComplex.Plus X.Modules) :
    QuasiIso ((godementTensorTotalUnit X E).app C).hom := by
  let := godementTensorUnit_quasiIso E C
  exact total_whiskerRight_quasiIso
    (godementTensorUnit X E) (godementTensorTotalUnit X E) rfl C

theorem godementTotalPlus_sameLowerBound {X : Scheme.{u}}
    (C : CochainComplex.Plus X.Modules) (a : ℤ) [C.obj.IsStrictlyGE a] :
    ((godementTotalPlus X).obj C).obj.IsStrictlyGE a :=
  godementTotal_isStrictlyGE C.obj a
    (fun n hn => CochainComplex.isZero_of_isStrictlyGE C.obj a n hn)

theorem godementTotalPlus_termwiseFlasque {X : Scheme.{u}}
    (C : CochainComplex.Plus X.Modules) (n : ℤ) :
    TopCat.Presheaf.IsFlasque (((godementTotalPlus X).obj C).obj.X n).presheaf := by
  obtain ⟨a, ha⟩ := C.property
  let := ha
  exact godementTotal_isFlasque C.obj a
    (fun i hi => CochainComplex.isZero_of_isStrictlyGE C.obj a i hi) n

end AlgebraicGeometry.Scheme.Modules.Godement
