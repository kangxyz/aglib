/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aglib contributors
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.ConstantModulePresheaf
public import Aglib.Algebra.Category.ModuleCat.FunctorTensorNaturality
public import Aglib.CategoryTheory.Preadditive.ScalarDiagramLinear
public import Aglib.Algebra.Category.ModuleCat.FunctorTensorRightScalars
public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.ConstantCoefficients

/-! # The original relative constant-module tensor comparison

All components use the original coefficient maps on the actual pulled-back
constant coefficient. Restriction naturality is the canonical tensor comparison's
naturality in that same cohomology functor. The coefficient action is on the
right factor and need not come from a ring map into the coefficient ring.
Invertibility is asserted only on affine tests, where the actual proper
base change is qcqs and the existing coefficient coproduct theorem applies.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct

namespace AlgebraicGeometry.Scheme.EtaleCohomology

universe u r w s e

attribute [local instance] hasSheafifyLarge

variable {X S : Scheme.{u}} (f : X ⟶ S) (R : Type) [Field R]
  [∀ U : S.Etale, HasExt.{max (u + 1) e}
    (AbelianSheaf.{u, u + 1} (pullback U.hom f))]

local instance constantModuleTensorFibre_additive (U : S.Etale) (q : ℕ) :
    (constantModuleFibreCohomology f R U q).Additive := by
  let H := (Functor.whiskeringRight (ModuleCat.{u + 1} R)
    AddCommGrpCat.{u + 1} AddCommGrpCat.{max (u + 1) e}).obj
      (constantAbelianFibreCohomology f U q)
  let A := forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1}
  let : (H.obj A).Additive := by
    change (constantModuleFibreCohomologyAb f R U q).Additive
    infer_instance
  exact Functor.coefficientModuleDiagram_additive H A
    (ModuleCat.forgetScalarAction R)

local instance constantModuleTensorFibre_linear (U : S.Etale) (q : ℕ) :
    (constantModuleFibreCohomology f R U q).Linear R := by
  unfold constantModuleFibreCohomology
  apply Functor.coefficientModuleDiagram_linear
  intro a M
  rfl

variable (Λ : Type r) [Ring Λ] (M : ModuleCat.{u + 1} R)
  [Module Λ M] [SMulCommClass Λ R M]

/-- The original relative cohomology tensor map is linear for the original
coefficient action, with no scalar-extension assumption on the two rings. -/
def constantModuleTensorComparison (U : S.Etale) (q : ℕ) :
    letI := TensorProduct.rightModule R Λ
      ((constantModuleFibreCohomology f R U q).obj (ModuleCat.liftedUnit.{0, u + 1} R)) M
    (constantModuleFibreCohomology f R U q).obj (ModuleCat.liftedUnit.{0, u + 1} R) ⊗[R] M →ₗ[Λ]
      (constantModuleFibreCohomology f Λ U q).obj (ModuleCat.of Λ M) := by
  letI := TensorProduct.rightModule R Λ
    ((constantModuleFibreCohomology f R U q).obj (ModuleCat.liftedUnit.{0, u + 1} R)) M
  let : Module Λ ((constantModuleFibreCohomology f R U q).obj M) :=
    inferInstanceAs (Module Λ
      ((constantModuleFibreCohomology f Λ U q).obj (ModuleCat.of Λ M)))
  exact ModuleCat.functorTensorComparisonOver (constantModuleFibreCohomology f R U q)
    Λ (fun a x => by rfl)

/-- The scalar-linear map retains the original canonical comparison function. -/
@[simp]
theorem constantModuleTensorComparison_apply (U : S.Etale) (q : ℕ)
    (z : (constantModuleFibreCohomology f R U q).obj
      (ModuleCat.liftedUnit.{0, u + 1} R) ⊗[R] M) :
    constantModuleTensorComparison f R Λ M U q z =
      ModuleCat.functorTensorComparison (constantModuleFibreCohomology f R U q) M z := rfl

variable [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]
  [∀ U : S.Etale, HasExt.{s} (Sheaf ((Scheme.smallEtaleTopology X).over
    ((siteBaseChange f).obj U)) AddCommGrpCat.{u + 1})]

/-- The coefficient action on the right factor of the sectionwise tensor. -/
local instance constantModuleTensorValueModule (U : S.Etaleᵒᵖ) (q : ℕ) :
    Module Λ ((constantModuleCohomologyPresheaf f R
      (ModuleCat.liftedUnit.{0, u + 1} R) q).obj U ⊗[R] M) :=
  TensorProduct.rightModule R Λ _ M

/-- The actual rank-one cohomology diagram tensored with the original module. -/
abbrev constantModuleTensorPresheaf (q : ℕ) :
    S.Etaleᵒᵖ ⥤ ModuleCat.{max (u + 1) e} Λ :=
  constantModuleCohomologyPresheaf f R (ModuleCat.liftedUnit.{0, u + 1} R) q ⋙
    ModuleCat.tensorRightScalarsFunctor R Λ M

/-- The complete coefficient-linear presheaf comparison uses precisely the
original restrictions and original coefficient maps on every test. -/
def constantModuleTensorPresheafComparison (q : ℕ) :
    constantModuleTensorPresheaf f R Λ M q ⟶
      constantModuleCohomologyPresheaf f Λ (ModuleCat.of Λ M) q where
  app U := ConcreteCategory.ofHom (C := ModuleCat.{max (u + 1) e} Λ)
    (X := (constantModuleTensorPresheaf f R Λ M q).obj U)
    (Y := (constantModuleCohomologyPresheaf f Λ (ModuleCat.of Λ M) q).obj U)
    (constantModuleTensorComparison f R Λ M U.unop q)
  naturality U V g := by
    ext z
    change constantModuleTensorComparison f R Λ M V.unop q
        (TensorProduct.map
          ((constantModuleFibreRestriction f R g.unop q).app
            (ModuleCat.liftedUnit.{0, u + 1} R)).hom LinearMap.id z) =
      (constantModuleFibreRestriction f Λ g.unop q).app (ModuleCat.of Λ M)
        (constantModuleTensorComparison f R Λ M U.unop q z)
    exact (ModuleCat.functorTensorComparison_natTrans_apply
      (constantModuleFibreRestriction f R g.unop q) M z).symm

/-- The actual inverse-image constant comparison, enhanced by the same
coefficient action, identifies the test functor with original constant cohomology. -/
def constantModuleFibreConstantIso (U : S.Etale) (q : ℕ) :
    constantModuleFibreCohomology f R U q ≅
      ModuleCat.Sheaf.constantCohomology (pullback U.hom f).smallEtaleTopology R q :=
  Functor.coefficientModuleDiagramNatIso
    (forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1})
    (ModuleCat.forgetScalarAction R)
    ((Functor.whiskeringRight (ModuleCat.{u + 1} R)
      AddCommGrpCat.{u + 1} AddCommGrpCat.{max (u + 1) e}).mapIso
        (Functor.isoWhiskerRight
          (inverseImageConstantIso (pullback.snd U.hom f))
          (Sheaf.functorH (pullback U.hom f).smallEtaleTopology q)))

omit [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]
  [∀ U : S.Etale, HasExt.{s} (Sheaf ((Scheme.smallEtaleTopology X).over
    ((siteBaseChange f).obj U)) AddCommGrpCat.{u + 1})] in
/-- On an affine test, properness gives the qcqs hypothesis required by the
existing arbitrary coefficient coproduct theorem. No assertion is made for
unrestricted non-quasicompact tests. -/
theorem constantModuleTensorComparison_bijective_of_affine
    [IsProper f] (U : S.Etale) [IsAffine U.left] (q : ℕ) :
    Function.Bijective (constantModuleTensorComparison f R Λ M U q) := by
  let : CompactSpace ((𝟭 Scheme.{u}).obj U.left) :=
    inferInstanceAs (CompactSpace U.left)
  let : QuasiSeparatedSpace ((𝟭 Scheme.{u}).obj U.left) :=
    inferInstanceAs (QuasiSeparatedSpace U.left)
  let p := pullback.fst U.hom f
  let : IsProper p := inferInstanceAs (IsProper (pullback.fst U.hom f))
  let : CompactSpace (pullback U.hom f : Scheme.{u}) :=
    QuasiCompact.compactSpace_of_compactSpace p
  let : QuasiSeparatedSpace (pullback U.hom f : Scheme.{u}) :=
    quasiSeparatedSpace_of_quasiSeparated p
  let : PreservesColimitsOfShape
      (Discrete (Module.Free.ChooseBasisIndex R M))
      (ModuleCat.Sheaf.constantCohomology (pullback U.hom f).smallEtaleTopology R q) :=
    Continuity.qcqsConstantCohomology_preservesCoproducts (pullback U.hom f) R
      (Module.Free.ChooseBasisIndex R M) q
  let : PreservesColimitsOfShape
      (Discrete (Module.Free.ChooseBasisIndex R M))
      (constantModuleFibreCohomology f R U q) :=
    preservesColimitsOfShape_of_natIso (constantModuleFibreConstantIso f R U q).symm
  exact (ModuleCat.functorTensorEquivOfBasis
    (constantModuleFibreCohomology f R U q) (Module.Free.chooseBasis R M)).bijective

end AlgebraicGeometry.Scheme.EtaleCohomology
