/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Aglib.Algebra.Category.ModuleCat.Sheaf.Evaluation
public import Aglib.Topology.Sheaves.BasisExactness
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor

/-!
# Detecting module-complex exactness on original sections over a basis

Exactness and acyclicity of actual module-sheaf complexes are detected by
the native variable-ring section functors on any topological basis. For
integer cochains, the same basis criterion detects quasi-isomorphisms.
The proof forgets scalars through the native exact conservative functor
to additive sheaves and reuses the established additive-sheaf criterion.
There is no quasicoherence, boundedness or acyclicity premise on the terms.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite HomologicalComplex

namespace AlgebraicGeometry.Scheme.Modules.Complex

universe u w

variable {X : Scheme.{u}}

/-- The native evaluation is additive also when its source is the scheme module
category with its explicitly installed abelian structure. -/
instance sectionsEvaluation_additive (U : X.Opens) :
    (SheafOfModules.evaluation.{u} X.ringCatSheaf (op U) :
      X.Modules ⥤ ModuleCat.{u} (X.ringCatSheaf.obj.obj (op U))).Additive where
  map_add := by intros; rfl

/-- The same original evaluation preserves the installed zero morphisms of scheme
modules, so it acts directly on the original complexes. -/
instance sectionsEvaluation_preservesZeroMorphisms (U : X.Opens) :
    (SheafOfModules.evaluation.{u} X.ringCatSheaf (op U) :
      X.Modules ⥤ ModuleCat.{u} (X.ringCatSheaf.obj.obj (op U))).PreservesZeroMorphisms where
  map_zero := by intros; rfl

/-- The original section-complex exactness at a degree on a basis detects actual
module-sheaf exactness, in an arbitrary complex shape and index universe. -/
theorem exactAt_of_sections_on_basis {ι : Type w} {c : ComplexShape ι}
    (K : HomologicalComplex X.Modules c) (j : ι)
    {B : Set X.Opens} (hB : Opens.IsBasis B)
    (hK : ∀ U ∈ B,
      (((SheafOfModules.evaluation.{u} X.ringCatSheaf (op U)).mapHomologicalComplex c).obj
        K).ExactAt j) : K.ExactAt j := by
  let F : X.Modules ⥤ TopCat.Sheaf AddCommGrpCat.{u} X :=
    SheafOfModules.toSheaf.{u} X.ringCatSheaf
  let : F.Additive := ⟨by intros; rfl⟩
  let : PreservesFiniteLimits F := by
    change PreservesFiniteLimits (SheafOfModules.toSheaf.{u} X.ringCatSheaf)
    infer_instance
  let : PreservesFiniteColimits F := by
    change PreservesFiniteColimits (SheafOfModules.toSheaf.{u} X.ringCatSheaf)
    infer_instance
  let : F.PreservesHomology :=
    Functor.preservesHomology_of_preservesMonos_and_cokernels F
  let : F.Faithful := by
    change (SheafOfModules.toSheaf.{u} X.ringCatSheaf).Faithful
    infer_instance
  apply ((K.sc j).exact_map_iff_of_faithful F).mp
  apply TopCat.Sheaf.exactAt_of_sections_on_basis ((F.mapHomologicalComplex c).obj K) j hB
  intro U hU
  let E := SheafOfModules.evaluation.{u} X.ringCatSheaf (op U)
  let G := forget₂ (ModuleCat.{u} (X.ringCatSheaf.obj.obj (op U))) AddCommGrpCat.{u}
  change ((((E.mapHomologicalComplex c).obj K).sc j).map G).Exact
  exact (hK U hU).map G

/-- Acyclicity of original section complexes on a basis detects actual module-sheaf
acyclicity, with no termwise quasicoherence or finiteness premise. -/
theorem acyclic_of_sections_on_basis {ι : Type w} {c : ComplexShape ι}
    (K : HomologicalComplex X.Modules c) {B : Set X.Opens} (hB : Opens.IsBasis B)
    (hK : ∀ U ∈ B,
      (((SheafOfModules.evaluation.{u} X.ringCatSheaf (op U)).mapHomologicalComplex c).obj
        K).Acyclic) : K.Acyclic :=
  fun j => exactAt_of_sections_on_basis K j hB (fun U hU => hK U hU j)

/-- A map of actual integer cochain complexes is a quasi-isomorphism if its original
variable-ring section maps are quasi-isomorphisms on every member of a basis. -/
theorem quasiIso_of_sections_on_basis {K L : CochainComplex X.Modules ℤ} (φ : K ⟶ L)
    {B : Set X.Opens} (hB : Opens.IsBasis B)
    (hφ : ∀ U ∈ B, QuasiIso
      (((SheafOfModules.evaluation.{u} X.ringCatSheaf (op U)).mapHomologicalComplex
        (.up ℤ)).map φ)) : QuasiIso φ := by
  let F : X.Modules ⥤ TopCat.Sheaf AddCommGrpCat.{u} X :=
    SheafOfModules.toSheaf.{u} X.ringCatSheaf
  let : F.Additive := ⟨by intros; rfl⟩
  let : PreservesFiniteLimits F := by
    change PreservesFiniteLimits (SheafOfModules.toSheaf.{u} X.ringCatSheaf)
    infer_instance
  let : PreservesFiniteColimits F := by
    change PreservesFiniteColimits (SheafOfModules.toSheaf.{u} X.ringCatSheaf)
    infer_instance
  let : F.PreservesHomology :=
    Functor.preservesHomology_of_preservesMonos_and_cokernels F
  let : F.ReflectsIsomorphisms := by
    change (SheafOfModules.toSheaf.{u} X.ringCatSheaf).ReflectsIsomorphisms
    infer_instance
  apply (quasiIso_map_iff_of_preservesHomology φ F).mp
  apply TopCat.Sheaf.quasiIso_of_sections_on_basis _ hB
  intro U hU
  let E := SheafOfModules.evaluation.{u} X.ringCatSheaf (op U)
  let G := forget₂ (ModuleCat.{u} (X.ringCatSheaf.obj.obj (op U))) AddCommGrpCat.{u}
  let : QuasiIso ((E.mapHomologicalComplex (.up ℤ)).map φ) := hφ U hU
  change QuasiIso ((G.mapHomologicalComplex (.up ℤ)).map
    ((E.mapHomologicalComplex (.up ℤ)).map φ))
  infer_instance

end AlgebraicGeometry.Scheme.Modules.Complex
