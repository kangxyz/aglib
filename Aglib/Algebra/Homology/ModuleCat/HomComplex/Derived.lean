/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.ModuleCat.HomComplex.Evaluation
public import Aglib.CategoryTheory.Linear.Opposite
public import Mathlib.Algebra.Homology.DerivedCategory.Linear
public import Mathlib.CategoryTheory.Localization.Linear

/-!
# The genuine fixed-coefficient derived dual and its evaluation

The native A-module-valued Hom complex with a supplied K-injective
coefficient is localized along actual A-quasi-isomorphisms. Its signed
A-linear evaluation descends through the original localization comparison.
No evaluation-isomorphism, biduality or trace hypothesis is used.
-/

@[expose] public section
noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive Opposite

universe u v w

attribute [local instance] CategoryTheory.Linear.opposite

namespace CochainComplex.HomComplex

variable {A : Type u} [CommRing A]

private theorem ofHom_smul {K L : CochainComplex (ModuleCat.{v} A) ℤ}
    (f : K ⟶ L) (a : A) : Cochain.ofHom (a • f) = a • Cochain.ofHom f := by
  apply Cochain.ext
  intro p q hpq
  simp only [Cochain.ofHom, Cochain.ofHoms, Cochain.mk_v, Cochain.smul_v,
    HomologicalComplex.smul_f_apply, Linear.smul_comp]

/-- The fixed-coefficient original Hom functor preserves the actual A-scalars. -/
instance moduleComplexFunctor_linear (J : CochainComplex (ModuleCat.{v} A) ℤ) :
    (moduleComplexFunctor A J).Linear A where
  map_smul {X Y} f a := by
    apply HomologicalComplex.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro x
    change (Cochain.ofHom (a • f.unop)).comp x (zero_add n) =
      a • (Cochain.ofHom f.unop).comp x (zero_add n)
    rw [ofHom_smul (K := Y.unop) (L := X.unop), Cochain.smul_comp]

variable [HasDerivedCategory.{w} (ModuleCat.{v} A)]

local instance derivedQ_op_linear :
    (DerivedCategory.Q (C := ModuleCat.{v} A)).op.Linear A where
  map_smul {X Y} f a := by
    apply Quiver.Hom.unop_inj
    change DerivedCategory.Q.map (a • (show Y.unop ⟶ X.unop from f.unop)) =
      a • DerivedCategory.Q.map f.unop
    exact DerivedCategory.Q.map_smul a f.unop

/-- K-injectivity proves that the actual A-Hom functor inverts the opposite
class of original A-quasi-isomorphisms after native localization. -/
theorem moduleComplexFunctor_inverts (J : CochainComplex (ModuleCat.{v} A) ℤ)
    [J.IsKInjective] :
    (HomologicalComplex.quasiIso (ModuleCat.{v} A) (.up ℤ)).op.IsInvertedBy
      (moduleComplexFunctor A J ⋙ DerivedCategory.Q) := by
  intro K L f hf
  let : QuasiIso f.unop := hf
  let : QuasiIso (precomp A f.unop J) := precomp_quasiIso A f.unop J
  change IsIso (DerivedCategory.Q.map (precomp A f.unop J))
  infer_instance

/-- The genuine A-derived dual with this actual fixed K-injective coefficient. -/
def derivedDual (J : CochainComplex (ModuleCat.{v} A) ℤ) [J.IsKInjective] :
    (DerivedCategory (ModuleCat.{v} A))ᵒᵖ ⥤ DerivedCategory (ModuleCat.{v} A) :=
  Localization.lift (moduleComplexFunctor A J ⋙ DerivedCategory.Q)
    (moduleComplexFunctor_inverts J) DerivedCategory.Q.op

/-- The comparison to the original A-chain-level dual, furnished by the
actual localization used to construct the derived functor. -/
def derivedDualFactors (J : CochainComplex (ModuleCat.{v} A) ℤ) [J.IsKInjective] :
    DerivedCategory.Q.op ⋙ derivedDual J ≅ moduleComplexFunctor A J ⋙ DerivedCategory.Q :=
  Localization.fac (moduleComplexFunctor A J ⋙ DerivedCategory.Q)
    (moduleComplexFunctor_inverts J) DerivedCategory.Q.op

/-- A-linearity descends from original source precomposition through the native
linear localization, without promoting an R-derived morphism to an A-derived one. -/
instance derivedDual_linear (J : CochainComplex (ModuleCat.{v} A) ℤ) [J.IsKInjective] :
    (derivedDual J).Linear A := by
  change (Localization.lift (moduleComplexFunctor A J ⋙ DerivedCategory.Q)
    (moduleComplexFunctor_inverts J) DerivedCategory.Q.op).Linear A
  exact (Localization.functor_linear_iff DerivedCategory.Q.op
    (HomologicalComplex.quasiIso (ModuleCat.{v} A) (.up ℤ)).op A
    (moduleComplexFunctor A J ⋙ DerivedCategory.Q) _).mp inferInstance

/-- The actual derived dual sends zero morphisms to zero, by its native A-linearity. -/
instance derivedDual_preservesZeroMorphisms
    (J : CochainComplex (ModuleCat.{v} A) ℤ) [J.IsKInjective] :
    (derivedDual J).PreservesZeroMorphisms where
  map_zero X Y := by
    have h := (derivedDual J).map_smul (0 : A) (0 : X ⟶ Y)
    simpa only [zero_smul] using h

/-- A comparison for contravariant functors induces the original comparison
for their doubles, with the first comparison reversed by rightOp. -/
def doubleComparison {C D : Type*} [Category* C] [Category* D]
    (Q : C ⥤ D) (B : Cᵒᵖ ⥤ C) (F : Dᵒᵖ ⥤ D)
    (e : Q.op ⋙ F ≅ B ⋙ Q) :
    Q ⋙ (F.rightOp ⋙ F) ≅ (B.rightOp ⋙ B) ⋙ Q := by
  let eOp : (Q.op ⋙ F).rightOp ≅ (B ⋙ Q).rightOp :=
    { hom := e.inv.rightOp
      inv := e.hom.rightOp
      hom_inv_id := by
        rw [← NatTrans.rightOp_comp, e.hom_inv_id, NatTrans.rightOp_id]
      inv_hom_id := by
        rw [← NatTrans.rightOp_comp, e.inv_hom_id, NatTrans.rightOp_id] }
  exact (Functor.associator Q F.rightOp F).symm ≪≫
    Functor.isoWhiskerRight eOp F ≪≫
    Functor.associator B.rightOp Q.op F ≪≫
    Functor.isoWhiskerLeft B.rightOp e ≪≫
    (Functor.associator B.rightOp B Q).symm

/-- The actual double-dual factorization preserves both occurrences of the
original single-dual localization comparison. -/
def derivedDoubleDualFactors (J : CochainComplex (ModuleCat.{v} A) ℤ) [J.IsKInjective] :
    DerivedCategory.Q ⋙ ((derivedDual J).rightOp ⋙ derivedDual J) ≅
      ((moduleComplexFunctor A J).rightOp ⋙ moduleComplexFunctor A J) ⋙ DerivedCategory.Q :=
  doubleComparison DerivedCategory.Q (moduleComplexFunctor A J) (derivedDual J)
    (derivedDualFactors J)

/-- The original signed A-evaluation descended to the actual derived category.
This constructs the morphism; its invertibility on R-perfect objects is a separate theorem. -/
def derivedEvaluation (J : CochainComplex (ModuleCat.{v} A) ℤ) [J.IsKInjective] :
    𝟭 (DerivedCategory (ModuleCat.{v} A)) ⟶ (derivedDual J).rightOp ⋙ derivedDual J := by
  let W := HomologicalComplex.quasiIso (ModuleCat.{v} A) (.up ℤ)
  let Q := DerivedCategory.Q (C := ModuleCat.{v} A)
  let B := moduleComplexFunctor A J
  let F := derivedDual J
  let : Localization.Lifting Q W Q (𝟭 _) := ⟨Functor.rightUnitor Q⟩
  let : Localization.Lifting Q W ((B.rightOp ⋙ B) ⋙ Q) (F.rightOp ⋙ F) :=
    ⟨derivedDoubleDualFactors J⟩
  exact Localization.liftNatTrans Q W Q ((B.rightOp ⋙ B) ⋙ Q) (𝟭 _) (F.rightOp ⋙ F)
    ((Functor.leftUnitor Q).inv ≫ Functor.whiskerRight (evaluationNatTrans J) Q)

/-- On each actual representative, the descended map is the original signed
chain evaluation followed by the original double-dual factorization inverse. -/
theorem derivedEvaluation_app_Q (J K : CochainComplex (ModuleCat.{v} A) ℤ)
    [J.IsKInjective] :
    (derivedEvaluation J).app (DerivedCategory.Q.obj K) =
      DerivedCategory.Q.map (evaluation K J) ≫ (derivedDoubleDualFactors J).inv.app K := by
  let e : DerivedCategory.Q.obj K ⟶
      DerivedCategory.Q.obj (moduleComplex A (moduleComplex A K J) J) :=
    DerivedCategory.Q.map (evaluation K J)
  let c : DerivedCategory.Q.obj (moduleComplex A (moduleComplex A K J) J) ⟶
      ((derivedDual J).rightOp ⋙ derivedDual J).obj (DerivedCategory.Q.obj K) :=
    (derivedDoubleDualFactors J).inv.app K
  unfold derivedEvaluation
  rw [Localization.liftNatTrans_app]
  change (𝟙 _) ≫ ((𝟙 _) ≫ e) ≫ c = e ≫ c
  simp only [Category.id_comp]

end CochainComplex.HomComplex
