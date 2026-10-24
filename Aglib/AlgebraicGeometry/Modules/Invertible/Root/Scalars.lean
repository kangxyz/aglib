/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Invertible.ScalarAutomorphisms
public import Aglib.AlgebraicGeometry.Modules.Invertible.DualTensorEquivalence

/-! # Actual scalar coordinates for line-bundle automorphisms

The original tensor-by-dual equivalence and actual dual evaluation identify
every automorphism of a line bundle with a global unit. Its inverse is the
original sectionwise scalar isomorphism. Original scheme pullback sends
scalar maps to their original pulled-back sections.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.Invertible.TrivializedPower

namespace AlgebraicGeometry.Scheme.Modules.Invertible.Root

universe u

variable (X : Scheme.{u}) (L : LineBundle X)

/-- Tensor the actual automorphism with the actual dual and use actual evaluation. -/
def tensorUnitAut (e : L.val ≅ L.val) :
    SheafOfModules.unit X.ringCatSheaf ≅ SheafOfModules.unit X.ringCatSheaf :=
  (dualEvaluationIso X L).symm ≪≫
    (lineBundleDualTensorEquivalence X L).functor.mapIso e ≪≫ dualEvaluationIso X L

private theorem tensorScalar (a : Γ(X, ⊤)) :
    tensorSheafMap X (𝟙 (dualLineBundle X L).val) (scalarMap X L.val a) =
      scalarMap X (tensorSheaf X (dualLineBundle X L).val L.val) a := by
  rw [← ScalarAutomorphisms.scalarMap_one X (dualLineBundle X L).val]
  simpa only [one_mul] using
    ScalarAutomorphisms.tensorSheafMap_scalar X (dualLineBundle X L).val L.val 1 a

/-- The unit coordinate agrees with the original scalar on the original structure module. -/
theorem tensorUnitAut_scalar (a : Γ(X, ⊤)ˣ) :
    tensorUnitAut X L (ScalarAutomorphisms.scalarIso X L.val a) =
      ScalarAutomorphisms.scalarIso X (SheafOfModules.unit X.ringCatSheaf) a := by
  apply CategoryTheory.Iso.ext
  change (dualEvaluationIso X L).inv ≫
      tensorSheafMap X (𝟙 (dualLineBundle X L).val) (scalarMap X L.val a) ≫
        (dualEvaluationIso X L).hom =
    scalarMap X (SheafOfModules.unit X.ringCatSheaf) a
  rw [tensorScalar, ScalarAutomorphisms.scalarMap_naturality,
    CategoryTheory.Iso.inv_hom_id_assoc]

/-- The global unit attached to the original tensor/evaluation coordinate. -/
def autUnit (e : L.val ≅ L.val) : Γ(X, ⊤)ˣ :=
  unitOfIso X (tensorUnitAut X L e)

/-- Every original line-bundle automorphism is its actual scalar isomorphism. -/
theorem aut_eq_scalar (e : L.val ≅ L.val) :
    e = ScalarAutomorphisms.scalarIso X L.val (autUnit X L e) := by
  apply CategoryTheory.Iso.ext
  apply (lineBundleDualTensorEquivalence X L).functor.map_injective
  have h := ScalarAutomorphisms.unitOfIso_hom X (tensorUnitAut X L e)
  have hs := congrArg CategoryTheory.Iso.hom (tensorUnitAut_scalar X L (autUnit X L e))
  have ht := h.trans hs.symm
  change (dualEvaluationIso X L).inv ≫
      ((lineBundleDualTensorEquivalence X L).functor.map e.hom ≫
        (dualEvaluationIso X L).hom) =
    (dualEvaluationIso X L).inv ≫
      ((lineBundleDualTensorEquivalence X L).functor.map
        (ScalarAutomorphisms.scalarIso X L.val (autUnit X L e)).hom ≫
        (dualEvaluationIso X L).hom) at ht
  exact (cancel_mono (dualEvaluationIso X L).hom).mp
    ((cancel_epi (dualEvaluationIso X L).inv).mp ht)

/-- Original automorphisms and original global units, with original scalar inverse. -/
def autUnitEquiv : (L.val ≅ L.val) ≃ Γ(X, ⊤)ˣ where
  toFun := autUnit X L
  invFun := ScalarAutomorphisms.scalarIso X L.val
  left_inv e := (aut_eq_scalar X L e).symm
  right_inv a := by
    change unitOfIso X (tensorUnitAut X L (ScalarAutomorphisms.scalarIso X L.val a)) = a
    rw [tensorUnitAut_scalar]
    exact (ScalarAutomorphisms.unitAutoEquiv X).right_inv a

/-- Actual geometric pullback of a scalar map uses the original global section map. -/
theorem pullback_scalarMap {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Y.Modules)
    (a : Γ(Y, ⊤)) :
    (Scheme.Modules.pullback f).map (scalarMap Y M a) =
      scalarMap X ((Scheme.Modules.pullback f).obj M) (f.appTop a) := by
  let A := Scheme.Modules.pullbackPushforwardAdjunction f
  let P := Scheme.Modules.pullback f
  apply (A.homEquiv M (P.obj M)).injective
  have hleft := A.homEquiv_naturality_left (scalarMap Y M a) (𝟙 (P.obj M))
  have hright := A.homEquiv_naturality_right (𝟙 (P.obj M))
    (scalarMap X (P.obj M) (f.appTop a))
  rw [Category.comp_id, Adjunction.homEquiv_id] at hleft
  rw [Category.id_comp, Adjunction.homEquiv_id] at hright
  rw [hleft, hright]
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro m
  let ηm : (P.obj M).val.obj (Opposite.op (f ⁻¹ᵁ U.unop)) :=
    (A.unit.app M).val.app U m
  change (A.unit.app M).val.app U
      (Y.presheaf.map (homOfLE le_top : U.unop ⟶ ⊤).op a • m) =
    X.presheaf.map (homOfLE le_top : (f ⁻¹ᵁ U.unop) ⟶ ⊤).op (f.appTop a) • ηm
  rw [((A.unit.app M).val.app U).hom.map_smul]
  change f.app U.unop (Y.presheaf.map (homOfLE le_top : U.unop ⟶ ⊤).op a) • ηm =
    X.presheaf.map (homOfLE le_top : (f ⁻¹ᵁ U.unop) ⟶ ⊤).op (f.appTop a) • ηm
  congr 1
  exact ConcreteCategory.congr_hom
    (f.toLRSHom.c.naturality (homOfLE le_top : U.unop ⟶ ⊤).op) a

end AlgebraicGeometry.Scheme.Modules.Invertible.Root
