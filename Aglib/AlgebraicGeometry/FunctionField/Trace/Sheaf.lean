/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.FunctionField.SectionRange
public import Aglib.AlgebraicGeometry.FunctionField.Trace
public import Aglib.AlgebraicGeometry.Modules.StructureSheaf.Pushforward

/-!
# The original field trace as a structure-linear sheaf morphism

The affine field-trace values extend uniquely to all nonempty opens by
the original stalk criterion for regular sections. On the empty open the
map is zero. The resulting maps commute with the actual restrictions and
give the original structure-linear morphism `f_* O_X → O_Y`.

The construction retains the original field map, section maps and
scalar actions; no separability or local freeness is
assumed. The fixed Gram-matrix and cohomology bound are later consumers.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.Scheme

universe u

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]

/-- Restriction retains the original value in the same function field. -/
theorem germToFunctionField_restrict {U V : X.Opens} (i : U ⟶ V)
    [Nonempty U] [Nonempty V] (s : Γ(X, V)) :
    X.germToFunctionField U (X.presheaf.map i.op s) =
      X.germToFunctionField V s := by
  have hη : genericPoint X ∈ U :=
    ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr
      (by simpa using (inferInstance : Nonempty U))
  exact X.presheaf.germ_res_apply i (genericPoint X) hη s

variable (f : X ⟶ Y) [IsDominant f] [IsFinite f]

/-- The same original field trace is regular on every nonempty open. -/
theorem exists_finiteSectionTrace_value (hNormal : NormalStalks Y)
    (U : Y.Opens) [Nonempty U] (s : Γ(X, f ⁻¹ᵁ U)) :
    letI : Nonempty (f ⁻¹ᵁ U) := nonempty_preimage_of_isDominant f U
    letI := functionFieldMapAlgebra f
    ∃ a : Γ(Y, U), Y.germToFunctionField U a =
      Algebra.trace Y.functionField X.functionField
        (X.germToFunctionField (f ⁻¹ᵁ U) s) := by
  let : Nonempty (f ⁻¹ᵁ U) := nonempty_preimage_of_isDominant f U
  let := functionFieldMapAlgebra f
  apply (mem_range_germToFunctionField_iff_stalk Y U _).mpr
  intro x
  obtain ⟨V, hV, hxV, hVU⟩ := exists_isAffineOpen_mem_and_subset x.property
  let : Nonempty V := ⟨⟨x.val, hxV⟩⟩
  let : Nonempty (f ⁻¹ᵁ V) := nonempty_preimage_of_isDominant f V
  let i : V ⟶ U := homOfLE hVU
  let j : (f ⁻¹ᵁ V) ⟶ (f ⁻¹ᵁ U) := (Opens.map f.base).map i
  let sV := X.presheaf.map j.op s
  refine ⟨Y.presheaf.germ V x.val hxV (finiteAffineSectionTrace f hNormal V hV sV), ?_⟩
  rw [algebraMap_germ_eq_germToFunctionField Y hxV,
    finiteAffineSectionTrace_germ f hNormal V hV]
  exact congrArg (Algebra.trace Y.functionField X.functionField)
    (germToFunctionField_restrict j s)

/-- The original field trace on an arbitrary nonempty open, linear for
the actual scalar map `f.app U`. -/
def finiteNonemptySectionTrace (hNormal : NormalStalks Y)
    (U : Y.Opens) [Nonempty U] :
    letI := (f.app U).hom.toAlgebra
    Γ(X, f ⁻¹ᵁ U) →ₗ[Γ(Y, U)] Γ(Y, U) := by
  letI : Nonempty (f ⁻¹ᵁ U) := nonempty_preimage_of_isDominant f U
  letI := functionFieldMapAlgebra f
  letI := (f.app U).hom.toAlgebra
  let t (s : Γ(X, f ⁻¹ᵁ U)) : Γ(Y, U) :=
    (exists_finiteSectionTrace_value f hNormal U s).choose
  have ht (s : Γ(X, f ⁻¹ᵁ U)) : Y.germToFunctionField U (t s) =
      Algebra.trace Y.functionField X.functionField
        (X.germToFunctionField (f ⁻¹ᵁ U) s) :=
    (exists_finiteSectionTrace_value f hNormal U s).choose_spec
  let gX := (X.germToFunctionField (f ⁻¹ᵁ U)).hom
  let gY := (Y.germToFunctionField U).hom
  let τ := Algebra.trace Y.functionField X.functionField
  refine { toFun := t, map_add' := ?_, map_smul' := ?_ }
  · intro s z
    apply Y.germToFunctionField_injective U
    calc
      gY (t (s + z)) = τ (gX (s + z)) := ht (s + z)
      _ = τ (gX s + gX z) := congrArg τ (map_add gX s z)
      _ = τ (gX s) + τ (gX z) := map_add τ (gX s) (gX z)
      _ = gY (t s) + gY (t z) := congrArg₂ (· + ·) (ht s).symm (ht z).symm
      _ = gY (t s + t z) := (map_add gY (t s) (t z)).symm
  · intro c s
    change t (f.app U c * s) = c * t s
    apply Y.germToFunctionField_injective U
    have hg := ConcreteCategory.congr_hom (functionFieldMap_germ_app f U) c
    change functionFieldMap f (Y.germToFunctionField U c) =
      X.germToFunctionField (f ⁻¹ᵁ U) (f.app U c) at hg
    calc
      gY (t (f.app U c * s)) = τ (gX (f.app U c * s)) := ht _
      _ = τ (gX (f.app U c) * gX s) := congrArg τ (map_mul gX _ _)
      _ = τ (functionFieldMap f (gY c) * gX s) := by rw [← hg]
      _ = gY c * τ (gX s) := by
        change τ ((gY c) • gX s) = (gY c) • τ (gX s)
        exact τ.map_smul _ _
      _ = gY c * gY (t s) := congrArg (gY c * ·) (ht s).symm
      _ = gY (c * t s) := (map_mul gY c (t s)).symm

/-- The nonempty-open map has the exact original field-trace value. -/
theorem finiteNonemptySectionTrace_germ (hNormal : NormalStalks Y)
    (U : Y.Opens) [Nonempty U] (s : Γ(X, f ⁻¹ᵁ U)) :
    letI : Nonempty (f ⁻¹ᵁ U) := nonempty_preimage_of_isDominant f U
    letI := functionFieldMapAlgebra f
    Y.germToFunctionField U (finiteNonemptySectionTrace f hNormal U s) =
      Algebra.trace Y.functionField X.functionField
        (X.germToFunctionField (f ⁻¹ᵁ U) s) :=
  (exists_finiteSectionTrace_value f hNormal U s).choose_spec

/-- The original section trace on every open, using zero on the empty open. -/
def finiteSectionTrace (hNormal : NormalStalks Y) (U : Y.Opens) :
    letI := (f.app U).hom.toAlgebra
    Γ(X, f ⁻¹ᵁ U) →ₗ[Γ(Y, U)] Γ(Y, U) := by
  classical
  letI := (f.app U).hom.toAlgebra
  exact if hU : Nonempty U then
    letI := hU
    finiteNonemptySectionTrace f hNormal U
  else 0

/-- On a nonempty open the all-open trace is the original field trace. -/
theorem finiteSectionTrace_germ (hNormal : NormalStalks Y)
    (U : Y.Opens) [hU : Nonempty U] (s : Γ(X, f ⁻¹ᵁ U)) :
    letI : Nonempty (f ⁻¹ᵁ U) := nonempty_preimage_of_isDominant f U
    letI := functionFieldMapAlgebra f
    Y.germToFunctionField U (finiteSectionTrace f hNormal U s) =
      Algebra.trace Y.functionField X.functionField
        (X.germToFunctionField (f ⁻¹ᵁ U) s) := by
  classical
  simpa only [finiteSectionTrace, dite_eq_left hU] using
    finiteNonemptySectionTrace_germ f hNormal U s

/-- The original trace commutes with the actual restriction maps. -/
theorem finiteSectionTrace_restrict (hNormal : NormalStalks Y)
    {U V : Y.Opens} (i : U ⟶ V) (s : Γ(X, f ⁻¹ᵁ V)) :
    finiteSectionTrace f hNormal U
        (X.presheaf.map ((Opens.map f.base).map i).op s) =
      Y.presheaf.map i.op (finiteSectionTrace f hNormal V s) := by
  classical
  by_cases hU : Nonempty U
  · let := hU
    let : Nonempty V := ⟨⟨hU.some.val, i.le hU.some.property⟩⟩
    let : Nonempty (f ⁻¹ᵁ U) := nonempty_preimage_of_isDominant f U
    let : Nonempty (f ⁻¹ᵁ V) := nonempty_preimage_of_isDominant f V
    let := functionFieldMapAlgebra f
    apply Y.germToFunctionField_injective U
    rw [finiteSectionTrace_germ f hNormal U,
      germToFunctionField_restrict i, finiteSectionTrace_germ f hNormal V]
    exact congrArg (Algebra.trace Y.functionField X.functionField)
      (germToFunctionField_restrict ((Opens.map f.base).map i) s)
  · apply TopCat.Presheaf.section_ext Y.sheaf
    intro x hx
    exact (hU ⟨⟨x, hx⟩⟩).elim

namespace Modules

/-- The ordinary finite-morphism trace, with the original structure action. -/
def finiteStructureTrace (hNormal : NormalStalks Y) :
    pushforwardStructureSheaf f ⟶ SheafOfModules.unit Y.ringCatSheaf := by
  let M : Y.Modules := pushforwardStructureSheaf f
  let N : Y.Modules := SheafOfModules.unit Y.ringCatSheaf
  let φ : M.presheaf ⟶ N.presheaf :=
    { app U := AddCommGrpCat.ofHom
        (finiteSectionTrace f hNormal U.unop).toAddMonoidHom
      naturality := by
        intro U V i
        ext s
        exact finiteSectionTrace_restrict f hNormal i.unop s }
  refine ⟨_root_.PresheafOfModules.homMk φ ?_⟩
  intro U r m
  change Γ(Y, U.unop) at r
  change Γ(X, f ⁻¹ᵁ U.unop) at m
  let := (f.app U.unop).hom.toAlgebra
  change finiteSectionTrace f hNormal U.unop (f.app U.unop r * m) =
    r * finiteSectionTrace f hNormal U.unop m
  exact (finiteSectionTrace f hNormal U.unop).map_smul r m

/-- Every component of the ordinary sheaf trace is the original section trace. -/
theorem finiteStructureTrace_app (hNormal : NormalStalks Y)
    (U : Y.Opens) (s : Γ(X, f ⁻¹ᵁ U)) :
    Hom.app (finiteStructureTrace f hNormal) U s = finiteSectionTrace f hNormal U s := rfl

end Modules

end AlgebraicGeometry.Scheme
