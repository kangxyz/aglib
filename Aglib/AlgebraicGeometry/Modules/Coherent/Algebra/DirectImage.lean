/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Coherent.Algebra.SectionLaws
public import Aglib.AlgebraicGeometry.Modules.Pullback.Tensor.Basic
public import Aglib.AlgebraicGeometry.Modules.StructureSheaf.Pushforward
public import Aglib.AlgebraicGeometry.Modules.Coherent.Pushforward.Finite.Quotient

/-!
# The native commutative direct-image structure algebra

For every scheme morphism the original module `f_* O` carries its native
commutative monoid structure. Its multiplication is the original direct-image
tensor comparison followed by the source structure-module multiplication.
Finite morphisms give finite-type underlying modules, without a flatness premise.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory MonoidalCategory Opposite

namespace AlgebraicGeometry.Scheme.Modules.Algebra

variable {Y X : Scheme.{u}} (f : Y ⟶ X)

/-- The original structure map into the direct-image structure module. -/
abbrev pushforwardStructureOne : 𝟙_ X.Modules ⟶ pushforwardStructureSheaf f :=
  SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom

/-- Multiplication on the actual direct-image module uses the original tensor comparison. -/
def pushforwardStructureMul :
    Scheme.Modules.Hom (X := X)
      (tensorSheaf X (pushforwardStructureSheaf f) (pushforwardStructureSheaf f))
      (pushforwardStructureSheaf f) :=
  pushforwardTensorMap f (𝟙_ Y.Modules) (𝟙_ Y.Modules) ≫
    (pushforward f).map (λ_ (𝟙_ Y.Modules)).hom

/-- The direct-image unit component is the original scheme structure map. -/
@[simp] theorem pushforwardStructureOne_app (U : X.Opens) (r : Γ(X, U)) :
    (pushforwardStructureOne f).app U r = (f.app U) r := rfl

/-- The direct-image multiplication is ordinary source-section multiplication. -/
@[simp] theorem pushforwardStructureMul_app (U : X.Opens)
    (m n : Γ(Y, f ⁻¹ᵁ U)) :
    (pushforwardStructureMul f).app U
      (moduleTensorSection X (pushforwardStructureSheaf f) (pushforwardStructureSheaf f) U m n) =
      m * n := by
  change (λ_ (𝟙_ Y.Modules)).hom.val.app (op (f ⁻¹ᵁ U))
    ((pushforwardTensorMap f (𝟙_ Y.Modules) (𝟙_ Y.Modules)).val.app (op U) _) = _
  exact (congrArg ((λ_ (𝟙_ Y.Modules)).hom.val.app (op (f ⁻¹ᵁ U)))
    (pushforwardTensorMap_tmul f (𝟙_ Y.Modules) (𝟙_ Y.Modules) (op U) m n)).trans
      (tensorLeftUnitIso_hom_section Y (𝟙_ Y.Modules) (f ⁻¹ᵁ U) m n)

/-- Every direct-image structure module is a native monoid object. -/
@[instance_reducible]
def pushforwardStructureSheafMonObj : MonObj (C := X.Modules) (pushforwardStructureSheaf f) := by
  let hSectionMonoids : ∀ U : X.Opens, CommMonoid Γ(pushforwardStructureSheaf f, U) :=
    fun U => inferInstanceAs (CommMonoid Γ(Y, f ⁻¹ᵁ U))
  exact monObjOfSectionMonoids (pushforwardStructureSheaf f)
    (pushforwardStructureOne f) (pushforwardStructureMul f)
    (fun U => map_one (f.app U).hom) (pushforwardStructureMul_app f)

attribute [instance] pushforwardStructureSheafMonObj

/-- The native direct-image structure monoid is commutative. -/
instance pushforwardStructureSheafIsCommMonObj :
    IsCommMonObj (C := X.Modules) (pushforwardStructureSheaf f) := by
  let hSectionMonoids : ∀ U : X.Opens, CommMonoid Γ(pushforwardStructureSheaf f, U) :=
    fun U => inferInstanceAs (CommMonoid Γ(Y, f ⁻¹ᵁ U))
  exact isCommMonObjOfSectionMonoids (pushforwardStructureSheaf f)
    (pushforwardStructureOne f) (pushforwardStructureMul f)
    (fun U => map_one (f.app U).hom) (pushforwardStructureMul_app f)

/-- The same native module, bundled as a commutative algebra object. -/
def pushforwardStructureAlgebra : CommMon X.Modules :=
  ⟨pushforwardStructureSheaf f⟩

/-- Finite direct images of structure modules are affine-locally finite type.
No flatness of the map to the ambient scheme is required. -/
theorem affineLocallyFiniteType_pushforwardStructureSheaf [IsFinite f] :
    QuasiCoherent.affineLocallyFiniteType X (pushforwardStructureSheaf f) :=
  QuasiCoherent.FiniteMorphism.affineLocallyFiniteType_pushforward f
    (Coherent.Support.unit_coherent Y)

end AlgebraicGeometry.Scheme.Modules.Algebra
