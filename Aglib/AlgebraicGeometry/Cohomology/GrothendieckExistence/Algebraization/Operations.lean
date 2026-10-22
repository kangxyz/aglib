/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.Algebraization.CompletionMaps
public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.Proper
public import Aglib.AlgebraicGeometry.Modules.Coherent.Algebra.Tensor
public import Aglib.AlgebraicGeometry.Modules.Coherent.Pushforward.Finite.Quotient

/-! # Algebraizing the original formal algebra operations

Multiplication and the unit descend through the original ideal-sheaf quotient
units. Full faithfulness lifts these maps. Native monoid laws are then detected
on coherent sources by the original stage maps. No monoidal structure on adic
systems, completion tensor comparison, or relative spectrum is required.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open scoped MonObj

namespace CategoryTheory

universe v₁ v₂ u₁ u₂
variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
  {J : Type u₂} [Category.{v₂} J] (F : J ⥤ C)
  [∀ j, MonObj (F.obj j)]
  [∀ i j (g : i ⟶ j), IsMonHom (F.map g)]

/-- The original stage units form a compatible family. -/
def algebraUnitFamily : (Functor.const J).obj (𝟙_ C) ⟶ F where
  app j := η[F.obj j]
  naturality i j g := by simp

/-- Multiplication composed with the entire original stage-map family. -/
def algebraMultiplicationFamily {M : C}
    (q : (Functor.const J).obj M ⟶ F) :
    (Functor.const J).obj (M ⊗ M) ⟶ F where
  app j := (q.app j ⊗ₘ q.app j) ≫ μ[F.obj j]
  naturality i j g := by
    have hq := q.naturality g
    change 𝟙 M ≫ q.app j = q.app i ≫ F.map g at hq
    rw [Category.id_comp] at hq
    change 𝟙 (M ⊗ M) ≫ (q.app j ⊗ₘ q.app j) ≫ μ[F.obj j] =
      ((q.app i ⊗ₘ q.app i) ≫ μ[F.obj i]) ≫ F.map g
    simp only [Category.id_comp, Category.assoc, IsMonHom.mul_hom,
      tensorHom_comp_tensorHom_assoc, hq]

variable [BraidedCategory C] [∀ j, IsCommMonObj (F.obj j)]

/-- Reconstruct the whole original-map algebra certificate from two lifted
compatible families. All monoidal calculations precede sheaf specialization. -/
def commMonOfLiftedFamilies {M : C} (q : (Functor.const J).obj M ⟶ F)
    (one : { f : 𝟙_ C ⟶ M //
      (Functor.const J).map f ≫ q = algebraUnitFamily F })
    (mul : { f : M ⊗ M ⟶ M //
      (Functor.const J).map f ≫ q = algebraMultiplicationFamily F q })
    (hM : JointlyDetects (fun j => q.app j) M)
    (hTensor : JointlyDetects (fun j => q.app j) (M ⊗ M))
    (hTriple : JointlyDetects (fun j => q.app j) ((M ⊗ M) ⊗ M)) :
    JointDetectionCommMonData (fun j => q.app j) :=
  commMonOfJointDetection (fun j => q.app j) one.val mul.val
    (fun j => NatTrans.congr_app one.property j)
    (fun j => NatTrans.congr_app mul.property j) hM hTensor hTriple

end CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules.Coherent

universe u
variable {X : Scheme.{u}} [IsLocallyNoetherian X] {K : X.IdealSheafData}

/-- Native commutative algebra structures on an adic system, with the actual
transition maps preserving both operations. This adds no formal tensor. -/
class AdicAlgebraStructure (F : AdicSystem X K) where
  mon : ∀ n : ℕᵒᵖ, MonObj (F.obj.obj n)
  comm : ∀ n : ℕᵒᵖ, @IsCommMonObj X.Modules _ _ _ (F.obj.obj n) (mon n)
  map : ∀ m n : ℕᵒᵖ, ∀ g : m ⟶ n,
    @IsMonHom X.Modules _ _ (F.obj.obj m) (F.obj.obj n) (mon m) (mon n) (F.obj.map g)

attribute [instance_reducible] AdicAlgebraStructure.mon
attribute [instance] AdicAlgebraStructure.mon AdicAlgebraStructure.comm
  AdicAlgebraStructure.map

/-- A coherent native algebra together with the specified original formal
comparison and the entire algebra-map certificate for its quotient maps. -/
structure AdicAlgebraizationData (F : AdicSystem X K) [AdicAlgebraStructure F] where
  /-- The algebraized coherent module underlying the native algebra. -/
  coherent : X.CoherentSheaf
  /-- The specified comparison from original coherent completion to the given adic system. -/
  beta : (completionFunctor X K).obj coherent ≅ F
  /-- The native algebra operations and their preservation by every original quotient map. -/
  operations : JointDetectionCommMonData
    (fun n => (originalCompletionMaps K beta).app n)

/-- Algebraize both operations over an already specified coherent realization.
The original comparison is retained literally in the result. -/
def algebraizationDataOfComparison
    (h : (completionFunctor X K).FullyFaithful)
    {F : AdicSystem X K} [AdicAlgebraStructure F]
    (M : X.CoherentSheaf) (beta : (completionFunctor X K).obj M ≅ F) :
    AdicAlgebraizationData F := by
  let Q := originalCompletionMaps K beta
  let U : X.CoherentSheaf := ⟨𝟙_ X.Modules, Support.unit_coherent X⟩
  let T : X.CoherentSheaf := ⟨M.obj ⊗ M.obj,
    QuasiCoherent.affineLocallyFiniteType_tensor M.obj M.obj M.property M.property⟩
  let TT : X.CoherentSheaf := ⟨T.obj ⊗ M.obj,
    QuasiCoherent.affineLocallyFiniteType_tensor T.obj M.obj T.property M.property⟩
  let one := originalCompletionLiftData K h beta U (algebraUnitFamily F.obj)
  let mul := originalCompletionLiftData K h beta T (algebraMultiplicationFamily F.obj Q)
  exact ⟨M, beta, commMonOfLiftedFamilies F.obj Q
    ⟨one.val.hom, one.property⟩ ⟨mul.val.hom, mul.property⟩
    (originalCompletionMaps_jointlyDetects K h beta M)
    (originalCompletionMaps_jointlyDetects K h beta T)
    (originalCompletionMaps_jointlyDetects K h beta TT)⟩

namespace AdicAlgebraizationData

variable {F : AdicSystem X K} [AdicAlgebraStructure F] (d : AdicAlgebraizationData F)

/-- The algebraized object is a native commutative monoid of module sheaves. -/
def algebra : CommMon X.Modules where
  X := d.coherent.obj
  mon := d.operations.mon
  comm := d.operations.comm

/-- The complete original stage-map family, including transition naturality. -/
abbrev quotientMaps : (Functor.const ℕᵒᵖ).obj d.algebra.X ⟶ F.obj :=
  originalCompletionMaps K d.beta

/-- The whole stage-map family is literally the original quotient unit followed
by the specified formal comparison. -/
theorem quotientMaps_original :
    d.quotientMaps = idealSheafQuotientTowerUnit X K d.coherent.obj ≫ d.beta.hom.hom := rfl

/-- Every original stage map preserves the algebraized operations. -/
instance instIsMonHomQuotientMaps (n : ℕᵒᵖ) :
    IsMonHom (show d.algebra.X ⟶ F.obj.obj n from d.quotientMaps.app n) :=
  d.operations.map n

/-- Coherence belongs to the actual underlying native algebra object. -/
theorem algebra_coherent : QuasiCoherent.affineLocallyFiniteType X d.algebra.X :=
  d.coherent.property

end AdicAlgebraizationData
end AlgebraicGeometry.Scheme.Modules.Coherent

namespace AlgebraicGeometry.Scheme.Cohomology

open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Coherent

universe u
variable {A : Type u} [CommRing A] [IsNoetherianRing A]
  (I : Ideal A) [IsAdicComplete I A] {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of A)) [IsProper f]

/-- Proper Grothendieck existence algebraizes native commutative algebra
operations, retaining the original formal isomorphism and all its stage maps. -/
def properAdicAlgebraization :
    letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
    ∀ (F : AdicSystem X (idealThickeningIdealSheaf f I)) [AdicAlgebraStructure F],
      AdicAlgebraizationData F := by
  letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  intro F _
  let e := properCompletionEquivalence I f
  exact algebraizationDataOfComparison (completionFunctorFullyFaithful I f)
    (e.inverse.obj F) (e.counitIso.app F)

end AlgebraicGeometry.Scheme.Cohomology
