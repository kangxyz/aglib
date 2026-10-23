/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Fields.FiniteTrivialization
public import Aglib.AlgebraicGeometry.EtaleCohomology.H0.ConstantFullness
public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

/-! # Finite locally constant cokernels over fields

An actual map from a constant coefficient to a finite locally constant
coefficient has a finite locally constant literal cokernel. A finite Galois
trivialization reduces the map to an additive value map; preservation of the
actual cokernel identifies its pullback with the finite constant quotient.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Fields

universe u

attribute [local instance] hasSheafifyLarge

variable (E : Type u) [Field E]

/-- The actual cokernel of a map from any constant to a finite constant over a field
is constant with a finite additive value, including values in the larger universe. -/
theorem exists_finite_constant_cokernel
    (A : Type u) [AddCommGroup A]
    (B : AddCommGrpCat.{u + 1}) [Finite B]
    (f : ConstantFinite.coefficient A (Spec (.of E)) ⟶
      (constantSheaf (smallEtaleTopology (Spec (.of E))) AddCommGrpCat.{u + 1}).obj B) :
    ∃ Q : AddCommGrpCat.{u + 1}, Finite Q ∧
      Nonempty (cokernel f ≅
        (constantSheaf (smallEtaleTopology (Spec (.of E))) AddCommGrpCat.{u + 1}).obj Q) := by
  let := Fintype.ofFinite B
  have : Small.{u} B := Small.mk'
    ((Fintype.equivFin B).trans (Equiv.ulift.{u}).symm)
  let D := Shrink.{u} B
  have : Finite D := Finite.of_equiv B (equivShrink B)
  let e : ConstantFinite.value D ≅ B :=
    AddEquiv.toAddCommGrpIso (AddEquiv.ulift.trans (Shrink.addEquiv (α := B)))
  let C := constantSheaf (smallEtaleTopology (Spec (.of E))) AddCommGrpCat.{u + 1}
  let : C.IsLeftAdjoint := (constantAdjunction (Spec (.of E))).isLeftAdjoint
  obtain ⟨g, hg⟩ := (ConstantFinite.constant_map_bijective (Spec (.of E)) A D).surjective
    (f ≫ (C.mapIso e).inv)
  let Q := cokernel g
  have : Finite Q := Finite.of_equiv
    (ConstantFinite.value D ⧸ AddMonoidHom.range g.hom)
    (Iso.addCommGroupIsoToAddEquiv (AddCommGrpCat.cokernelIsoQuotient g).symm).toEquiv
  refine ⟨Q, inferInstance, ⟨?_⟩⟩
  exact cokernel.mapIso f (C.map g) (Iso.refl _) (C.mapIso e).symm
    (by simpa using hg.symm) ≪≫ (PreservesCokernel.iso C g).symm

/-- A literal cokernel of any map from a constant coefficient to an
actual finite locally constant coefficient remains finite locally constant.
No monomorphism hypothesis or separable closedness of the field is needed. -/
theorem isFiniteLocallyConstant_cokernel_from_constant
    (A : Type u) [AddCommGroup A]
    (F : AbelianSheaf.{u, u + 1} (Spec (.of E))) (hF : IsFiniteLocallyConstant F)
    (f : ConstantFinite.coefficient A (Spec (.of E)) ⟶ F) :
    IsFiniteLocallyConstant (cokernel f) := by
  obtain ⟨L, B, hB, ⟨e⟩⟩ := exists_finiteGalois_trivialization E F hF
  let := hB
  let p := Spec.algebraMap E L
  let a := (inverseImageConstantIso p).app (ConstantFinite.value A)
  let g := a.inv ≫ (inverseImage p).map f ≫ e.hom
  obtain ⟨Q, hQ, ⟨q⟩⟩ := exists_finite_constant_cokernel L A B g
  let t : (inverseImage p).obj (cokernel f) ≅
      (constantSheaf (smallEtaleTopology (Spec (.of L))) AddCommGrpCat.{u + 1}).obj Q :=
    PreservesCokernel.iso (inverseImage p) f ≪≫
      cokernel.mapIso ((inverseImage p).map f) g a e (by simp [g]) ≪≫ q
  refine ⟨{
    index := PUnit.{u + 1}
    chart := fun _ => (Scheme.FiniteEtale.toEtale _).obj
      (Scheme.FiniteEtale.FieldGalois.Arbitrary.finiteFieldCover E L)
    covers := ?_
    value := fun _ => Q
    finite_value := fun _ => hQ
    trivialization := fun _ => t }⟩
  intro x
  refine ⟨PUnit.unit, (default : Spec (.of L)), ?_⟩
  change p (default : Spec (.of L)) = x
  exact Subsingleton.elim _ _

/-- Annihilation of the original target descends to its literal cokernel. -/
theorem killedBy_cokernel {X : Scheme.{u}} {F G : AbelianSheaf.{u, u + 1} X}
    (f : F ⟶ G) (n : ℕ) (hG : KilledBy n G) : KilledBy n (cokernel f) := by
  apply (cancel_epi (cokernel.π f)).mp
  rw [Preadditive.comp_nsmul, Category.comp_id, comp_zero]
  have h := congrArg (fun a => a ≫ cokernel.π f) hG
  simpa only [Preadditive.nsmul_comp, Category.id_comp, zero_comp] using h

end AlgebraicGeometry.Scheme.EtaleCohomology.Fields
