/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Fields.FiniteCokernel

/-! # Cokernels of arbitrary finite locally constant coefficients over fields

Trivializing the source over a finite Galois field cover reduces the actual
map to the constant-source theorem. The resulting local charts compose with
that same field cover; the descended coefficient is the literal cokernel.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Fields

universe u

attribute [local instance] hasSheafifyLarge

/-- Local trivializations on an actual surjective etale cover give local
trivializations of the original coefficient, by composing the same charts. -/
theorem isFiniteLocallyConstant_of_etale_pullback
    {X Y : Scheme.{u}} (p : Y ⟶ X) [Etale p] (hp : Function.Surjective p)
    (F : AbelianSheaf.{u, u + 1} X)
    (hF : IsFiniteLocallyConstant ((inverseImage p).obj F)) :
    IsFiniteLocallyConstant F := by
  obtain ⟨t⟩ := hF
  refine ⟨{
    index := t.index
    chart := fun i => Scheme.Etale.mk ((t.chart i).hom ≫ p)
    covers := ?_
    value := t.value
    finite_value := t.finite_value
    trivialization := fun i =>
      (inverseImageComp p (t.chart i).hom).app F ≪≫ t.trivialization i }⟩
  intro x
  obtain ⟨y, rfl⟩ := hp x
  obtain ⟨i, z, hz⟩ := t.covers y
  exact ⟨i, z, by change p ((t.chart i).hom z) = p y; rw [hz]⟩

/-- The literal cokernel of every actual map of finite locally constant
coefficients over an arbitrary field is finite locally constant. -/
theorem isFiniteLocallyConstant_cokernel
    (E : Type u) [Field E]
    (F G : AbelianSheaf.{u, u + 1} (Spec (.of E)))
    (hF : IsFiniteLocallyConstant F) (hG : IsFiniteLocallyConstant G) (f : F ⟶ G) :
    IsFiniteLocallyConstant (cokernel f) := by
  obtain ⟨L, B, hB, ⟨e⟩⟩ := exists_finiteGalois_trivialization E F hF
  let := hB
  let := Fintype.ofFinite B
  have : Small.{u} B := Small.mk'
    ((Fintype.equivFin B).trans (Equiv.ulift.{u}).symm)
  let D := Shrink.{u} B
  have : Finite D := Finite.of_equiv B (equivShrink B)
  let d : ConstantFinite.value D ≅ B :=
    AddEquiv.toAddCommGrpIso (AddEquiv.ulift.trans (Shrink.addEquiv (α := B)))
  let p := Spec.algebraMap E L
  let C := constantSheaf (smallEtaleTopology (Spec (.of L))) AddCommGrpCat.{u + 1}
  let a := e ≪≫ C.mapIso d.symm
  let g := a.inv ≫ (inverseImage p).map f
  have hg : IsFiniteLocallyConstant (cokernel g) :=
    isFiniteLocallyConstant_cokernel_from_constant L D ((inverseImage p).obj G)
      (isFiniteLocallyConstant_pullback p hG) g
  let q : (inverseImage p).obj (cokernel f) ≅ cokernel g :=
    PreservesCokernel.iso (inverseImage p) f ≪≫
      cokernel.mapIso ((inverseImage p).map f) g a (Iso.refl _) (by simp [g])
  have hpG : IsFiniteLocallyConstant ((inverseImage p).obj (cokernel f)) :=
    (isFiniteLocallyConstant_iff_of_iso q).mpr hg
  let : Etale p :=
    (Scheme.FiniteEtale.FieldGalois.Arbitrary.finiteFieldCover E L).property.2
  exact isFiniteLocallyConstant_of_etale_pullback p
    (fun x => ⟨default, Subsingleton.elim _ _⟩) (cokernel f) hpG

end AlgebraicGeometry.Scheme.EtaleCohomology.Fields
