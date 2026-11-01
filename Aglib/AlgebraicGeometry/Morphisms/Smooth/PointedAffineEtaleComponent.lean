/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.Smooth.StandardSectionComponentBaseChange
public import Aglib.AlgebraicGeometry.Morphisms.Smooth.RationalPoint
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.Descent.FiniteFieldPoint
public import Aglib.AlgebraicGeometry.Properties.Noetherian.LocallyConnected
public import Aglib.AlgebraicGeometry.Spec.ResidueField
public import Aglib.RingTheory.Smooth.SeparableResiduePointEtaleNeighborhood
public import Mathlib.FieldTheory.IsSepClosed

/-! # A genuine etale section component above an original affine point

The original point lifts to the separable closure of its actual base residue
field. A rational point in its same original connected component descends by
the existing finite-field point theorem. The genuine etale residue-neighborhood
producer supplies the section; the original component relation is retained
through the native pullback map and literal locus preimage. The original
point need not itself have finite residue field.
-/

@[expose] public noncomputable section
open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme
universe u

/-- Every original point of a standard smooth affine family belongs to the
section component after one genuine etale affine base change. All points,
sections and projections in the conclusion are the original native ones. -/
theorem exists_pointed_affine_etale_section_component
    (R B : Type u) [CommRing R] [CommRing B] [Algebra R B]
    (n : ℕ) [Algebra.IsStandardSmoothOfRelativeDimension n R B]
    (x : Spec (.of B)) :
    ∃ (T : Type u) (_ : CommRing T) (_ : Algebra R T),
      Algebra.Etale R T ∧ ∃ (ε : B →ₐ[R] T)
        (y : (pullback (Spec.algebraMap R B) (Spec.algebraMap R T) : Scheme.{u})),
        pullback.fst (Spec.algebraMap R B) (Spec.algebraMap R T) y = x ∧
        y ∈ sectionComponentLocus
          (pullback.snd (Spec.algebraMap R B) (Spec.algebraMap R T))
          (rationalPointBaseChangeSection ε) (rationalPointBaseChangeSection_snd ε) := by
  let f : Spec (.of B) ⟶ Spec (.of R) := Spec.algebraMap R B
  let : SmoothOfRelativeDimension n f := by
    change SmoothOfRelativeDimension n (Spec.map (CommRingCat.ofHom (algebraMap R B)))
    rw [HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension n)]
    apply RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso
    exact (RingHom.isStandardSmoothOfRelativeDimension_algebraMap n).mpr inferInstance
  let : Smooth f := SmoothOfRelativeDimension.smooth n f
  let : Algebra.IsStandardSmooth R B :=
    Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth (R := R) (S := B) n
  let p : Spec (.of R) := f x
  let : p.asIdeal.IsPrime := p.isPrime
  let k := p.asIdeal.ResidueField
  let Ω := SeparableClosure k
  let bk : Spec (.of k) ⟶ Spec (.of R) := Spec.algebraMap R k
  let β : Spec (.of Ω) ⟶ Spec (.of R) := Spec.algebraMap k Ω ≫ bk
  let η : Spec (.of Ω) := IsLocalRing.closedPoint Ω
  have hη : β η = p := by
    change bk ((Spec.algebraMap k Ω) η) = p
    rw [Subsingleton.elim ((Spec.algebraMap k Ω) η) (IsLocalRing.closedPoint k)]
    exact Spec.map_algebraMap_residueField_closedPoint (A := .of R) p.asIdeal
  let Z : Scheme.{u} := pullback f β
  let zfst : Z ⟶ Spec (.of B) := pullback.fst f β
  let zq : Z ⟶ Spec (.of Ω) := pullback.snd f β
  obtain ⟨z, hzx, _⟩ := Scheme.Pullback.exists_preimage_pullback
    (f := f) (g := β) x η hη.symm
  let : Smooth zq := inferInstanceAs (Smooth (pullback.snd f β))
  let : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian zq
  let C : Z.Opens := ⟨connectedComponent z, isClopen_connectedComponent.2⟩
  obtain ⟨o, ho, hom⟩ := exists_section_mem_open_of_smooth_of_isSepClosed Ω zq C
    ⟨z, mem_connectedComponent⟩
  have hzcomp : z ∈ connectedComponent (o η) := by
    rw [← connectedComponent_eq hom]
    exact mem_connectedComponent
  have hoover : (o ≫ zfst) ≫ f = Spec.algebraMap k Ω ≫ bk := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, ho, Category.id_comp]
  obtain ⟨s, a, ha, he⟩ := FiniteEtale.FieldCoverDescent.exists_finite_field_point
    k Ω f bk (o ≫ zfst) hoover
  let F := FiniteEtale.FieldLimit.finiteField k Ω s
  let : Algebra R F := Algebra.restrictScalars R k F
  let : IsScalarTower R k F := IsScalarTower.of_algebraMap_eq' rfl
  have hRF : Spec.algebraMap k F ≫ bk = Spec.algebraMap R F :=
    Spec.map_algHom_algebraMap (IsScalarTower.toAlgHom R k F)
  have haR : a ≫ f = Spec.algebraMap R F := ha.trans hRF
  let ψ : B →ₐ[R] F := Spec.homEquivAlgHom ⟨a, haR⟩
  have hψ : Spec.map (CommRingCat.ofHom ψ.toRingHom) = a :=
    congrArg Subtype.val (Spec.homEquivAlgHom.symm_apply_apply ⟨a, haR⟩)
  obtain ⟨T, hT, hRT, het, ε, l, hlε, _⟩ :=
    Algebra.Smooth.SeparableResiduePoint.exists_etale_lift R p.asIdeal F B ψ
  let : CommRing T := hT
  let : Algebra R T := hRT
  let c : Spec (.of T) ⟶ Spec (.of R) := Spec.algebraMap R T
  let t : Spec (.of Ω) ⟶ Spec (.of T) :=
    Spec.algebraMap F Ω ≫ Spec.map (CommRingCat.ofHom l.toRingHom)
  have ht : t ≫ c = β := by
    change (Spec.algebraMap F Ω ≫ Spec.map (CommRingCat.ofHom l.toRingHom)) ≫
      Spec.algebraMap R T = Spec.algebraMap k Ω ≫ bk
    rw [Category.assoc, Spec.map_algHom_algebraMap l, ← hRF, ← Category.assoc]
    have hFΩ : Spec.algebraMap F Ω ≫ Spec.algebraMap k F = Spec.algebraMap k Ω :=
      Spec.map_algHom_algebraMap (IsScalarTower.toAlgHom k F Ω)
    exact congrArg (fun q => q ≫ bk) hFΩ
  have hmaps : Spec.map (CommRingCat.ofHom l.toRingHom) ≫
      Spec.map (CommRingCat.ofHom ε.toRingHom) = Spec.map (CommRingCat.ofHom ψ.toRingHom) := by
    have hr : l.toRingHom.comp ε.toRingHom = ψ.toRingHom :=
      congrArg AlgHom.toRingHom hlε
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hr]
  have hofst : o ≫ zfst = t ≫ Spec.map (CommRingCat.ofHom ε.toRingHom) := by
    rw [← he, ← hψ, ← hmaps, ← Category.assoc]
  let Y : Scheme.{u} := pullback f c
  let yfst : Y ⟶ Spec (.of B) := pullback.fst f c
  let yq : Y ⟶ Spec (.of T) := pullback.snd f c
  let σ : Spec (.of T) ⟶ Y := rationalPointBaseChangeSection ε
  let hσ := rationalPointBaseChangeSection_snd ε
  let α : Z ⟶ Y := pullback.lift zfst (zq ≫ t) (by
    rw [Category.assoc, ht]
    exact pullback.condition)
  have hαfst : α ≫ yfst = zfst := pullback.lift_fst _ _ _
  have hαq : α ≫ yq = zq ≫ t := pullback.lift_snd _ _ _
  have Houter : IsPullback (α ≫ yfst) zq f (t ≫ c) := by
    rw [hαfst, ht]
    exact IsPullback.of_hasPullback f β
  have H : IsPullback α zq yq t :=
    IsPullback.of_right Houter hαq (IsPullback.of_hasPullback f c)
  have hoα : o ≫ α = t ≫ σ := by
    apply pullback.hom_ext
    · rw [Category.assoc, hαfst, Category.assoc, rationalPointBaseChangeSection_fst]
      exact hofst
    · rw [Category.assoc, hαq, ← Category.assoc, ho, Category.id_comp,
        Category.assoc, rationalPointBaseChangeSection_snd, Category.comp_id]
  let : Smooth yq := inferInstanceAs (Smooth (pullback.snd f c))
  have hpre := sectionComponentLocus_preimage_of_isPullback yq α zq t H σ hσ o ho hoα
  have hzin : z ∈ sectionComponentLocus zq o ho := by
    rw [sectionComponentLocus_eq_connectedComponent_of_field Ω zq o ho]
    exact hzcomp
  refine ⟨T, hT, hRT, het, ε, α z, ?_, ?_⟩
  · exact (congrArg (fun g : Z ⟶ Spec (.of B) => g z) hαfst).trans hzx
  · change z ∈ α ⁻¹' sectionComponentLocus yq σ hσ
    rw [hpre]
    exact hzin

end AlgebraicGeometry.Scheme
