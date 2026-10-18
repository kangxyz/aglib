/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.Descent.FiniteFieldCoverGluing
public import Aglib.RingTheory.Descent.FieldOfDefinition.Presentation

/-! Convert the tensor-chart constructor to the exact field-limit projection on affine schemes. -/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open TensorProduct
open _root_.AlgebraicGeometry.Scheme.FiniteEtale (baseChange baseChangeComp baseChangeId)

namespace AlgebraicGeometry.Scheme.FiniteEtale.FieldCoverDescent

universe u

section IsoSquare

variable {X X' T T' : Scheme.{u}} (eT : T' ≅ T) (eX : X' ≅ X)
  (f : T ⟶ X) (g : T' ⟶ X') (h : eT.hom ≫ f = g ≫ eX.hom)
  (Y : Scheme.FiniteEtale T) (Z : Scheme.FiniteEtale X')
    (e : (baseChange g).obj Z ≅ (baseChange eT.hom).obj Y)

/-- Transfer a cover descent witness through specified isomorphisms of its base-change square. -/
def descentIsoOfIsoSquare :
    (baseChange f).obj ((baseChange eX.inv).obj Z) ≅ Y := by
  have H : f ≫ eX.inv = eT.inv ≫ g := by
    rw [← cancel_epi eT.hom, ← Category.assoc, h, Category.assoc,
      eX.hom_inv_id, Category.comp_id, eT.hom_inv_id_assoc]
  exact ((baseChangeComp eX.inv f).symm.app Z) ≪≫
    eqToIso (congrArg (fun k ↦ (baseChange k).obj Z) H) ≪≫
    (baseChangeComp g eT.inv).app Z ≪≫
    (baseChange eT.inv).mapIso e ≪≫
    ((baseChangeComp eT.hom eT.inv).symm.app Y) ≪≫
    eqToIso (congrArg (fun k ↦ (baseChange k).obj Y) eT.inv_hom_id) ≪≫
    (baseChangeId T).app Y

end IsoSquare

section AffineCoordinates

variable (K R : Type u) [Field K] [CommRing R] [Algebra K R]
  {X : Scheme.{u}} (p : X ⟶ Spec (.of K)) (eX : Spec (.of R) ≅ X)
  (hX : eX.hom ≫ p = Spec.algebraMap K R)
  (L : Type u) [CommRing L] [Algebra K L]

/-- The canonical tensor-product coordinates for the actual standard-order field pullback. -/
def tensorPullbackIso : Spec (.of (R ⊗[K] L)) ≅ pullback p (Spec.algebraMap K L) :=
  (pullbackSpecIso K R L).symm ≪≫
    asIso (pullback.map (Spec.algebraMap K R) (Spec.algebraMap K L)
      p (Spec.algebraMap K L) eX.hom (𝟙 _) (𝟙 _)
        (by simpa using hX.symm) (by simp))

@[reassoc] theorem tensorPullbackIso_hom_fst :
    (tensorPullbackIso K R p eX hX L).hom ≫ pullback.fst p (Spec.algebraMap K L) =
      Spec.algebraMap R (R ⊗[K] L) ≫ eX.hom := by
  simp only [tensorPullbackIso, Iso.trans_hom, Iso.symm_hom, asIso_hom,
    Category.assoc, pullback.map, pullback.lift_fst, pullbackSpecIso_inv_fst'_assoc]

@[reassoc] theorem tensorPullbackIso_hom_snd :
    (tensorPullbackIso K R p eX hX L).hom ≫ pullback.snd p (Spec.algebraMap K L) =
      Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight : L →ₐ[K] R ⊗[K] L).toRingHom) := by
  simp only [tensorPullbackIso, Iso.trans_hom, Iso.symm_hom, asIso_hom,
    Category.assoc, pullback.map, pullback.lift_snd, Category.comp_id,
    pullbackSpecIso_inv_snd]
  rfl

end AffineCoordinates

section ActualStage

variable (K Ω R : Type u) [Field K] [Field Ω] [Algebra K Ω]
  [CommRing R] [Algebra K R] {X : Scheme.{u}} (p : X ⟶ Spec (.of K))
  (eX : Spec (.of R) ≅ X) (hX : eX.hom ≫ p = Spec.algebraMap K R)

/-- Coordinates for the exact, opposite-order stage chosen in FieldLimit.schemeDiagram. -/
def tensorStageIso (s : Finset Ω) :
    Spec (.of (_root_.Algebra.Descent.FieldOfDefinition.stageRing K Ω R s)) ≅
      ((FieldLimit.schemeDiagram K Ω p).obj (op s)).left :=
  tensorPullbackIso K R p eX hX (FieldLimit.finiteField K Ω s) ≪≫
    pullbackSymmetry p (Spec.algebraMap K (FieldLimit.finiteField K Ω s))

@[reassoc] theorem tensorStageIso_hom_field (s : Finset Ω) :
    (tensorStageIso K Ω R p eX hX s).hom ≫
      pullback.fst (Spec.algebraMap K (FieldLimit.finiteField K Ω s)) p =
        Spec.map (CommRingCat.ofHom
          (Algebra.TensorProduct.includeRight : FieldLimit.finiteField K Ω s →ₐ[K]
            _root_.Algebra.Descent.FieldOfDefinition.stageRing K Ω R s).toRingHom) := by
  change ((tensorPullbackIso K R p eX hX (FieldLimit.finiteField K Ω s)).hom ≫
    (pullbackSymmetry p (Spec.algebraMap K (FieldLimit.finiteField K Ω s))).hom) ≫ _ = _
  rw [Category.assoc, pullbackSymmetry_hom_comp_fst, tensorPullbackIso_hom_snd]

@[reassoc] theorem tensorStageIso_hom_base (s : Finset Ω) :
    (tensorStageIso K Ω R p eX hX s).hom ≫
      ((FieldLimit.schemeDiagram K Ω p).obj (op s)).hom =
        Spec.algebraMap R (_root_.Algebra.Descent.FieldOfDefinition.stageRing K Ω R s) ≫ eX.hom
          := by
  change ((tensorPullbackIso K R p eX hX (FieldLimit.finiteField K Ω s)).hom ≫
    (pullbackSymmetry p (Spec.algebraMap K (FieldLimit.finiteField K Ω s))).hom) ≫
      pullback.snd (Spec.algebraMap K (FieldLimit.finiteField K Ω s)) p = _
  rw [Category.assoc, pullbackSymmetry_hom_comp_snd, tensorPullbackIso_hom_fst]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The tensor coefficient map and the field-limit projection form the specified actual square. -/
theorem tensorStageIso_projection (s : Finset Ω) :
    (tensorPullbackIso K R p eX hX Ω).hom ≫ FieldLimit.fieldProjection K Ω p (op s) =
      Spec.algebraMap (_root_.Algebra.Descent.FieldOfDefinition.stageRing K Ω R s) (R ⊗[K] Ω) ≫
        (tensorStageIso K Ω R p eX hX s).hom := by
  apply pullback.hom_ext (f := Spec.algebraMap K (FieldLimit.finiteField K Ω s)) (g := p)
  · simp only [Category.assoc, fieldProjection_field, tensorStageIso_hom_field]
    rw [tensorPullbackIso_hom_snd_assoc, ← Spec.map_comp, ← Spec.map_comp]
    congr 1
  · change _ ≫ ((FieldLimit.schemeDiagram K Ω p).obj (op s)).hom =
      _ ≫ ((FieldLimit.schemeDiagram K Ω p).obj (op s)).hom
    simp only [Category.assoc, FieldLimit.fieldProjection_base, tensorStageIso_hom_base]
    rw [tensorPullbackIso_hom_fst, ← Category.assoc, ← Spec.map_comp]
    congr 1

variable [Algebra.IsAlgebraic K Ω]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- A finite étale cover over the field base change of an explicitly affine scheme
comes from an actual cover at one of the exact field-limit stages. -/
def affineCoverDescentOfCoordinates (Y : Scheme.FiniteEtale (pullback p (Spec.algebraMap K Ω))) :
    Σ s : Finset Ω, Σ Z : Scheme.FiniteEtale (((FieldLimit.schemeDiagram K Ω p).obj (op s)).left),
      (baseChange (FieldLimit.fieldProjection K Ω p (op s))).obj Z ≅ Y := by
  let eΩ := tensorPullbackIso K R p eX hX Ω
  let D := tensorAffineCoverDescent K Ω R ((baseChange eΩ.hom).obj Y)
  let eE := tensorStageIso K Ω R p eX hX D.1
  exact ⟨D.1, (baseChange eE.inv).obj D.2.1,
    descentIsoOfIsoSquare eΩ eE _ _ (tensorStageIso_projection K Ω R p eX hX D.1)
      Y D.2.1 D.2.2⟩

end ActualStage

section Affine

variable (K Ω : Type u) [Field K] [Field Ω] [Algebra K Ω] [Algebra.IsAlgebraic K Ω]
  {X : Scheme.{u}} [IsAffine X] (p : X ⟶ Spec (.of K))

/-- Actual field-stage object descent on every affine scheme, independent of a chosen
presentation. -/
def affineCoverDescent (Y : Scheme.FiniteEtale (pullback p (Spec.algebraMap K Ω))) :
    Σ s : Finset Ω, Σ Z : Scheme.FiniteEtale (((FieldLimit.schemeDiagram K Ω p).obj (op s)).left),
      (baseChange (FieldLimit.fieldProjection K Ω p (op s))).obj Z ≅ Y := by
  let R := Γ(X, ⊤)
  let a : K →+* R := ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ p.appTop).hom
  let : Algebra K R := a.toAlgebra
  let eX : Spec (.of R) ≅ X := X.isoSpec.symm
  have hX : eX.hom ≫ p = Spec.algebraMap K R := by
    change X.isoSpec.inv ≫ p = Spec.algebraMap K R
    rw [← Scheme.isoSpec_inv_naturality, Scheme.isoSpec_Spec_inv, ← Spec.map_comp]
    rfl
  exact affineCoverDescentOfCoordinates K Ω R p eX hX Y

end Affine

end AlgebraicGeometry.Scheme.FiniteEtale.FieldCoverDescent

/- Migration source: the R5Lab/Aglib mirror; exact module in the migration record.
R5 revision c82abf3a72ce1e1cedf4a4f1fe08bea994ad4df5.
SHA256 ec09e1eafcad7b66117fe52a8f515a34c841ba911c35a7a351d7d5b6f1870cf9.
Definitions, hypotheses and universes are retained modulo native names. -/
