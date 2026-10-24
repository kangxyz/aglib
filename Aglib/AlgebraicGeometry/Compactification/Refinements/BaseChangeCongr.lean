/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Compactification.Refinements.BaseChange
public import Aglib.AlgebraicGeometry.Compactification.Refinements.SourceIso
public import Aglib.AlgebraicGeometry.Compactification.Refinements.ClosedAmbient

/-!
# Original base-equality transport for normalized base change

Both source and ambient identifications use `pullback.congrHom` for the given
base-map equality. The comparison retains this original ambient isomorphism,
which is needed when reassociating three base maps.
-/

@[expose] public noncomputable section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.Scheme.Hom.DenseCompactification

variable {X S T : Scheme.{u}} {f : X ⟶ S} {b₀ b₁ : T ⟶ S} (h : b₀ = b₁)

/-- The original source identification for an equality of base maps. -/
def congrSourceIso : pullback b₀ f ≅ pullback b₁ f := pullback.congrHom h rfl

@[reassoc (attr := simp)]
lemma congrSourceIso_hom_fst :
    (congrSourceIso (f := f) h).hom ≫ pullback.fst b₁ f = pullback.fst b₀ f := by
  simp [congrSourceIso, pullback.congrHom_hom, pullback.map, pullback.lift_fst]

@[reassoc (attr := simp)]
lemma congrSourceIso_hom_snd :
    (congrSourceIso (f := f) h).hom ≫ pullback.snd b₁ f = pullback.snd b₀ f := by
  simp [congrSourceIso, pullback.congrHom_hom, pullback.map, pullback.lift_snd]

/-- Source transport using the actual base-equality pullback isomorphism. -/
def congrSourceTransport :
    DenseCompactification (pullback.fst b₁ f) ⥤ DenseCompactification (pullback.fst b₀ f) :=
  sourceIso _ (congrSourceIso (f := f) h) (congrSourceIso_hom_fst h)

/-- The raw open map commutes with the original source and ambient equality identifications. -/
lemma baseChange_congr_open (C : DenseCompactification f) :
    (C.toCompactification.baseChange b₀).j ≫ (congrSourceIso (f := C.p) h).hom =
      (congrSourceIso (f := f) h).hom ≫ (C.toCompactification.baseChange b₁).j := by
  subst h
  simp only [congrSourceIso, pullback.congrHom_hom, pullback.map_id, Category.id_comp]
  exact Category.comp_id _

variable [QuasiCompact f] (C : DenseCompactification f)

/-- The original normalized inclusion followed by the original ambient base equality. -/
def congrNormalization : ((baseChange b₀).obj C).Xbar ⟶ pullback b₁ C.p :=
  baseChangeNormalization b₀ C ≫ (congrSourceIso (f := C.p) h).hom

instance congrNormalization_isClosedImmersion : IsClosedImmersion (congrNormalization h C) :=
  inferInstanceAs (IsClosedImmersion
    (baseChangeNormalization b₀ C ≫ (congrSourceIso (f := C.p) h).hom))

lemma congrNormalization_p :
    congrNormalization h C ≫ pullback.fst b₁ C.p = ((baseChange b₀).obj C).p :=
  (Category.assoc _ _ _).trans
    ((congrArg (fun k => baseChangeNormalization b₀ C ≫ k)
      (congrSourceIso_hom_fst (f := C.p) h)).trans (baseChangeNormalization_fst b₀ C))

lemma congrNormalization_open :
    ((baseChange b₀).obj C).j ≫ congrNormalization h C =
      ((baseChange b₁ ⋙ congrSourceTransport h).obj C).j ≫ baseChangeNormalization b₁ C := by
  change ((baseChange b₀).obj C).j ≫
      (baseChangeNormalization b₀ C ≫ (congrSourceIso (f := C.p) h).hom) =
    ((congrSourceIso (f := f) h).hom ≫ ((baseChange b₁).obj C).j) ≫
      baseChangeNormalization b₁ C
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun k => k ≫ (congrSourceIso (f := C.p) h).hom)
      (baseChange_j_normalization b₀ C)).trans
        ((baseChange_congr_open h C).trans
          ((congrArg (fun k : pullback b₁ f ⟶ pullback b₁ C.p =>
              (congrSourceIso (f := f) h).hom ≫ k)
            (baseChange_j_normalization b₁ C).symm).trans
              (Category.assoc (congrSourceIso (f := f) h).hom
                ((baseChange b₁).obj C).j (baseChangeNormalization b₁ C)).symm)))

/-- Actual normalized comparison for the specified equality of base maps. -/
def baseChangeCongrIso :
    (baseChange b₀).obj C ≅ (baseChange b₁ ⋙ congrSourceTransport h).obj C :=
  @closedAmbientIso (pullback b₀ f) T (pullback b₁ C.p) (pullback.fst b₀ f)
    ((baseChange b₀).obj C) ((baseChange b₁ ⋙ congrSourceTransport h).obj C)
    (pullback.fst b₁ C.p) (congrNormalization h C) (baseChangeNormalization b₁ C)
    (baseChangeNormalization_isClosedImmersion b₁ C) (congrNormalization_open h C)
    (congrNormalization_p h C) (baseChangeNormalization_fst b₁ C)
    (congrNormalization_isClosedImmersion h C)

@[simp, reassoc]
lemma baseChangeCongrIso_hom_normalization :
    (baseChangeCongrIso h C).hom.hom ≫ baseChangeNormalization b₁ C = congrNormalization h C :=
  @closedAmbientIso_hom_comp (pullback b₀ f) T (pullback b₁ C.p) (pullback.fst b₀ f)
    ((baseChange b₀).obj C) ((baseChange b₁ ⋙ congrSourceTransport h).obj C)
    (pullback.fst b₁ C.p) (congrNormalization h C) (baseChangeNormalization b₁ C)
    (baseChangeNormalization_isClosedImmersion b₁ C) (congrNormalization_open h C)
    (congrNormalization_p h C) (baseChangeNormalization_fst b₁ C)
    (congrNormalization_isClosedImmersion h C)

/-- Naturality in actual compactification refinements of base-equality transport. -/
def baseChangeCongr : baseChange b₀ ≅ baseChange b₁ ⋙ congrSourceTransport (f := f) h :=
  NatIso.ofComponents (baseChangeCongrIso h) (fun _ => Subsingleton.elim _ _)

end AlgebraicGeometry.Scheme.Hom.DenseCompactification
