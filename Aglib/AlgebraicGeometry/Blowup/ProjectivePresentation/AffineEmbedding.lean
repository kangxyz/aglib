/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Blowup.AffineAtlas
public import Aglib.AlgebraicGeometry.ProjectiveSpectrum.DegreeOneBaseChange
public import Aglib.RingTheory.ReesAlgebra.DegreeOneGenerators

/-!
# Actual affine embeddings of arbitrary scalar base changes of a blowup

The full scalar-extended Rees Proj is identified with the literal base
change of the supplied original affine blowup datum. A displayed family
spanning the full tensor ideal gives its actual polynomial Proj closed
embedding. The original coefficient-ring structural triangle is retained.

For a finite family this is a finite-coordinate projective embedding.
No flatness, domain, or image-ideal blowup comparison is assumed.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TensorProduct
open HomogeneousLocalization.Away

universe u

namespace AlgebraicGeometry.Scheme.Blowup.ProjectivePresentation.AffineEmbedding

variable {R : Type u} [CommRing R] {I : Ideal R}

/-- The original affine blowup structural map is the original graded coefficient map. -/
theorem affineProjMap_eq_structureMap :
    affineProjMap I = Proj.DegreeOneEmbedding.structureMap (reesAlgebra.grading I) := by
  apply congrArg (fun φ : R →+* reesAlgebra.grading I 0 =>
    Proj.toSpecZero (reesAlgebra.grading I) ≫ Spec.map (CommRingCat.ofHom φ))
  apply RingHom.ext
  intro r
  apply Subtype.ext
  exact reesAlgebra.degreeZeroEquiv_symm_coe I r

variable (B : BlowupDatum (affineCenter R I))
  (S : Type u) [CommRing S] [Algebra R S]

/-- The original scalar Proj map followed by the unique original blowup comparison. -/
def scalarMap :
    Proj (scalarGrading R (reesAlgebra.grading I) S) ⟶ B.Y :=
  Proj.DegreeOneBaseChange.scalarMap R (reesAlgebra.grading I) S ≫
    ((affineProjBlowupDatum I).comparisonIso B).hom

/-- The supplied affine blowup and its original structural map give the actual scalar square. -/
theorem scalarMap_isPullback :
    IsPullback (scalarMap B S)
      (Proj.DegreeOneEmbedding.structureMap (scalarGrading R (reesAlgebra.grading I) S))
      B.map (Spec.map (CommRingCat.ofHom (algebraMap R S))) := by
  refine (Proj.DegreeOneBaseChange.isPullback_scalarMap R (reesAlgebra.grading I) S
    (reesAlgebra.degreeOne I) (reesAlgebra.degreeOne_mem I)
    (reesAlgebra.irrelevant_eq_span_degreeOne I).le).of_iso
      (Iso.refl _) ((affineProjBlowupDatum I).comparisonIso B)
      (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · simp only [scalarMap, Iso.refl_hom, Category.id_comp]
  · simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
  · simp only [Iso.refl_hom, Category.comp_id]
    exact (affineProjMap_eq_structureMap (R := R) (I := I)).symm.trans
      (BlowupDatum.comparisonIso_hom_map (affineProjBlowupDatum I) B).symm
  · simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]

/-- The full tensor Rees Proj is the literal base change of the supplied original blowup. -/
def scalarReesIso :
    Proj (scalarGrading R (reesAlgebra.grading I) S) ≅
      pullback B.map (Spec.map (CommRingCat.ofHom (algebraMap R S))) :=
  (scalarMap_isPullback B S).isoPullback

/-- The first projection is the original graded map and original blowup comparison. -/
@[reassoc (attr := simp)]
theorem scalarReesIso_hom_fst :
    (scalarReesIso B S).hom ≫
      pullback.fst B.map (Spec.map (CommRingCat.ofHom (algebraMap R S))) =
        scalarMap B S :=
  (scalarMap_isPullback B S).isoPullback_hom_fst

/-- The second projection is the original structural morphism to the new coefficient ring. -/
@[reassoc (attr := simp)]
theorem scalarReesIso_hom_snd :
    (scalarReesIso B S).hom ≫
      pullback.snd B.map (Spec.map (CommRingCat.ofHom (algebraMap R S))) =
        Proj.DegreeOneEmbedding.structureMap (scalarGrading R (reesAlgebra.grading I) S) :=
  (scalarMap_isPullback B S).isoPullback_hom_snd

variable {κ : Type u} (v : κ → S ⊗[R] I)
  (hv : Submodule.span S (Set.range v) = ⊤)

/-- The actual projective embedding defined by the specified full tensor-ideal generators. -/
def embedding :
    pullback B.map (Spec.map (CommRingCat.ofHom (algebraMap R S))) ⟶
      ProjectiveSpace S κ :=
  (scalarReesIso B S).inv ≫
    Proj.DegreeOneEmbedding.embedding (scalarGrading R (reesAlgebra.grading I) S)
      (fun i => reesAlgebra.scalarDegreeOneMap I S (v i))
      (reesAlgebra.span_scalarDegreeOneMap I S v hv)
      (reesAlgebra.baseChange_grading_one_pow I)

/-- The original generator evaluation and scalar Rees comparison give a closed immersion. -/
theorem embedding_isClosedImmersion : IsClosedImmersion (embedding B S v hv) := by
  let : IsClosedImmersion
      (Proj.DegreeOneEmbedding.embedding (scalarGrading R (reesAlgebra.grading I) S)
        (fun i => reesAlgebra.scalarDegreeOneMap I S (v i))
        (reesAlgebra.span_scalarDegreeOneMap I S v hv)
        (reesAlgebra.baseChange_grading_one_pow I)) :=
    Proj.DegreeOneEmbedding.embedding_isClosedImmersion _ _ _ _
  unfold embedding
  infer_instance

/-- The actual embedding keeps the original projection to the new affine base. -/
@[reassoc]
theorem embedding_toSpec :
    embedding B S v hv ≫ ProjectiveSpace.toSpec S κ =
      pullback.snd B.map (Spec.map (CommRingCat.ofHom (algebraMap R S))) := by
  rw [embedding, Category.assoc, Proj.DegreeOneEmbedding.embedding_toSpec,
    ← scalarReesIso_hom_snd B S, Iso.inv_hom_id_assoc]

end AlgebraicGeometry.Scheme.Blowup.ProjectivePresentation.AffineEmbedding
