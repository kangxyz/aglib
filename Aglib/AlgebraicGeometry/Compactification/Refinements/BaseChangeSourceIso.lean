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
# Normalized base change and original source-isomorphism transport

The source comparison is the native pullback map of the source isomorphism.
Both normalized ambients are compared inside the same original raw pullback.
-/

@[expose] public noncomputable section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.Scheme.Hom.DenseCompactification

variable {X X' S T : Scheme.{u}} {f : X ⟶ S} (f' : X' ⟶ S)
  (e : X' ≅ X) (h : e.hom ≫ f = f') (b : T ⟶ S)

/-- The original pullback source isomorphism induced by the original source isomorphism. -/
def pullbackSourceIso : pullback b f' ≅ pullback b f :=
  asIso (pullback.map b f' b f (𝟙 T) e.hom (𝟙 S)
    ((Category.comp_id _).trans (Category.id_comp _).symm)
    ((Category.comp_id _).trans h.symm))

@[reassoc (attr := simp)]
lemma pullbackSourceIso_hom_fst :
    (pullbackSourceIso f' e h b).hom ≫ pullback.fst b f = pullback.fst b f' :=
  (pullback.lift_fst _ _ _).trans (Category.comp_id _)

@[reassoc (attr := simp)]
lemma pullbackSourceIso_hom_snd :
    (pullbackSourceIso f' e h b).hom ≫ pullback.snd b f = pullback.snd b f' ≫ e.hom :=
  pullback.lift_snd _ _ _

/-- Transport on the literal base-changed sources. -/
def pullbackSourceTransport :
    DenseCompactification (pullback.fst b f) ⥤ DenseCompactification (pullback.fst b f') :=
  sourceIso _ (pullbackSourceIso f' e h b) (pullbackSourceIso_hom_fst f' e h b)

/-- Raw base change retains the original source-isomorphism square. -/
lemma baseChange_sourceIso_open (C : DenseCompactification f) :
    (((sourceIso f' e h).obj C).toCompactification.baseChange b).j =
      (pullbackSourceIso f' e h b).hom ≫ (C.toCompactification.baseChange b).j := by
  apply pullback.hom_ext
  · exact (Compactification.baseChange_j_fst ((sourceIso f' e h).obj C).toCompactification b).trans
      (((Category.assoc _ _ _).trans
        ((congrArg (fun k => (pullbackSourceIso f' e h b).hom ≫ k)
          (Compactification.baseChange_j_fst C.toCompactification b)).trans
            (pullbackSourceIso_hom_fst f' e h b))).symm)
  · exact (Compactification.baseChange_j_snd
      ((sourceIso f' e h).obj C).toCompactification b).trans
      ((Category.assoc (pullback.snd b f') e.hom C.j).symm.trans
        ((congrArg (fun k => k ≫ C.j) (pullbackSourceIso_hom_snd f' e h b).symm).trans
          ((Category.assoc (pullbackSourceIso f' e h b).hom (pullback.snd b f) C.j).trans
            ((congrArg (fun k : pullback b f ⟶ C.Xbar =>
                (pullbackSourceIso f' e h b).hom ≫ k)
              (Compactification.baseChange_j_snd C.toCompactification b).symm).trans
                (Category.assoc (pullbackSourceIso f' e h b).hom
                  (C.toCompactification.baseChange b).j (pullback.snd b C.p)).symm))))

variable [QuasiCompact f] [QuasiCompact f'] (C : DenseCompactification f)

/-- The two normalized embeddings agree on the original base-changed source. -/
lemma baseChangeSourceIso_open :
    ((sourceIso f' e h ⋙ baseChange b).obj C).j ≫
        baseChangeNormalization b ((sourceIso f' e h).obj C) =
      ((baseChange b ⋙ pullbackSourceTransport f' e h b).obj C).j ≫
        baseChangeNormalization b C := by
  change ((baseChange b).obj ((sourceIso f' e h).obj C)).j ≫
      baseChangeNormalization b ((sourceIso f' e h).obj C) =
    ((pullbackSourceIso f' e h b).hom ≫ ((baseChange b).obj C).j) ≫
      baseChangeNormalization b C
  exact (baseChange_j_normalization b ((sourceIso f' e h).obj C)).trans
    ((baseChange_sourceIso_open f' e h b C).trans
      ((congrArg (fun k : pullback b f ⟶ pullback b C.p =>
          (pullbackSourceIso f' e h b).hom ≫ k)
        (baseChange_j_normalization b C).symm).trans
          (Category.assoc (pullbackSourceIso f' e h b).hom
            ((baseChange b).obj C).j (baseChangeNormalization b C)).symm))

/-- Actual normalized base change commutes with original source-isomorphism transport. -/
def baseChangeSourceIsoComponent :
    (sourceIso f' e h ⋙ baseChange b).obj C ≅
      (baseChange b ⋙ pullbackSourceTransport f' e h b).obj C :=
  @closedAmbientIso (pullback b f') T (pullback b C.p) (pullback.fst b f')
    ((sourceIso f' e h ⋙ baseChange b).obj C)
    ((baseChange b ⋙ pullbackSourceTransport f' e h b).obj C) (pullback.fst b C.p)
    (baseChangeNormalization b ((sourceIso f' e h).obj C)) (baseChangeNormalization b C)
    (baseChangeNormalization_isClosedImmersion b C) (baseChangeSourceIso_open f' e h b C)
    (baseChangeNormalization_fst b ((sourceIso f' e h).obj C))
    (baseChangeNormalization_fst b C)
    (baseChangeNormalization_isClosedImmersion b ((sourceIso f' e h).obj C))

/-- The comparison preserves the actual embeddings into the original raw ambient. -/
@[simp, reassoc]
lemma baseChangeSourceIsoComponent_normalization :
    (baseChangeSourceIsoComponent f' e h b C).hom.hom ≫ baseChangeNormalization b C =
      baseChangeNormalization b ((sourceIso f' e h).obj C) :=
  @closedAmbientIso_hom_comp (pullback b f') T (pullback b C.p) (pullback.fst b f')
    ((sourceIso f' e h ⋙ baseChange b).obj C)
    ((baseChange b ⋙ pullbackSourceTransport f' e h b).obj C) (pullback.fst b C.p)
    (baseChangeNormalization b ((sourceIso f' e h).obj C)) (baseChangeNormalization b C)
    (baseChangeNormalization_isClosedImmersion b C) (baseChangeSourceIso_open f' e h b C)
    (baseChangeNormalization_fst b ((sourceIso f' e h).obj C))
    (baseChangeNormalization_fst b C)
    (baseChangeNormalization_isClosedImmersion b ((sourceIso f' e h).obj C))

/-- Naturality of the original source-transport comparison in actual refinements. -/
def baseChangeSourceIso : sourceIso f' e h ⋙ baseChange b ≅
    baseChange b ⋙ pullbackSourceTransport f' e h b :=
  NatIso.ofComponents (baseChangeSourceIsoComponent f' e h b)
    (fun _ => Subsingleton.elim _ _)

end AlgebraicGeometry.Scheme.Hom.DenseCompactification
