/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Compactification.Refinements.Densification
public import Aglib.AlgebraicGeometry.Compactification.Refinements.Common
public import Aglib.AlgebraicGeometry.Compactification.BaseChange

/-!
# Normalized base change of dense compactifications

First take the supplied literal base change, then take the schematic image of
its original open source. Schematic density is not assumed to survive arbitrary
base change. Refinement maps lift through the two images and retain the actual
ambient pullback map. No flatness or qcqs condition on the new base is needed.
-/

@[expose] public noncomputable section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.Scheme.Hom.DenseCompactification

variable {X S T : Scheme.{u}} {f : X ⟶ S}
  {C D : DenseCompactification f} (a : C ⟶ D) (b : T ⟶ S)

/-- The actual map between the two unnormalized ambient pullbacks. -/
def baseChangeAmbientMap : pullback b C.p ⟶ pullback b D.p :=
  pullback.lift (pullback.fst b C.p) (pullback.snd b C.p ≫ a.hom) (by
    rw [Category.assoc, a.base_fac]
    exact pullback.condition)

@[reassoc (attr := simp)]
lemma baseChangeAmbientMap_fst :
    baseChangeAmbientMap a b ≫ pullback.fst b D.p = pullback.fst b C.p :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma baseChangeAmbientMap_snd :
    baseChangeAmbientMap a b ≫ pullback.snd b D.p = pullback.snd b C.p ≫ a.hom :=
  pullback.lift_snd _ _ _

/-- The raw ambient pullback map preserves the supplied base-changed open immersion. -/
@[simp, reassoc]
lemma baseChange_j_ambientMap :
    (C.toCompactification.baseChange b).j ≫ baseChangeAmbientMap a b =
      (D.toCompactification.baseChange b).j := by
  let jC : pullback b f ⟶ pullback b C.p := (C.toCompactification.baseChange b).j
  let jD : pullback b f ⟶ pullback b D.p := (D.toCompactification.baseChange b).j
  change jC ≫ baseChangeAmbientMap a b = jD
  apply pullback.hom_ext
  · calc
      (jC ≫ baseChangeAmbientMap a b) ≫ pullback.fst b D.p =
          jC ≫ (baseChangeAmbientMap a b ≫ pullback.fst b D.p) := Category.assoc _ _ _
      _ = jC ≫ pullback.fst b C.p :=
        congrArg (fun k => jC ≫ k) (baseChangeAmbientMap_fst a b)
      _ = pullback.fst b f := Compactification.baseChange_j_fst C.toCompactification b
      _ = jD ≫ pullback.fst b D.p :=
        (Compactification.baseChange_j_fst D.toCompactification b).symm
  · calc
      (jC ≫ baseChangeAmbientMap a b) ≫ pullback.snd b D.p =
          jC ≫ (baseChangeAmbientMap a b ≫ pullback.snd b D.p) := Category.assoc _ _ _
      _ = jC ≫ (pullback.snd b C.p ≫ a.hom) :=
        congrArg (fun k => jC ≫ k) (baseChangeAmbientMap_snd a b)
      _ = (jC ≫ pullback.snd b C.p) ≫ a.hom := (Category.assoc _ _ _).symm
      _ = (pullback.snd b f ≫ C.j) ≫ a.hom :=
        congrArg (fun k => k ≫ a.hom)
          (Compactification.baseChange_j_snd C.toCompactification b)
      _ = pullback.snd b f ≫ (C.j ≫ a.hom) := Category.assoc _ _ _
      _ = pullback.snd b f ≫ D.j := congrArg (fun k => pullback.snd b f ≫ k) a.open_fac
      _ = jD ≫ pullback.snd b D.p :=
        (Compactification.baseChange_j_snd D.toCompactification b).symm

variable [QuasiCompact f]

instance baseChange_j_quasiCompact (C : DenseCompactification f) :
    QuasiCompact (C.toCompactification.baseChange b).j := by
  have : QuasiCompact
      ((C.toCompactification.baseChange b).j ≫ (C.toCompactification.baseChange b).p) := by
    rw [Compactification.fac]
    infer_instance
  exact QuasiCompact.of_comp (C.toCompactification.baseChange b).j
    (C.toCompactification.baseChange b).p

/-- The dense normalization of the supplied literal base change. -/
def baseChangeObj (C : DenseCompactification f) :
    DenseCompactification (pullback.fst b f) :=
  Compactification.densify (C.toCompactification.baseChange b)

/-- Base change followed by schematic-image normalization on objects and actual maps. -/
def baseChange : DenseCompactification f ⥤ DenseCompactification (pullback.fst b f) where
  obj := baseChangeObj b
  map {C D} a := Compactification.densifyRefinement
    (C.toCompactification.baseChange b) (D.toCompactification.baseChange b)
    (baseChangeAmbientMap a b) (baseChange_j_ambientMap a b) (baseChangeAmbientMap_fst a b)
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

/-- The normalized comparison to the original ambient pullback is its closed image inclusion. -/
def baseChangeNormalization (C : DenseCompactification f) :
    ((baseChange b).obj C).Xbar ⟶ pullback b C.p :=
  Compactification.densifyι (C.toCompactification.baseChange b)

instance baseChangeNormalization_isClosedImmersion (C : DenseCompactification f) :
    IsClosedImmersion (baseChangeNormalization b C) :=
  inferInstanceAs
    (IsClosedImmersion (Compactification.densifyι (C.toCompactification.baseChange b)))

/-- Normalization does not change the original source map. -/
@[reassoc (attr := simp)]
lemma baseChange_j_normalization (C : DenseCompactification f) :
    ((baseChange b).obj C).j ≫ baseChangeNormalization b C =
      (C.toCompactification.baseChange b).j :=
  Compactification.densify_j_ι _

/-- The structural map of the dense base change is the original ambient projection. -/
@[reassoc (attr := simp)]
lemma baseChangeNormalization_fst (C : DenseCompactification f) :
    baseChangeNormalization b C ≫ pullback.fst b C.p = ((baseChange b).obj C).p :=
  Compactification.densifyι_p _

/-- The normalized source map retains its original projection to the old source. -/
@[reassoc]
lemma baseChange_j_normalization_snd (C : DenseCompactification f) :
    ((baseChange b).obj C).j ≫ baseChangeNormalization b C ≫ pullback.snd b C.p =
      pullback.snd b f ≫ C.j := by
  rw [← Category.assoc, baseChange_j_normalization]
  exact Compactification.baseChange_j_snd C.toCompactification b

/-- The actual normalized refinement lies over the original ambient pullback map. -/
@[reassoc (attr := simp)]
lemma baseChange_map_normalization :
    ((baseChange b).map a).hom ≫ baseChangeNormalization b D =
      baseChangeNormalization b C ≫ baseChangeAmbientMap a b :=
  Compactification.densifyMap_ι (C.toCompactification.baseChange b)
    (D.toCompactification.baseChange b) (baseChangeAmbientMap a b)
    (baseChange_j_ambientMap a b)

/-- Normalization is Cartesian over the original base-changed open source. -/
lemma isPullback_baseChangeNormalization (C : DenseCompactification f) :
    IsPullback ((baseChange b).obj C).j (𝟙 (pullback b f))
      (baseChangeNormalization b C) (C.toCompactification.baseChange b).j :=
  Compactification.isPullback_densify _

end AlgebraicGeometry.Scheme.Hom.DenseCompactification
