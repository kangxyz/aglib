/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Normalization.GenericFiniteEtale.ComponentRecognition
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.Reduced

/-! # Original generic normalization under genuine etale base change

The generic-source square is constructed from the actual generic-fibre map
of a locally quasi-finite morphism. Native smooth normalization base change
then gives the original normalization comparison. No ramified normalization
base-change isomorphism or new generic-field model is used.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.FiniteEtale.GenericNormalization.OpenRecovery

universe u

section Source

variable {U V E : Scheme.{u}} [IsIntegral U] [IsIntegral V]
  (g : V ⟶ U) [IsDominant g] [LocallyQuasiFinite g] (p : E ⟶ U)

local notation "γU" => U.fromSpecStalk (genericPoint U)
local notation "γV" => V.fromSpecStalk (genericPoint V)
local notation "s" => Spec.map (CommRingCat.ofHom (functionFieldMap g))

/-- The actual map between the original generic pullbacks of a cover. -/
def genericPullbackMap : pullback γV (pullback.snd p g) ⟶ pullback γU p :=
  pullback.lift (pullback.fst _ _ ≫ s) (pullback.snd _ _ ≫ pullback.fst p g) (by
    rw [Category.assoc, ← fromSpecStalk_genericPoint_naturality g,
      ← Category.assoc, pullback.condition]
    simp only [Category.assoc, pullback.condition])

omit [LocallyQuasiFinite g] in
@[reassoc (attr := simp)] theorem genericPullbackMap_fst :
    genericPullbackMap g p ≫ pullback.fst _ _ = pullback.fst _ _ ≫ s :=
  pullback.lift_fst ..

omit [LocallyQuasiFinite g] in
@[reassoc (attr := simp)] theorem genericPullbackMap_snd :
    genericPullbackMap g p ≫ pullback.snd _ _ = pullback.snd _ _ ≫ pullback.fst p g :=
  pullback.lift_snd ..

/-- The full generic-source square is cartesian for the original locally
quasi-finite map; the cover itself need not be integral or connected. -/
theorem genericPullbackMap_isPullback :
    IsPullback (genericPullbackMap g p)
      (pullback.snd _ _ ≫ pullback.snd p g) (pullback.snd _ _ ≫ p) g := by
  let : IsIso (genericFibreMap g) := genericFibreMap_isIso g
  have hγ : IsPullback s γV γU g :=
    (IsPullback.of_iso_pullback ⟨fromSpecStalk_genericPoint_naturality g⟩
      (asIso (genericFibreMap g)) (pullback.lift_fst ..) (pullback.lift_snd ..)).flip
  have houter : IsPullback (pullback.snd γV (pullback.snd p g) ≫ pullback.fst p g)
      (pullback.fst γV (pullback.snd p g)) p (γV ≫ g) :=
    (IsPullback.of_hasPullback γV (pullback.snd p g)).flip.paste_horiz
      (IsPullback.of_hasPullback p g)
  have hleft : IsPullback (genericPullbackMap g p)
      (pullback.fst γV (pullback.snd p g)) (pullback.fst γU p) s := by
    apply IsPullback.of_right (h₁₂ := pullback.snd γU p)
      (h₂₂ := γU) _ (genericPullbackMap_fst g p)
      (IsPullback.of_hasPullback γU p).flip
    rw [genericPullbackMap_snd, ← fromSpecStalk_genericPoint_naturality g]
    exact houter
  have h := hleft.paste_vert hγ
  simpa only [pullback.condition] using h

end Source

section Normalization

variable {X B U V : Scheme.{u}} [IsIntegral X] [IsIntegral B]
  [IsIntegral U] [IsIntegral V]
  (j : U ⟶ X) [IsOpenImmersion j] (jB : V ⟶ B) [IsOpenImmersion jB]
  (b : B ⟶ X) [Etale b] (g : V ⟶ U) [IsDominant g] [LocallyQuasiFinite g]
  (H : IsPullback g jB j b) (Y : FiniteEtale U)

local notation "pB" => pullback.snd Y.obj.hom g
local notation "q₀" => genericMap j Y.obj.hom
local notation "qB" => genericMap jB pB
local notation "m" => genericPullbackMap g Y.obj.hom

omit [Etale b] in
include H in
/-- The original generic maps form the actual base-change square. -/
theorem genericMap_baseChange_isPullback : IsPullback m qB q₀ b := by
  have h := (genericPullbackMap_isPullback g Y.obj.hom).paste_vert H
  simpa only [genericMap_eq, genericToCover] using h

/-- The genuine etale comparison of the original native normalizations. -/
def etaleBaseChangeIso : (qB).normalization ≅ pullback (q₀).fromNormalization b :=
  Hom.normalizationSourceIso (genericMap_baseChange_isPullback j jB b g H Y).isoPullback
    qB (pullback.snd q₀ b)
    (genericMap_baseChange_isPullback j jB b g H Y).isoPullback_hom_snd ≪≫
      asIso ((q₀).normalizationPullback b)

@[reassoc (attr := simp)] theorem etaleBaseChangeIso_hom_snd :
    (etaleBaseChangeIso j jB b g H Y).hom ≫ pullback.snd _ _ = (qB).fromNormalization := by
  simp only [etaleBaseChangeIso, Iso.trans_hom, asIso_hom, Category.assoc,
    Hom.normalizationPullback_snd, Hom.normalizationSourceIso_hom_over]

/-- The unchanged original generic-source triangle of the smooth comparison. -/
@[reassoc] theorem etaleBaseChangeIso_hom_generic :
    (qB).toNormalization ≫ (etaleBaseChangeIso j jB b g H Y).hom ≫ pullback.fst _ _ =
      m ≫ (q₀).toNormalization := by
  dsimp only [etaleBaseChangeIso, Iso.trans_hom, asIso_hom]
  simp only [Category.assoc]
  rw [Hom.normalizationSourceIso_hom_generic_assoc]
  rw [Hom.toNormalization_normalizationPullback_fst]
  rw [← Category.assoc, IsPullback.isoPullback_hom_fst]

/-- The same comparison preserves the original covering-source inclusion. -/
@[reassoc] theorem inclusion_etaleBaseChangeIso_hom_fst
    [∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)]
    [∀ x : B, IsIntegrallyClosed (B.presheaf.stalk x)] :
    inclusion jB pB ≫ (etaleBaseChangeIso j jB b g H Y).hom ≫ pullback.fst _ _ =
      pullback.fst Y.obj.hom g ≫ inclusion j Y.obj.hom := by
  let : ∀ x : V, IsIntegrallyClosed (V.presheaf.stalk x) := fun x =>
    IsIntegrallyClosed.of_equiv (asIso (jB.stalkMap x)).commRingCatIsoToRingEquiv
  let t := genericToCover jB pB
  let : IsIso t.fromNormalization := inferInstanceAs
    (IsIso (pullback.snd (V.fromSpecStalk (genericPoint V)) pB).fromNormalization)
  let : IsDominant t := by
    rw [← Hom.toNormalization_fromNormalization t]
    infer_instance
  let : IsReduced (pullback Y.obj.hom g) := Etale.finite_isReduced pB
  have hbase :
      (inclusion jB pB ≫ (etaleBaseChangeIso j jB b g H Y).hom ≫ pullback.fst _ _) ≫
          (q₀).fromNormalization =
        (pullback.fst Y.obj.hom g ≫ inclusion j Y.obj.hom) ≫ (q₀).fromNormalization := by
    simp only [Category.assoc, pullback.condition, etaleBaseChangeIso_hom_snd_assoc,
      inclusion_over_assoc, inclusion_over]
    rw [← H.w]
    simp only [← Category.assoc, pullback.condition]
  apply ext_of_isDominant_of_isSeparated (q₀).fromNormalization hbase t
  change genericToCover jB pB ≫ _ = genericToCover jB pB ≫ _
  have hgen : genericToCover jB pB ≫ inclusion jB pB = (qB).toNormalization :=
    genericToCover_inclusion jB ((baseChange g).obj Y)
  have hmap : m ≫ genericToCover j Y.obj.hom =
      genericToCover jB pB ≫ pullback.fst Y.obj.hom g :=
    genericPullbackMap_snd g Y.obj.hom
  rw [← Category.assoc (genericToCover jB pB) (inclusion jB pB), hgen,
    etaleBaseChangeIso_hom_generic]
  rw [← Category.assoc (genericToCover jB pB), ← hmap, Category.assoc,
    genericToCover_inclusion]

end Normalization

end AlgebraicGeometry.Scheme.FiniteEtale.GenericNormalization.OpenRecovery
