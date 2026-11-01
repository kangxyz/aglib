/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Normalization.GenericFiniteEtale.Finite
public import Aglib.AlgebraicGeometry.Normalization.Relative
public import Aglib.AlgebraicGeometry.FunctionField.Normalization
public import Aglib.AlgebraicGeometry.FunctionField.AffineCharts

/-! # Recovering a finite-etale cover over the original open

The original generic pullback of a finite-etale cover is normalized over the
ambient normal integral scheme. Over the given nonempty open, this literal
normalization recovers the unchanged covering scheme. The comparison retains
both structural maps and the cartesian square. Local Noetherianity is needed
only for finiteness of the normalization, not for open recovery. Empty and
disconnected covering schemes are allowed.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.FiniteEtale.GenericNormalization.OpenRecovery

variable {X U E : Scheme.{u}} [IsIntegral X] [Nonempty U]
  (j : U ⟶ X) [IsOpenImmersion j] (p : E ⟶ U) [IsFinite p] [Etale p]

/-- The original generic cover, transported only by the original open
immersion's function-field isomorphism. -/
def genericCover : Scheme.FiniteEtale (Spec X.functionField) := by
  let : IsIntegral U := isIntegral_of_isOpenImmersion j
  let : IsDominant j := Scheme.isDominant_of_isOpenImmersion j
  let : IsIso (CommRingCat.ofHom (functionFieldMap j)) := FunctionField.fieldMap_isIso j
  let : IsIso (Spec.map (CommRingCat.ofHom (functionFieldMap j))) := inferInstance
  let : IsFinite (pullback.fst (U.fromSpecStalk (genericPoint U)) p) := inferInstance
  let : Etale (pullback.fst (U.fromSpecStalk (genericPoint U)) p) := inferInstance
  let s := Spec.map (CommRingCat.ofHom (functionFieldMap j))
  let : IsFinite s := inferInstance
  let : Etale s := inferInstance
  let q : pullback (U.fromSpecStalk (genericPoint U)) p ⟶ Spec X.functionField :=
    pullback.fst (U.fromSpecStalk (genericPoint U)) p ≫ s
  let : IsFinite q := MorphismProperty.comp_mem (@IsFinite)
    (pullback.fst (U.fromSpecStalk (genericPoint U)) p) s inferInstance inferInstance
  let : Etale q := Etale.etale_comp
    (pullback.fst (U.fromSpecStalk (genericPoint U)) p) s
  exact ⟨Over.mk q, ⟨‹IsFinite q›, ‹Etale q›⟩⟩

/-- The original generic pullback projection to the unchanged cover. -/
def genericToCover : (genericCover j p).obj.left ⟶ E := by
  let : IsIntegral U := isIntegral_of_isOpenImmersion j
  exact pullback.snd (U.fromSpecStalk (genericPoint U)) p

instance : QuasiCompact (genericToCover j p) := by
  let : IsIntegral U := isIntegral_of_isOpenImmersion j
  exact inferInstanceAs (QuasiCompact (pullback.snd (U.fromSpecStalk (genericPoint U)) p))

instance : QuasiSeparated (genericToCover j p) := by
  let : IsIntegral U := isIntegral_of_isOpenImmersion j
  exact inferInstanceAs (QuasiSeparated (pullback.snd (U.fromSpecStalk (genericPoint U)) p))

/-- The actual generic map whose native relative normalization is used. -/
def genericMap : (genericCover j p).obj.left ⟶ X :=
  (genericCover j p).obj.hom ≫ X.fromSpecStalk (genericPoint X)

instance : QuasiCompact (genericMap j p) := by
  unfold genericMap
  infer_instance

instance : QuasiSeparated (genericMap j p) := by
  unfold genericMap
  infer_instance

/-- The original generic map factors through the original open and cover. -/
theorem genericMap_eq :
    genericMap j p =
      (genericToCover j p ≫ p) ≫ j := by
  let : IsIntegral U := isIntegral_of_isOpenImmersion j
  let : IsDominant j := Scheme.isDominant_of_isOpenImmersion j
  let γ : Spec U.functionField ⟶ U := U.fromSpecStalk (genericPoint U)
  let s : Spec U.functionField ⟶ Spec X.functionField :=
    Spec.map (CommRingCat.ofHom (functionFieldMap j))
  let π : (genericCover j p).obj.left ⟶ Spec U.functionField := pullback.fst γ p
  have hn : s ≫ X.fromSpecStalk (genericPoint X) = γ ≫ j :=
    (fromSpecStalk_genericPoint_naturality j).symm
  have hπ : π ≫ γ = genericToCover j p ≫ p := pullback.condition (f := γ) (g := p)
  exact (Category.assoc π s (X.fromSpecStalk (genericPoint X))).trans
    ((congrArg (fun t => π ≫ t) hn).trans
      ((Category.assoc π γ j).symm.trans (congrArg (fun t => t ≫ j) hπ)))

section Normal

variable [∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)]

/-- The generic cover normalized over the open recovers the original cover. -/
def originalNormalizationIso :
    (genericToCover j p ≫ p).normalization ≅ E := by
  let : IsIntegral U := isIntegral_of_isOpenImmersion j
  let : ∀ x : U, IsIntegrallyClosed (U.presheaf.stalk x) := fun x =>
    IsIntegrallyClosed.of_equiv (asIso (j.stalkMap x)).commRingCatIsoToRingEquiv
  let : IsIso (genericToCover j p).fromNormalization :=
    inferInstanceAs
      (IsIso (pullback.snd (U.fromSpecStalk (genericPoint U)) p).fromNormalization)
  exact Hom.normalizationIntegralFactorIso (genericToCover j p) p ≪≫
    asIso (genericToCover j p).fromNormalization

private theorem originalNormalizationIso_over :
    (originalNormalizationIso j p).hom ≫ p =
      (genericToCover j p ≫ p).fromNormalization := by
  exact Hom.normalizationIntegralFactorIso_hom_over _ _

/-- Smooth normalization base change at the original open square. -/
def normalizationPullbackIso :
    (genericToCover j p ≫ p).normalization ≅
      pullback (genericMap j p).fromNormalization j := by
  let t := genericToCover j p ≫ p
  have H : IsPullback (𝟙 _) t (genericMap j p) j :=
    IsPullback.of_horiz_isIso_mono ⟨by simpa only [Category.id_comp] using genericMap_eq j p⟩
  exact Hom.normalizationSourceIso H.isoPullback t
      (pullback.snd (genericMap j p) j) H.isoPullback_hom_snd ≪≫
    asIso ((genericMap j p).normalizationPullback j)

omit [∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)] in
private theorem normalizationPullbackIso_over :
    (normalizationPullbackIso j p).hom ≫ pullback.snd _ _ =
      (genericToCover j p ≫ p).fromNormalization := by
  dsimp only [normalizationPullbackIso, Iso.trans_hom, asIso_hom]
  rw [Category.assoc, Hom.normalizationPullback_snd]
  exact Hom.normalizationSourceIso_hom_over _ _ _ _

/-- Recovery of the unchanged cover as the literal open pullback of the
native relative normalization. No connectedness of the cover is required. -/
def iso : E ≅ pullback (genericMap j p).fromNormalization j :=
  (originalNormalizationIso j p).symm ≪≫ normalizationPullbackIso j p

@[reassoc (attr := simp)]
theorem iso_hom_snd : (iso j p).hom ≫ pullback.snd _ _ = p := by
  apply (cancel_epi (originalNormalizationIso j p).hom).mp
  simp only [iso, Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.hom_inv_id_assoc]
  exact (normalizationPullbackIso_over j p).trans (originalNormalizationIso_over j p).symm

/-- The original cover's open immersion into the actual normalization. -/
def inclusion : E ⟶ (genericMap j p).normalization :=
  (iso j p).hom ≫ pullback.fst _ _

@[reassoc (attr := simp)]
theorem inclusion_over : inclusion j p ≫ (genericMap j p).fromNormalization = p ≫ j := by
  simp only [inclusion, Category.assoc, pullback.condition, iso_hom_snd_assoc]

/-- The original cover and open form the actual normalization pullback square. -/
theorem isPullback : IsPullback (inclusion j p) p (genericMap j p).fromNormalization j :=
  IsPullback.of_iso_pullback ⟨inclusion_over j p⟩ (iso j p) rfl (iso_hom_snd j p)

instance : IsOpenImmersion (inclusion j p) :=
  MorphismProperty.of_isPullback (isPullback j p).flip inferInstance

/-- Finiteness follows from the genuine finite-etale generic cover and the
normal locally Noetherian ambient scheme. No Nagata premise is needed. -/
theorem fromNormalization_isFinite [IsLocallyNoetherian X] :
    IsFinite (genericMap j p).fromNormalization := by
  unfold genericMap
  infer_instance

end Normal

end AlgebraicGeometry.Scheme.FiniteEtale.GenericNormalization.OpenRecovery
