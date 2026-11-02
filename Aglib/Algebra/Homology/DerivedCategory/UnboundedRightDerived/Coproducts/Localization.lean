/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.HomotopyCategory.Coproducts
public import Aglib.Algebra.Homology.DerivedCategory.KInjective.Representatives
public import Aglib.Algebra.Homology.DerivedCategory.KInjective.Existence.Tower.Replacement
public import Aglib.Algebra.Homology.Coproduct.Homology
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence

/-!
# Coproducts under the original derived localization

A supplied actual K-injective replacement proves the universal property of the
original cofan `Q(∐ K)`, with legs `Q.map (Sigma.ι K a)`. The proof uses original
chain representatives and glues their actual homotopies, not an assumed
cocontinuity property of localization. For a Grothendieck abelian category the
proved regular-stage replacement supplies this input and gives native derived
coproducts. Exactness is required only by the homology comparison.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u v w s t

open CategoryTheory CategoryTheory.Limits

namespace DerivedCategory

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
  {κ : Type t} [HasColimitsOfShape (Discrete κ) C]

/-- The actual localization cofan is colimiting when an actual K-injective
replacement is supplied. No exactness of coproducts is used. -/
def qCoproductCofanIsColimitOfKInjectiveReplacement
    (R : CochainComplex C ℤ ⥤ CochainComplex C ℤ)
    (η : 𝟭 (CochainComplex C ℤ) ⟶ R)
    (hη : ∀ K, QuasiIso (η.app K))
    (hR : ∀ K, (R.obj K).IsKInjective)
    (K : κ → CochainComplex C ℤ) :
    IsColimit (Cofan.mk (Q.obj (∐ K)) (fun a => Q.map (Sigma.ι K a))) := by
  let I (T : DerivedCategory C) := R.obj (Q.objPreimage T)
  let e (T : DerivedCategory C) : T ≅ Q.obj (I T) := by
    letI := hη (Q.objPreimage T)
    exact (Q.objObjPreimageIso T).symm ≪≫ asIso (Q.map (η.app (Q.objPreimage T)))
  have hl : ∀ (s : Cofan (fun a => Q.obj (K a))) (a : κ),
      ∃ l : K a ⟶ I s.pt, Q.map l = s.inj a ≫ (e s.pt).hom := by
    intro s a
    let : (I s.pt).IsKInjective := hR _
    exact CochainComplex.exists_chain_representative_of_isKInjective _
  choose l hl using hl
  refine Cofan.IsColimit.mk _
    (fun s => Q.map (Sigma.desc (l s)) ≫ (e s.pt).inv) ?_ ?_
  · intro s a
    change Q.map (Sigma.ι K a) ≫ (Q.map (Sigma.desc (l s)) ≫ (e s.pt).inv) = _
    rw [← Category.assoc, ← Functor.map_comp, Sigma.ι_comp_desc, hl]
    simp
  · intro s m hm
    let : (I s.pt).IsKInjective := hR _
    obtain ⟨f, hf⟩ := CochainComplex.exists_chain_representative_of_isKInjective
      (m ≫ (e s.pt).hom)
    change ∀ a, Q.map (Sigma.ι K a) ≫ m = s.inj a at hm
    apply (cancel_mono (e s.pt).hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [← hf]
    apply Q_map_eq_of_homotopy C
    apply Homotopy.ofCoproductInclusions K
    intro a
    apply CochainComplex.homotopyOfDerivedEqOfIsKInjective
    rw [Sigma.ι_comp_desc, Functor.map_comp, hf, ← Category.assoc, hm a, hl]

variable [IsGrothendieckAbelian.{s} C]

/-- The proved regular-stage K-injective replacement supplies the original
localization coproduct universal property in a Grothendieck category. -/
def qCoproductCofanIsColimit (K : κ → CochainComplex C ℤ) :
    IsColimit (Cofan.mk (Q.obj (∐ K)) (fun a => Q.map (Sigma.ι K a))) :=
  qCoproductCofanIsColimitOfKInjectiveReplacement
    (CochainComplex.kInjectiveReplacementFunctor (isSeparator_separator C))
    (CochainComplex.kInjectiveReplacementUnit (isSeparator_separator C))
    (CochainComplex.kInjectiveReplacementUnit_quasiIso (isSeparator_separator C))
    (CochainComplex.kInjectiveReplacement_isKInjective (isSeparator_separator C)) K

instance Q_preservesCoproduct (K : κ → CochainComplex C ℤ) :
    PreservesColimit (Discrete.functor K) (Q (C := C)) :=
  preservesColimit_of_preserves_colimit_cocone (coproductIsCoproduct K)
    ((isColimitMapCoconeCofanMkEquiv _ _ _).symm (qCoproductCofanIsColimit K))

instance Q_preservesCoproducts : PreservesColimitsOfShape (Discrete κ) (Q (C := C)) :=
  preservesColimitsOfShape_of_discrete _

instance hasCoproduct (K : κ → DerivedCategory C) : HasCoproduct K := by
  let L (a : κ) := Q.objPreimage (K a)
  let : HasCoproduct (fun a => Q.obj (L a)) :=
    HasColimit.mk ⟨_, qCoproductCofanIsColimit L⟩
  exact hasColimit_of_iso
    (F := Discrete.functor (fun a => Q.obj (L a)))
    (Discrete.natIso (fun a => (Q.objObjPreimageIso (K a.as)).symm))

instance hasCoproducts : HasColimitsOfShape (Discrete κ) (DerivedCategory C) where
  has_colimit F := hasColimit_of_iso (Discrete.natIsoFunctor (F := F))

/-- The native coproduct comparison for the same original localization functor. -/
def qCoproductIso (K : κ → CochainComplex C ℤ) :
    Q.obj (∐ K) ≅ ∐ (fun a => Q.obj (K a)) :=
  PreservesCoproduct.iso Q K

/-- The localization coproduct comparison retains each original inclusion. -/
@[reassoc (attr := simp)]
theorem Q_map_sigma_ι_coproductIso_hom (K : κ → CochainComplex C ℤ) (a : κ) :
    Q.map (Sigma.ι K a) ≫ (qCoproductIso K).hom =
      Sigma.ι (fun a => Q.obj (K a)) a := by
  apply (cancel_mono (qCoproductIso K).inv).mp
  rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  exact (ι_comp_sigmaComparison Q K a).symm

variable [HasExactColimitsOfShape (Discrete κ) C]

/-- Homology of the actual derived coproduct of localized complexes. -/
def qCoproductHomologyIso (K : κ → CochainComplex C ℤ) (n : ℤ) :
    (homologyFunctor C n).obj (∐ (fun a => Q.obj (K a))) ≅
      ∐ (fun a => (K a).homology n) :=
  (homologyFunctor C n).mapIso (qCoproductIso K).symm ≪≫
    (homologyFunctorFactors C n).app (∐ K) ≪≫
    HomologicalComplex.coproductHomologyIso K n

/-- Original derived coproduct inclusions agree with the original homology
inclusions under the canonical homology comparison. -/
@[reassoc (attr := simp)]
theorem homology_sigma_ι_Q_coproductHomologyIso_hom
    (K : κ → CochainComplex C ℤ) (a : κ) (n : ℤ) :
    (homologyFunctor C n).map (Sigma.ι (fun a => Q.obj (K a)) a) ≫
        (qCoproductHomologyIso K n).hom =
      (homologyFunctorFactors C n).hom.app (K a) ≫
        Sigma.ι (fun a => (K a).homology n) a := by
  have hι : Sigma.ι (fun a => Q.obj (K a)) a ≫ (qCoproductIso K).inv =
      Q.map (Sigma.ι K a) := by
    rw [← Q_map_sigma_ι_coproductIso_hom, Category.assoc,
      Iso.hom_inv_id, Category.comp_id]
  dsimp only [qCoproductHomologyIso, Iso.trans_hom, Functor.mapIso_hom,
    Iso.symm_hom, Iso.app_hom]
  rw [← Category.assoc, ← Functor.map_comp, hι]
  have h := homologyFunctorFactors_hom_naturality (Sigma.ι K a) n
  have h' := congrArg (fun f => f ≫
    (HomologicalComplex.coproductHomologyIso K n).hom) h
  simpa only [Category.assoc,
    HomologicalComplex.homologyMap_sigma_ι_coproductHomologyIso_hom] using h'

end DerivedCategory
