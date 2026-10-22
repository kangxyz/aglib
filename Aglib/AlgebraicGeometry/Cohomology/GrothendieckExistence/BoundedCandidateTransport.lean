/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.BoundedCandidateIso
public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.CandidateIsoTransportComparison

/-! # Bounded candidate isomorphisms across original overlap coordinates

The two formal ideals are equal. Their original diagrams and algebraic targets
may have different native presentations. A specified unit-compatible comparison
of the target completions and the original formal square suffice to transport
the genuine bounded-candidate theorem, preserving both original projections.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.Modules.Coherent

universe u

/-- Compare genuine bounded candidates in two equal-ideal coordinate systems.
All comparison maps are explicit and retain the original quotient units. -/
def boundedCandidateIsoAcrossIdeals
    {X : Scheme.{u}} [IsLocallyNoetherian X] {I J : X.IdealSheafData} (hIJ : I = J)
    {F₁ : AdicSystem X I} {F₂ : AdicSystem X J}
    {H₁ H₂ G₁ G₂ : X.CoherentSheaf}
    (α₁ : F₁ ⟶ (completionFunctor X I).obj H₁)
    (α₂ : F₂ ⟶ (completionFunctor X J).obj H₂)
    (eF : F₁.obj ≅ F₂.obj) (eH : H₁ ≅ H₂)
    (eC : ((completionFunctor X I).obj H₁).obj ≅
      ((completionFunctor X J).obj H₂).obj)
    (hunit : ∀ n : ℕ,
      (idealSheafQuotientUnit X (I ^ n)).app H₁.obj ≫ eC.hom.app (op n) =
        eH.hom.hom ≫ (idealSheafQuotientUnit X (J ^ n)).app H₂.obj)
    (hα : α₁.hom ≫ eC.hom = eF.hom ≫ α₂.hom)
    (a₁ : G₁ ⟶ H₁) (β₁ : (completionFunctor X I).obj G₁ ≅ F₁)
    (h₁ : β₁.hom ≫ α₁ = (completionFunctor X I).map a₁)
    (t₁ : ℕ) (hk₁ : killedByIdealSheaf (I ^ t₁) (kernel a₁.hom))
    (hc₁ : killedByIdealSheaf (I ^ t₁) (cokernel a₁.hom))
    (a₂ : G₂ ⟶ H₂) (β₂ : (completionFunctor X J).obj G₂ ≅ F₂)
    (h₂ : β₂.hom ≫ α₂ = (completionFunctor X J).map a₂)
    (t₂ : ℕ) (hk₂ : killedByIdealSheaf (J ^ t₂) (kernel a₂.hom))
    (hc₂ : killedByIdealSheaf (J ^ t₂) (cokernel a₂.hom)) :
    CandidateIsoTransportComparison eF eH a₁ β₁ a₂ β₂ := by
  subst J
  let E : F₁ ≅ F₂ := ObjectProperty.isoMk _ eF
  have heC : eC.hom = ((completionFunctor X I).map eH.hom).hom := by
    apply NatTrans.ext
    funext n
    apply (cancel_epi ((idealSheafQuotientUnit X (I ^ n.unop)).app H₁.obj)).mp
    rw [hunit]
    exact (idealSheafQuotientUnit X (I ^ n.unop)).naturality eH.hom.hom
  have heα : α₁ ≫ (completionFunctor X I).map eH.hom = E.hom ≫ α₂ := by
    apply ObjectProperty.hom_ext
    change α₁.hom ≫ ((completionFunctor X I).map eH.hom).hom = eF.hom ≫ α₂.hom
    rw [← heC]
    exact hα
  let a₂' := a₂ ≫ eH.inv
  let β₂' := β₂ ≪≫ E.symm
  have h₂' : β₂'.hom ≫ α₁ = (completionFunctor X I).map a₂' := by
    apply (cancel_mono ((completionFunctor X I).map eH.hom)).mp
    dsimp only [β₂', a₂', Iso.trans_hom, Iso.symm_hom]
    rw [Category.assoc, heα]
    simp only [← Functor.map_comp, Category.assoc, Iso.inv_hom_id_assoc,
      Iso.inv_hom_id, Category.comp_id]
    exact h₂
  have hb₂ : killedByIdealSheaf (I ^ t₂) (kernel a₂'.hom) ∧
      killedByIdealSheaf (I ^ t₂) (cokernel a₂'.hom) :=
    ⟨killedByIdealSheaf_of_iso _ (kernelCompMono a₂.hom eH.inv.hom).symm hk₂,
      killedByIdealSheaf_of_iso _ (cokernelCompIsIso a₂.hom eH.inv.hom).symm hc₂⟩
  let d := boundedCandidateIsoComparison α₁ a₁ β₁ h₁ t₁ hk₁ hc₁
    a₂' β₂' h₂' t₂ hb₂.1 hb₂.2
  refine ⟨d.val, ?_, ?_⟩
  · have hd := congrArg (fun f => f ≫ eH.hom) d.property.1
    simpa only [a₂', Category.assoc, Iso.inv_hom_id, Category.comp_id] using hd
  · intro n
    have hd := congrArg (fun f => f ≫ eF.hom.app (op n)) (d.property.2 n)
    simpa only [β₂', E, Iso.trans_hom, Iso.symm_hom, ObjectProperty.FullSubcategory.comp_hom,
      NatTrans.comp_app, ObjectProperty.isoMk, ObjectProperty.homMk, Category.assoc,
      Iso.inv_hom_id_app, Category.comp_id] using hd

end AlgebraicGeometry.Scheme.Modules.Coherent
