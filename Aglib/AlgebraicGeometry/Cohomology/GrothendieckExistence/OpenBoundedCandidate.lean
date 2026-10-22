/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.OpenFormalCompletion
public import Aglib.AlgebraicGeometry.Modules.Restriction.ExtensionByZero

/-! # Actual open pullback of bounded reconstruction candidates

The actual algebraic map, formal isomorphism, original square, and both
ordinary bounds are retained. All-limit preservation uses open restriction's
existing right adjoint structure, not a completion/localization assertion.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Modules.Coherent

/-- Conjugating a candidate square by original comparison isomorphisms,
proved before any geometric completion objects are substituted. -/
theorem functorConjugateCandidateSquare {C D : Type*} [Category C] [Category D]
    (T : C ⥤ D) {F G H : C} {G' H' : D}
    (α : F ⟶ H) (β : G ≅ F) (a : G ⟶ H) (h : β.hom ≫ α = a)
    (eG : T.obj G ≅ G') (eH : T.obj H ≅ H') (b : G' ⟶ H')
    (hb : T.map a ≫ eH.hom = eG.hom ≫ b) :
    (eG.symm ≪≫ T.mapIso β).hom ≫ (T.map α ≫ eH.hom) = b := by
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Category.assoc]
  rw [← Functor.map_comp_assoc, h, hb]
  simp only [Iso.inv_hom_id_assoc]

universe u
variable {X Y : Scheme.{u}} [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
  (p : Y ⟶ X) [IsOpenImmersion p] {K : X.IdealSheafData}
  {F : AdicSystem X K} {G H : X.CoherentSheaf}
  (α : F ⟶ (completionFunctor X K).obj H)

/-- The original formal morphism under actual open pullback. -/
def openReconstructionComparison :
    (openIdealPullbackFunctor p K).obj F ⟶
      (completionFunctor Y (K.comap p)).obj ((coherentPullback p).obj H) :=
  (openIdealPullbackFunctor p K).map α ≫ (openIdealPullbackCompletionIso p K H).hom

/-- The specified candidate formal isomorphism under actual open pullback. -/
def openReconstructionCandidateIso (β : (completionFunctor X K).obj G ≅ F) :
    (completionFunctor Y (K.comap p)).obj ((coherentPullback p).obj G) ≅
      (openIdealPullbackFunctor p K).obj F :=
  (openIdealPullbackCompletionIso p K G).symm ≪≫
    (openIdealPullbackFunctor p K).mapIso β

/-- The pulled candidate retains its original algebraic target square. -/
theorem openReconstructionCandidateIso_square (a : G ⟶ H)
    (β : (completionFunctor X K).obj G ≅ F)
    (hβ : β.hom ≫ α = (completionFunctor X K).map a) :
    (openReconstructionCandidateIso p β).hom ≫ openReconstructionComparison p α =
      (completionFunctor Y (K.comap p)).map ((coherentPullback p).map a) :=
  functorConjugateCandidateSquare (openIdealPullbackFunctor p K) α β
    ((completionFunctor X K).map a) hβ
    (openIdealPullbackCompletionIso p K G) (openIdealPullbackCompletionIso p K H)
    ((completionFunctor Y (K.comap p)).map ((coherentPullback p).map a))
    (openIdealPullbackCompletionIso_naturality p K a)

/-- Both ordinary algebraic defects remain bounded by the same original
pulled ideal power. The two defects are not assumed to form an adic system. -/
theorem openReconstructionCandidate_bounds (a : G ⟶ H) (t : ℕ)
    (hk : killedByIdealSheaf (K ^ t) (kernel a.hom))
    (hc : killedByIdealSheaf (K ^ t) (cokernel a.hom)) :
    killedByIdealSheaf (K.comap p ^ t) (kernel ((coherentPullback p).map a).hom) ∧
      killedByIdealSheaf (K.comap p ^ t) (cokernel ((coherentPullback p).map a).hom) := by
  let : G.obj.IsQuasicoherent := QuasiCoherent.quasicoherent_of_affineCharts _
    (fun R j _ => (G.property R j).1)
  let : H.obj.IsQuasicoherent := QuasiCoherent.quasicoherent_of_affineCharts _
    (fun R j _ => (H.property R j).1)
  let : (kernel a.hom).IsQuasicoherent := QuasiCoherent.quasicoherent_kernel a.hom
  let : (cokernel a.hom).IsQuasicoherent := QuasiCoherent.quasicoherent_cokernel a.hom
  let : PreservesLimits (pullback p) :=
    preservesLimits_of_natIso (restrictFunctorIsoPullback p)
  exact ⟨killedByIdealSheaf_of_iso _ (PreservesKernel.iso (pullback p) a.hom)
      (killedByOpenIdeal_pullback p K (kernel a.hom) t hk),
    killedByIdealSheaf_of_iso _ (PreservesCokernel.iso (pullback p) a.hom)
      (killedByOpenIdeal_pullback p K (cokernel a.hom) t hc)⟩

end AlgebraicGeometry.Scheme.Modules.Coherent
