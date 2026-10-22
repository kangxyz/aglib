/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.GlobalFormalComparison
public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.AffineModificationFactorizationBound
public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.BoundedDefectsOpenCover

/-! # The original global modification comparison with one uniform bound

The actual map comes from affine formal functions and native Hom-sheaf gluing.
Its chartwise bounds apply to every stage simultaneously. A finite open subcover
then gives a single positive exceptional-ideal exponent globally.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.Modules.Coherent
universe u
variable {A : Type u} [CommRing A] {X Y : Scheme.{u}}
  [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
  (p : Y ⟶ X) [IsProper p] (f : X ⟶ Spec (CommRingCat.of A)) (I : Ideal A)
  (F : AdicSystem X (idealThickeningIdealSheaf f I)) (G : Y.CoherentSheaf)
  (β : (baseIdealPullbackFunctor p f I).obj F ≅
    (completionFunctor Y (idealThickeningIdealSheaf (p ≫ f) I)).obj G)
  (α : F ⟶ (completionFunctor X (idealThickeningIdealSheaf f I)).obj
    (properPushforwardCoefficient p G))
  (hα : α.hom ≫ formalPushforwardComparison p f I G =
    formalModificationAdjoint p f I F _ β.hom)
  (K : X.IdealSheafData) (V : X.Opens) [IsIso (p ∣_ V)]
  (hV : (V : Set X)ᶜ ⊆ K.support)

include hα hV in
/-- One affine open has one bound for every original pulled stage. The map is
the pullback of the specified global map, not an unrelated affine comparison. -/
theorem formalModificationComparison_affine_pullback_bound
    (B : CommRingCat.{u}) (j : Spec B ⟶ X) [IsOpenImmersion j] :
    ∃ t : ℕ, ∀ n : ℕ,
      killedByIdealSheaf (K.comap j ^ t) (kernel ((pullback j).map (α.hom.app (op n)))) ∧
      killedByIdealSheaf (K.comap j ^ t) (cokernel ((pullback j).map (α.hom.app (op n)))) := by
  let : IsLocallyNoetherian (Spec B) := isLocallyNoetherian_of_isOpenImmersion j
  let : IsNoetherianRing B := isLocallyNoetherian_Spec.mp inferInstance
  let a := pullback.fst p j
  let b := pullback.snd p j
  let h := IsPullback.of_hasPullback p j
  let : IsLocallyNoetherian (Limits.pullback p j) := isLocallyNoetherian_of_isOpenImmersion a
  let F' := (baseIdealPullbackFunctor j f I).obj F
  let G' := (coherentPullback a).obj G
  let β' := formalModificationBaseChangeIso a b p j h.w f I F G β
  let α' := formalModificationComparisonBaseChange a b p j h f I F G α
  let : IsIso (b ∣_ (j ⁻¹ᵁ V)) := Scheme.Hom.isIso_restrict_pullback p j V
  have hV' : ((j ⁻¹ᵁ V : (Spec B).Opens) : Set (Spec B))ᶜ ⊆ (K.comap j).support := by
    intro x hx
    rw [IdealSheafData.support_comap]
    exact hV hx
  obtain ⟨t, _, ht⟩ := affineModificationComparison_overArbitraryBase_hasBoundedDefects
    b G' (j ≫ f) I F' β' α'
    (formalModificationComparisonBaseChange_diagram a b p j h f I F G β α hα)
    (K.comap j) (j ⁻¹ᵁ V) hV'
  have hp := defectsKilled_of_originalComposite
    ((baseIdealPullbackFunctor j f I).map α)
    (baseIdealPullbackCompletionIso j f I (properPushforwardCoefficient p G))
    ((completionFunctor (Spec B) (idealThickeningIdealSheaf (j ≫ f) I)).mapIso
      (properPushforwardOpenCoefficientIso a b p j h G))
    ((completionFunctor (Spec B) (idealThickeningIdealSheaf (j ≫ f) I)).map
      (properPushforwardBaseChangeCoefficient a b p j h G))
    rfl α' (formalModificationComparisonBaseChange_eq a b p j h f I F G α) ht
  exact ⟨t, hp⟩

include hα hV in
/-- The original global comparison has one exceptional-ideal bound independent
of all formal stages. Quasicompactness is used only to choose a finite cover. -/
theorem formalModificationComparison_hasBoundedDefects [CompactSpace X] :
    AdicSystem.HasBoundedDefects K α := by
  classical
  let B := X.affineOpenCover.X
  let j := X.affineOpenCover.f
  have hc : ∀ x : X, ∃ (i : X.affineOpenCover.I₀) (y : Spec (B i)), j i y = x :=
    fun x => ⟨X.affineOpenCover.idx x, X.affineOpenCover.covers x⟩
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover
    (fun i => ((j i).opensRange : Set X)) (fun i => (j i).opensRange.isOpen) (by
      intro x _
      obtain ⟨i, y, hy⟩ := hc x
      exact Set.mem_iUnion.mpr ⟨i, y, hy⟩)
  let T := {i // i ∈ s}
  have hcover : ∀ x : X, ∃ (i : T) (y : Spec (B i.val)), j i.val y = x := by
    intro x
    obtain ⟨i, hi, hx⟩ := Set.mem_iUnion₂.mp (hs (Set.mem_univ x))
    obtain ⟨y, hy⟩ := hx
    exact ⟨⟨i, hi⟩, y, hy⟩
  exact AdicSystem.hasBoundedDefects_of_pullback_openCover
    (fun i : T => Spec (B i.val)) (fun i => j i.val) hcover K α
    (fun i => formalModificationComparison_affine_pullback_bound p f I F G β α hα K V hV
      (B i.val) (j i.val))

include hV in
/-- The original global 088B comparison, with its exact original diagram and
one positive bound. No density or reconstruction premise is required. -/
theorem exists_formalModificationComparison_bounded [IsProper f] :
    ∃ φ : F ⟶ (completionFunctor X (idealThickeningIdealSheaf f I)).obj
      (properPushforwardCoefficient p G),
      φ.hom ≫ formalPushforwardComparison p f I G =
        formalModificationAdjoint p f I F _ β.hom ∧ AdicSystem.HasBoundedDefects K φ := by
  let := QuasiCompact.compactSpace_of_compactSpace f
  let φ := globalFormalModificationComparison p f I F G β.hom
  have hφ := globalFormalModificationComparison_diagram p f I F G β.hom
  exact ⟨φ, hφ, formalModificationComparison_hasBoundedDefects p f I F G β φ hφ K V hV⟩

end AlgebraicGeometry.Scheme.Modules.Coherent
