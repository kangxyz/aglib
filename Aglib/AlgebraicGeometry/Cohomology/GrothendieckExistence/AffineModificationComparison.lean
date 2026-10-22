/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Iso.CertifiedHomTransport
public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.AffineFormalComparison
public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.AffinePushforwardLimitComparison

/-! # The original affine formal modification comparison

The comparison uses the actual proper formal-functions equivalence. Its input
is the specified upstairs formal map, not an assumed bijectivity statement for
an unspecified limit comparison. The ambient pushforward tower is not asserted
to be adic and the individual comparison stages need not be injective.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme.Modules.Coherent

universe u
variable {B : CommRingCat.{u}} [IsNoetherianRing B]
  {Y : Scheme.{u}} [IsLocallyNoetherian Y]
  (p : Y ⟶ Spec B) [IsProper p] (J : Ideal B)
  (F : AdicSystem (Spec B) (idealThickeningIdealSheaf (𝟙 (Spec B)) J))
  (G : Y.CoherentSheaf)
  (β : (baseIdealPullbackFunctor p (𝟙 (Spec B)) J).obj F ⟶
    (completionFunctor Y (idealThickeningIdealSheaf (p ≫ 𝟙 (Spec B)) J)).obj G)

/-- The same native associator and target-ideal transport used by the original ψ. -/
def affineModificationTargetIso :
    (((completionFunctor Y (idealThickeningIdealSheaf (p ≫ 𝟙 (Spec B)) J)).obj G).obj ⋙
      pushforward p) ⋙ moduleSpecΓFunctor ≅ affinePushforwardCompletionTower p J G :=
  Functor.associator _ _ _ ≪≫ eqToIso
    (congrArg (fun q : Y ⟶ Spec B =>
      idealSheafQuotientTower Y (idealThickeningIdealSheaf q J) G.obj ⋙
        pushforward p ⋙ moduleSpecΓFunctor) (Category.comp_id p))

/-- The original affine ψ is the original sheaf ψ with its one common target transport. -/
theorem affinePushforwardComparison_eq_whisker :
    affinePushforwardComparison p J G =
      Functor.whiskerRight (formalPushforwardComparison p (𝟙 (Spec B)) J G)
        moduleSpecΓFunctor ≫ (affineModificationTargetIso p J G).hom := by
  dsimp only [affinePushforwardComparison, affinePushforwardComparisonData, id]
  refine (certifiedHomTransport_val (C := ℕᵒᵖ ⥤ ModuleCat.{u} B)
    (fun q : Y ⟶ Spec B =>
      idealSheafQuotientTower Y (idealThickeningIdealSheaf q J) G.obj ⋙
        pushforward p ⋙ moduleSpecΓFunctor)
    (idealSheafQuotientTower (Spec B) (idealThickeningIdealSheaf (𝟙 (Spec B)) J)
      ((pushforward p).obj G.obj) ⋙ moduleSpecΓFunctor)
    (fun q α => ∀ n, moduleSpecΓFunctor.map
      ((idealSheafQuotientUnit (Spec B) (idealThickeningIdealSheaf (𝟙 (Spec B)) J ^ n)).app
        ((pushforward p).obj G.obj)) ≫ NatTrans.app α (op n) =
      moduleSpecΓFunctor.map ((pushforward p).map
        ((idealSheafQuotientUnit Y (idealThickeningIdealSheaf q J ^ n)).app G.obj)))
    (Category.comp_id p) _).trans ?_
  simp only [whiskerOriginalUnitComparison, affineModificationTargetIso,
    Iso.trans_hom, formalPushforwardComparison, Category.assoc]
  dsimp only [completionFunctor, eqToIso]
  rfl

/-- Original adjunction on β with precisely the same target normalization as ψ. -/
def affineModificationAdjoint :
    F.affineSectionsTower ⟶ affinePushforwardCompletionTower p J G :=
  Functor.whiskerRight (formalModificationAdjoint p (𝟙 (Spec B)) J F _ β)
    moduleSpecΓFunctor ≫ (affineModificationTargetIso p J G).hom

/-- Assemble the native affine map and whole normalized diagram/uniqueness together. -/
def originalAffineComparisonData {A : CommRingCat.{u}} [IsNoetherianRing A]
    {K : (Spec A).IdealSheafData} (M N : AdicSystem (Spec A) K)
    {T : ℕᵒᵖ ⥤ ModuleCat.{u} A} (ψ : N.affineSectionsTower ⟶ T)
    (hψ : originalLimitBijective (originalDiagramSectionsMap ψ))
    (γ : M.affineSectionsTower ⟶ T) :
    {α : M ⟶ N // Functor.whiskerRight α.hom moduleSpecΓFunctor ≫ ψ = γ ∧
      ∀ a : M ⟶ N, Functor.whiskerRight a.hom moduleSpecΓFunctor ≫ ψ = γ → a = α} := by
  let α := M.affineFormalComparison N (fun j => (ψ.app j).hom)
    (fun a x => ConcreteCategory.congr_hom (ψ.naturality a) x) hψ
    (fun j => (γ.app j).hom)
    (fun a x => ConcreteCategory.congr_hom (γ.naturality a) x)
  refine ⟨α, ?_, ?_⟩
  · apply NatTrans.ext
    funext j
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change (ψ.app j).hom ((moduleSpecΓFunctor.map (α.hom.app j)).hom x) =
      (γ.app j).hom x
    exact M.affineFormalComparison_diagram N (fun k => (ψ.app k).hom)
      (fun a x => ConcreteCategory.congr_hom (ψ.naturality a) x) hψ
      (fun k => (γ.app k).hom)
      (fun a x => ConcreteCategory.congr_hom (γ.naturality a) x) j x
  · intro a ha
    apply M.affineFormalComparison_unique N _ _ _ _ _ a
    intro j x
    exact ConcreteCategory.congr_hom (congr_app ha j) x

/-- Cancel only the common target iso, not any original comparison stage. -/
theorem normalizedDiagram_iff {C : Type*} [Category C] {W X Y Z : C}
    (a : W ⟶ X) (ψ : X ⟶ Y) (γ : W ⟶ Y) (e : Y ≅ Z) :
    a ≫ (ψ ≫ e.hom) = γ ≫ e.hom ↔ a ≫ ψ = γ := by
  rw [← Category.assoc]
  exact cancel_mono e.hom

/-- Normalize a fixed original arrow without rewriting its certificate's dependent type. -/
theorem originalDiagram_of_normalized {C : Type*} [Category C] {W X Y Z : C}
    (a : W ⟶ X) (ψ : X ⟶ Y) (ψn : X ⟶ Z) (γ : W ⟶ Y) (e : Y ≅ Z)
    (hψ : ψn = ψ ≫ e.hom) (h : a ≫ ψn = γ ≫ e.hom) : a ≫ ψ = γ :=
  (normalizedDiagram_iff a ψ γ e).mp
    ((congrArg (fun t => a ≫ t) hψ).symm.trans h)

/-- Recover the original sheaf diagram and whole-family uniqueness while all
coefficients and diagrams are still abstract. The ambient tower is only coherent
stagewise; no adic compatibility of that tower is assumed. -/
def originalAffineSheafComparisonData {A : CommRingCat.{u}} [IsNoetherianRing A]
    {K : (Spec A).IdealSheafData} (M N : AdicSystem (Spec A) K)
    (T : ℕᵒᵖ ⥤ (Spec A).Modules)
    (hT : ∀ j, QuasiCoherent.affineLocallyFiniteType (Spec A) (T.obj j))
    {U : ℕᵒᵖ ⥤ ModuleCat.{u} A} (ψn : N.affineSectionsTower ⟶ U)
    (hψ : originalLimitBijective (originalDiagramSectionsMap ψn))
    (ψ : N.obj ⟶ T) (γ : M.obj ⟶ T)
    (e : T ⋙ moduleSpecΓFunctor ≅ U)
    (he : ψn = Functor.whiskerRight ψ moduleSpecΓFunctor ≫ e.hom) :
    {α : M ⟶ N // α.hom ≫ ψ = γ ∧ ∀ a : M ⟶ N, a.hom ≫ ψ = γ → a = α} := by
  let c := originalAffineComparisonData M N ψn hψ
    (Functor.whiskerRight γ moduleSpecΓFunctor ≫ e.hom)
  have heq (a : M ⟶ N) :
      Functor.whiskerRight a.hom moduleSpecΓFunctor ≫ ψn =
          Functor.whiskerRight γ moduleSpecΓFunctor ≫ e.hom ↔ a.hom ≫ ψ = γ := by
    constructor
    · intro ha
      have hh := originalDiagram_of_normalized _ _ _ _ e he ha
      apply NatTrans.ext
      funext j
      apply Coherent.affineHom_ext (M.affineCoefficient j) ⟨T.obj j, hT j⟩
      exact (moduleSpecΓFunctor.map_comp (a.hom.app j) (ψ.app j)).trans (congr_app hh j)
    · intro ha
      have hh : Functor.whiskerRight a.hom moduleSpecΓFunctor ≫
          Functor.whiskerRight ψ moduleSpecΓFunctor =
            Functor.whiskerRight γ moduleSpecΓFunctor := by
        simpa only [Functor.whiskerRight_comp] using
          congrArg (fun η => Functor.whiskerRight η moduleSpecΓFunctor) ha
      exact (congrArg (fun t => Functor.whiskerRight a.hom moduleSpecΓFunctor ≫ t) he).trans
        ((normalizedDiagram_iff _ _ _ e).mpr hh)
  exact ⟨c.val, (heq c.val).mp c.property.1,
    fun a ha => c.property.2 a ((heq a).mpr ha)⟩

/-- Actual formal functions supplies the original map, original sheaf diagram,
and whole-family uniqueness as one packet. -/
def affineModificationComparisonData :
    {α : F ⟶ (completionFunctor (Spec B)
        (idealThickeningIdealSheaf (𝟙 (Spec B)) J)).obj (properPushforwardCoefficient p G) //
      α.hom ≫ formalPushforwardComparison p (𝟙 (Spec B)) J G =
        formalModificationAdjoint p (𝟙 (Spec B)) J F _ β ∧
      ∀ a : F ⟶ (completionFunctor (Spec B)
          (idealThickeningIdealSheaf (𝟙 (Spec B)) J)).obj (properPushforwardCoefficient p G),
        a.hom ≫ formalPushforwardComparison p (𝟙 (Spec B)) J G =
          formalModificationAdjoint p (𝟙 (Spec B)) J F _ β → a = α} := by
  let H := (completionFunctor Y
    (idealThickeningIdealSheaf (p ≫ 𝟙 (Spec B)) J)).obj G
  exact originalAffineSheafComparisonData F
    ((completionFunctor (Spec B) (idealThickeningIdealSheaf (𝟙 (Spec B)) J)).obj
      (properPushforwardCoefficient p G)) (H.obj ⋙ pushforward p)
    (fun j => (properPushforwardCoefficient p
      ⟨H.obj.obj j, H.property.coherent j.unop⟩).property)
    (affinePushforwardComparison p J G) (affinePushforwardLimitMap_bijective p J G)
    (formalPushforwardComparison p (𝟙 (Spec B)) J G)
    (formalModificationAdjoint p (𝟙 (Spec B)) J F _ β)
    (affineModificationTargetIso p J G) (affinePushforwardComparison_eq_whisker p J G)

/-- The actual map is projected only after its original compatible-family construction. -/
def affineModificationComparison : F ⟶
    (completionFunctor (Spec B) (idealThickeningIdealSheaf (𝟙 (Spec B)) J)).obj
      (properPushforwardCoefficient p G) :=
  (affineModificationComparisonData p J F G β).val

/-- The original equation holds in the original sheaf-valued diagrams. -/
theorem affineModificationComparison_original_diagram :
    (affineModificationComparison p J F G β).hom ≫
        formalPushforwardComparison p (𝟙 (Spec B)) J G =
      formalModificationAdjoint p (𝟙 (Spec B)) J F _ β :=
  (affineModificationComparisonData p J F G β).property.1

/-- The original sheaf-valued equation determines the entire formal map. -/
theorem affineModificationComparison_original_unique
    (α : F ⟶ (completionFunctor (Spec B)
      (idealThickeningIdealSheaf (𝟙 (Spec B)) J)).obj (properPushforwardCoefficient p G))
    (hα : α.hom ≫ formalPushforwardComparison p (𝟙 (Spec B)) J G =
      formalModificationAdjoint p (𝟙 (Spec B)) J F _ β) :
    α = affineModificationComparison p J F G β :=
  (affineModificationComparisonData p J F G β).property.2 α hα

/-- The actual comparison is natural in the original formal source. The proof
uses uniqueness of the whole compatible family, not injectivity at one stage. -/
theorem affineModificationComparison_naturality
    (F' : AdicSystem (Spec B) (idealThickeningIdealSheaf (𝟙 (Spec B)) J))
    (e : F' ⟶ F) :
    e ≫ affineModificationComparison p J F G β =
      affineModificationComparison p J F' G
        ((baseIdealPullbackFunctor p (𝟙 (Spec B)) J).map e ≫ β) := by
  apply affineModificationComparison_original_unique
  change (e.hom ≫ (affineModificationComparison p J F G β).hom) ≫
      formalPushforwardComparison p (𝟙 (Spec B)) J G = _
  rw [Category.assoc, affineModificationComparison_original_diagram]
  exact (((pullbackPushforwardAdjunction p).whiskerRight ℕᵒᵖ).homEquiv_naturality_left
    e.hom β.hom).symm

end AlgebraicGeometry.Scheme.Modules.Coherent
