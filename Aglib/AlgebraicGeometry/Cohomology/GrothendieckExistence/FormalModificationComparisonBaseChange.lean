/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.FormalModificationAdjointBaseChange
public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.FormalPushforwardOpenComparison

/-! # Base change of the original modification comparison equation

Pulling back the actual comparison and composing the original proper-pushforward
mate preserves the specified upstairs adjunction equation. This applies to open
restrictions and completed bases alike, without stagewise injectivity.
-/

@[expose] public noncomputable section
open CategoryTheory Opposite
namespace AlgebraicGeometry.Scheme.Modules.Coherent
universe u
variable {R : Type u} [CommRing R]
  {X Y X' Y' : Scheme.{u}}
  [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
  [IsLocallyNoetherian X'] [IsLocallyNoetherian Y']
  (a : Y' ⟶ Y) (b : Y' ⟶ X') (p : Y ⟶ X) (g : X' ⟶ X)
  [IsProper p] [IsProper b]
  (h : IsPullback a b p g) (f : X ⟶ Spec (CommRingCat.of R)) (I : Ideal R)
  (F : AdicSystem X (idealThickeningIdealSheaf f I)) (G : Y.CoherentSheaf)

local instance : G.obj.IsQuasicoherent :=
  QuasiCoherent.quasicoherent_of_affineCharts _ (fun B j _ => (G.property B j).1)
local instance : ((pushforward p).obj G.obj).IsQuasicoherent :=
  QuasiCoherent.quasicoherent_of_affineCharts _
    (fun B j _ => ((properPushforwardCoefficient p G).property B j).1)

/-- The native proper-pushforward mate as a morphism of coherent coefficients. -/
def properPushforwardBaseChangeCoefficient :
    (coherentPullback g).obj (properPushforwardCoefficient p G) ⟶
      properPushforwardCoefficient b ((coherentPullback a).obj G) :=
  ObjectProperty.homMk ((cartesianBaseChangeMap a b p g h).app G.obj)

/-- Compose the original factorization using whole native unit packets before
specializing any quotient object or adjunction component. -/
theorem compositeAdjoint_of_unitPackets
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    (P : D ⥤ C) (T : C ⥤ C') (H : D ⥤ D') (S : D' ⥤ C')
    (bc : P ⋙ T ⟶ H ⋙ S) (N : D)
    (A : ℕᵒᵖ ⥤ C) (Q : ℕᵒᵖ ⥤ D) (A' B' : ℕᵒᵖ ⥤ C') (Q' : ℕᵒᵖ ⥤ D')
    (u : ∀ n, P.obj N ⟶ A.obj (op n)) (v : ∀ n, N ⟶ Q.obj (op n))
    (u₁ : ∀ n, T.obj (P.obj N) ⟶ A'.obj (op n))
    (u₂ : ∀ n, S.obj (H.obj N) ⟶ B'.obj (op n))
    (v' : ∀ n, H.obj N ⟶ Q'.obj (op n))
    (cψ : {ψ : A ⟶ Q ⋙ P // ∀ n, u n ≫ ψ.app (op n) = P.map (v n)})
    (cψ' : {ψ : B' ⟶ Q' ⋙ S // ∀ n, u₂ n ≫ ψ.app (op n) = S.map (v' n)})
    (cc : {e : A ⋙ T ≅ A' // ∀ n, T.map (u n) ≫ e.hom.app (op n) = u₁ n})
    (ck : {k : A' ⟶ B' // ∀ n, u₁ n ≫ k.app (op n) = bc.app N ≫ u₂ n})
    (d : ∀ n, {e : H.obj (Q.obj (op n)) ≅ Q'.obj (op n) //
      H.map (v n) ≫ e.hom = v' n})
    (hu : ∀ n, Epi (T.map (u n)))
    (L₀ : C ⥤ D) (adj₀ : L₀ ⊣ P) (L : C' ⥤ D') (adj : L ⊣ S)
    (sq : T ⋙ L ≅ L₀ ⋙ H) (F : ℕᵒᵖ ⥤ C) (β : F ⋙ L₀ ≅ Q)
    (cβ : {e : (F ⋙ T) ⋙ L ≅ Q' // ∀ n, e.hom.app (op n) =
      sq.hom.app (F.obj (op n)) ≫ H.map (β.hom.app (op n)) ≫ (d n).val.hom})
    (α : F ⟶ A) (c₀ : A ⋙ T ≅ A') (hc₀ : cc.val = c₀)
    (hα : α ≫ cψ.val = (adj₀.whiskerRight ℕᵒᵖ).homEquiv _ _ β.hom)
    (hm : ∀ (M : C) (V : D) (e : L₀.obj M ⟶ V),
      T.map (adj₀.homEquiv _ _ e) ≫ bc.app V =
        adj.homEquiv _ _ (sq.hom.app M ≫ H.map e)) :
    (Functor.whiskerRight α T ≫ c₀.hom ≫ ck.val) ≫ cψ'.val =
      (adj.whiskerRight ℕᵒᵖ).homEquiv _ _ cβ.val.hom := by
  rw [← hc₀]
  apply NatTrans.ext
  funext ⟨n⟩
  have hs := diagramSquare_of_unitPackets P T H S bc N A Q A' B' Q'
    u v u₁ u₂ v' cψ cψ' cc ck d hu n
  have ha := NatTrans.congr_app hα (op n)
  change α.app (op n) ≫ cψ.val.app (op n) =
    (((adj₀.whiskerRight ℕᵒᵖ).unit.app F).app (op n)) ≫ P.map (β.hom.app (op n)) at ha
  rw [Adjunction.whiskerRight_unit_app_app] at ha
  change α.app (op n) ≫ cψ.val.app (op n) =
    adj₀.homEquiv _ _ (β.hom.app (op n)) at ha
  change (T.map (α.app (op n)) ≫ cc.val.hom.app (op n) ≫ ck.val.app (op n)) ≫
    cψ'.val.app (op n) =
      (((adj.whiskerRight ℕᵒᵖ).unit.app (F ⋙ T)).app (op n)) ≫
        S.map (cβ.val.hom.app (op n))
  rw [Category.assoc, Category.assoc, ← hs, ← T.map_comp_assoc, ha,
    ← Category.assoc, hm, Adjunction.whiskerRight_unit_app_app]
  change adj.homEquiv _ _ (sq.hom.app (F.obj (op n)) ≫ H.map (β.hom.app (op n))) ≫
    S.map (d n).val.hom = adj.homEquiv _ _ (cβ.val.hom.app (op n))
  rw [← adj.homEquiv_naturality_right, Category.assoc, ← cβ.property n]
  rfl

/-- Construct the literal original composite and all its conditional laws together. -/
def formalCompositeDataOfUnitPackets
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    (P : D ⥤ C) (T : C ⥤ C') (H : D ⥤ D') (S : D' ⥤ C')
    (bc : P ⋙ T ⟶ H ⋙ S) (N : D)
    (A : ℕᵒᵖ ⥤ C) (Q : ℕᵒᵖ ⥤ D) (A' B' : ℕᵒᵖ ⥤ C') (Q' : ℕᵒᵖ ⥤ D')
    (ℙ : ObjectProperty (ℕᵒᵖ ⥤ C'))
    (hA : ℙ (A ⋙ T)) (hA' : ℙ A') (hB' : ℙ B')
    (u : ∀ n, P.obj N ⟶ A.obj (op n)) (v : ∀ n, N ⟶ Q.obj (op n))
    (u₁ : ∀ n, T.obj (P.obj N) ⟶ A'.obj (op n))
    (u₂ : ∀ n, S.obj (H.obj N) ⟶ B'.obj (op n))
    (v' : ∀ n, H.obj N ⟶ Q'.obj (op n))
    (cψ : {ψ : A ⟶ Q ⋙ P // ∀ n, u n ≫ ψ.app (op n) = P.map (v n)})
    (cψ' : {ψ : B' ⟶ Q' ⋙ S // ∀ n, u₂ n ≫ ψ.app (op n) = S.map (v' n)})
    (cc : {e : (⟨A ⋙ T, hA⟩ : ℙ.FullSubcategory) ≅ ⟨A', hA'⟩ //
      ∀ n, T.map (u n) ≫ e.hom.hom.app (op n) = u₁ n})
    (ck : {k : (⟨A', hA'⟩ : ℙ.FullSubcategory) ⟶ ⟨B', hB'⟩ //
      ∀ n, u₁ n ≫ k.hom.app (op n) = bc.app N ≫ u₂ n})
    (d : ∀ n, {e : H.obj (Q.obj (op n)) ≅ Q'.obj (op n) //
      H.map (v n) ≫ e.hom = v' n})
    (hu : ∀ n, Epi (T.map (u n)))
    (L₀ : C ⥤ D) (adj₀ : L₀ ⊣ P) (L : C' ⥤ D') (adj : L ⊣ S)
    (sq : T ⋙ L ≅ L₀ ⋙ H) (F : ℕᵒᵖ ⥤ C) (hF : ℙ (F ⋙ T))
    (B : Type*) (β : B → (F ⋙ L₀ ≅ Q))
    (cβ : ∀ t : B, {e : (F ⋙ T) ⋙ L ≅ Q' // ∀ n, e.hom.app (op n) =
      sq.hom.app (F.obj (op n)) ≫ H.map ((β t).hom.app (op n)) ≫ (d n).val.hom})
    (α : F ⟶ A)
    (α' : (⟨F ⋙ T, hF⟩ : ℙ.FullSubcategory) ⟶ ⟨A ⋙ T, hA⟩)
    (hα' : α'.hom = Functor.whiskerRight α T)
    (γ : B → (F ⟶ Q ⋙ P))
    (hγ : ∀ t, γ t = (adj₀.whiskerRight ℕᵒᵖ).homEquiv _ _ (β t).hom)
    (γ' : B → (F ⋙ T ⟶ Q' ⋙ S))
    (hγ' : ∀ t, γ' t = (adj.whiskerRight ℕᵒᵖ).homEquiv _ _ (cβ t).val.hom)
    (hm : ∀ (M : C) (V : D) (e : L₀.obj M ⟶ V),
      T.map (adj₀.homEquiv _ _ e) ≫ bc.app V =
        adj.homEquiv _ _ (sq.hom.app M ≫ H.map e)) :
    {m : (⟨F ⋙ T, hF⟩ : ℙ.FullSubcategory) ⟶ ⟨B', hB'⟩ //
      m = α' ≫ cc.val.hom ≫ ck.val ∧
      ∀ t, α ≫ cψ.val = γ t → m.hom ≫ cψ'.val = γ' t} := by
  refine ⟨α' ≫ cc.val.hom ≫ ck.val, rfl, ?_⟩
  intro t ht
  have hh := compositeAdjoint_of_unitPackets P T H S bc N A Q A' B' Q'
    u v u₁ u₂ v' cψ cψ' ⟨ℙ.ι.mapIso cc.val, cc.property⟩
    ⟨ck.val.hom, ck.property⟩ d hu L₀ adj₀ L adj sq F (β t) (cβ t) α
    (ℙ.ι.mapIso cc.val) rfl (ht.trans (hγ t)) hm
  change (α'.hom ≫ cc.val.hom.hom ≫ ck.val.hom) ≫ cψ'.val = γ' t
  rw [hα', hγ' t]
  exact hh

/-- Completion of the native coherent map, with its original unit family. -/
def completionHomUnitComparison {Z : Scheme.{u}} [IsLocallyNoetherian Z]
    (J : Z.IdealSheafData) {M N : Z.CoherentSheaf} (e : M ⟶ N) :
    {e' : (completionFunctor Z J).obj M ⟶ (completionFunctor Z J).obj N //
      ∀ n, (idealSheafQuotientUnit Z (J ^ n)).app M.obj ≫ e'.hom.app (op n) =
        e.hom ≫ (idealSheafQuotientUnit Z (J ^ n)).app N.obj} := by
  refine ⟨(completionFunctor Z J).map e, ?_⟩
  intro n
  exact ((idealSheafQuotientUnit Z (J ^ n)).naturality e.hom).symm

/-- The original composite together with every specified-beta equation.
The map itself is independent of beta and of its factorization hypothesis. -/
def formalModificationComparisonBaseChangeData
    (α : F ⟶ (completionFunctor X (idealThickeningIdealSheaf f I)).obj
      (properPushforwardCoefficient p G)) :
    {m : (baseIdealPullbackFunctor g f I).obj F ⟶
      (completionFunctor X' (idealThickeningIdealSheaf (g ≫ f) I)).obj
        (properPushforwardCoefficient b ((coherentPullback a).obj G)) //
      m = (baseIdealPullbackFunctor g f I).map α ≫
        (baseIdealPullbackCompletionIso g f I (properPushforwardCoefficient p G)).hom ≫
        (completionFunctor X' (idealThickeningIdealSheaf (g ≫ f) I)).map
          (properPushforwardBaseChangeCoefficient a b p g h G) ∧
      ∀ β : (baseIdealPullbackFunctor p f I).obj F ≅
          (completionFunctor Y (idealThickeningIdealSheaf (p ≫ f) I)).obj G,
        α.hom ≫ formalPushforwardComparison p f I G =
            formalModificationAdjoint p f I F _ β.hom →
        m.hom ≫ formalPushforwardComparison b (g ≫ f) I ((coherentPullback a).obj G) =
          formalModificationAdjoint b (g ≫ f) I
            ((baseIdealPullbackFunctor g f I).obj F) _
            (formalModificationBaseChangeIso a b p g h.w f I F G β).hom} := by
  exact formalCompositeDataOfUnitPackets
    (pushforward p) (pullback g) (pullback a)
    (pushforward b) (cartesianBaseChangeMap a b p g h) G.obj
    (idealSheafQuotientTower X (idealThickeningIdealSheaf f I) ((pushforward p).obj G.obj))
    (idealSheafQuotientTower Y (idealThickeningIdealSheaf (p ≫ f) I) G.obj)
    (idealSheafQuotientTower X' (idealThickeningIdealSheaf (g ≫ f) I)
      ((pullback g).obj ((pushforward p).obj G.obj)))
    (idealSheafQuotientTower X' (idealThickeningIdealSheaf (g ≫ f) I)
      ((pushforward b).obj ((pullback a).obj G.obj)))
    (idealSheafQuotientTower Y' (idealThickeningIdealSheaf (b ≫ (g ≫ f)) I)
      ((pullback a).obj G.obj))
    _
    (((baseIdealPullbackFunctor g f I).obj
      ((completionFunctor X (idealThickeningIdealSheaf f I)).obj
        (properPushforwardCoefficient p G))).property)
    (((completionFunctor X' (idealThickeningIdealSheaf (g ≫ f) I)).obj
      ((coherentPullback g).obj (properPushforwardCoefficient p G))).property)
    (((completionFunctor X' (idealThickeningIdealSheaf (g ≫ f) I)).obj
      (properPushforwardCoefficient b ((coherentPullback a).obj G))).property)
    (fun k => (idealSheafQuotientUnit X (idealThickeningIdealSheaf f I ^ k)).app
      ((pushforward p).obj G.obj))
    (fun k => (idealSheafQuotientUnit Y (idealThickeningIdealSheaf (p ≫ f) I ^ k)).app
      G.obj)
    (fun k => (idealSheafQuotientUnit X' (idealThickeningIdealSheaf (g ≫ f) I ^ k)).app
      ((pullback g).obj ((pushforward p).obj G.obj)))
    (fun k => (idealSheafQuotientUnit X' (idealThickeningIdealSheaf (g ≫ f) I ^ k)).app
      ((pushforward b).obj ((pullback a).obj G.obj)))
    (fun k => (idealSheafQuotientUnit Y'
      (idealThickeningIdealSheaf (b ≫ (g ≫ f)) I ^ k)).app ((pullback a).obj G.obj))
    (formalPushforwardComparisonData p f I G)
    (formalPushforwardComparisonData b (g ≫ f) I ((coherentPullback a).obj G))
    (originalFormalPullbackCompletionUnitComparison g f I (properPushforwardCoefficient p G))
    (completionHomUnitComparison (idealThickeningIdealSheaf (g ≫ f) I)
      (properPushforwardBaseChangeCoefficient a b p g h G))
    (fun k => squarePullbackQuotientComparisonOfComm a b p g h.w f I G k)
    (fun k => by
      let : Epi ((idealSheafQuotientUnit X
          (idealThickeningIdealSheaf f I ^ k)).app ((pushforward p).obj G.obj)) :=
        pullbackPushforwardUnit_epi
          (idealThickeningIdealSheaf f I ^ k).subschemeι ((pushforward p).obj G.obj)
      exact (pullback g).map_epi
        ((idealSheafQuotientUnit X (idealThickeningIdealSheaf f I ^ k)).app
          ((pushforward p).obj G.obj)))
    (pullback p) (pullbackPushforwardAdjunction p)
    (pullback b) (pullbackPushforwardAdjunction b) (pullbackSquareIso a b p g h.w) F.obj
    (((baseIdealPullbackFunctor g f I).obj F).property)
    ((baseIdealPullbackFunctor p f I).obj F ≅
      (completionFunctor Y (idealThickeningIdealSheaf (p ≫ f) I)).obj G)
    (fun β => (adicSystemToDiagram Y (idealThickeningIdealSheaf (p ≫ f) I)).mapIso β)
    (formalModificationBaseChangeData a b p g h.w f I F G) α.hom
    ((baseIdealPullbackFunctor g f I).map α) rfl
    (fun β => formalModificationAdjoint p f I F _ β.hom) (fun _ => rfl)
    (fun β => formalModificationAdjoint b (g ≫ f) I
      ((baseIdealPullbackFunctor g f I).obj F) _
      (formalModificationBaseChangeIso a b p g h.w f I F G β).hom)
    (fun _ => rfl) (cartesianBaseChangeMap_adjoint a b p g h)

/-- Pullback of the original formal map, followed by the original quotient
comparison and the original coherent pushforward mate. -/
def formalModificationComparisonBaseChange
    (α : F ⟶ (completionFunctor X (idealThickeningIdealSheaf f I)).obj
      (properPushforwardCoefficient p G)) :
    (baseIdealPullbackFunctor g f I).obj F ⟶
      (completionFunctor X' (idealThickeningIdealSheaf (g ≫ f) I)).obj
        (properPushforwardCoefficient b ((coherentPullback a).obj G)) :=
  (formalModificationComparisonBaseChangeData a b p g h f I F G α).val

/-- The projected map is exactly the original native three-factor composite. -/
theorem formalModificationComparisonBaseChange_eq
    (α : F ⟶ (completionFunctor X (idealThickeningIdealSheaf f I)).obj
      (properPushforwardCoefficient p G)) :
    formalModificationComparisonBaseChange a b p g h f I F G α =
      (baseIdealPullbackFunctor g f I).map α ≫
        (baseIdealPullbackCompletionIso g f I (properPushforwardCoefficient p G)).hom ≫
        (completionFunctor X' (idealThickeningIdealSheaf (g ≫ f) I)).map
          (properPushforwardBaseChangeCoefficient a b p g h G) :=
  (formalModificationComparisonBaseChangeData a b p g h f I F G α).property.1

/-- Base change preserves the whole original adjunction equation. -/
theorem formalModificationComparisonBaseChange_diagram
    (β : (baseIdealPullbackFunctor p f I).obj F ≅
      (completionFunctor Y (idealThickeningIdealSheaf (p ≫ f) I)).obj G)
    (α : F ⟶ (completionFunctor X (idealThickeningIdealSheaf f I)).obj
      (properPushforwardCoefficient p G))
    (hα : α.hom ≫ formalPushforwardComparison p f I G =
      formalModificationAdjoint p f I F _ β.hom) :
    (formalModificationComparisonBaseChange a b p g h f I F G α).hom ≫
        formalPushforwardComparison b (g ≫ f) I ((coherentPullback a).obj G) =
      formalModificationAdjoint b (g ≫ f) I
        ((baseIdealPullbackFunctor g f I).obj F) _
        (formalModificationBaseChangeIso a b p g h.w f I F G β).hom :=
  (formalModificationComparisonBaseChangeData a b p g h f I F G α).property.2 β hα

end AlgebraicGeometry.Scheme.Modules.Coherent
