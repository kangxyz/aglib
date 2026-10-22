/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.FormalPushforwardDiagramBaseChange
public import Aglib.AlgebraicGeometry.Modules.BaseChange.OpenImmersion.Pullback

/-! # The original formal pushforward comparison on open charts

Both target identifications are the original open base-change mate. The
completion target is adic, while the ambient pushforward tower need not be.
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
  [IsOpenImmersion a] [IsOpenImmersion g] [IsProper p] [IsProper b]
  (h : IsPullback a b p g) (f : X ⟶ Spec (CommRingCat.of R)) (I : Ideal R)
  (G : Y.CoherentSheaf)

/-- Form the entire original open square under abstract unit certificates. -/
theorem openDiagramSquare_of_unitPackets
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    (P : D ⥤ C) (T : C ⥤ C') (H : D ⥤ D') (S : D' ⥤ C')
    (bc : P ⋙ T ⟶ H ⋙ S) [IsIso bc] (N : D)
    (A : ℕᵒᵖ ⥤ C) (Q : ℕᵒᵖ ⥤ D) (A' B' : ℕᵒᵖ ⥤ C') (Q' : ℕᵒᵖ ⥤ D')
    (u : ∀ n, P.obj N ⟶ A.obj (op n)) (v : ∀ n, N ⟶ Q.obj (op n))
    (u₁ : ∀ n, T.obj (P.obj N) ⟶ A'.obj (op n))
    (u₂ : ∀ n, S.obj (H.obj N) ⟶ B'.obj (op n))
    (v' : ∀ n, H.obj N ⟶ Q'.obj (op n))
    (cψ : {ψ : A ⟶ Q ⋙ P // ∀ n, u n ≫ ψ.app (op n) = P.map (v n)})
    (cψ' : {ψ : B' ⟶ Q' ⋙ S // ∀ n, u₂ n ≫ ψ.app (op n) = S.map (v' n)})
    (cc : {e : A ⋙ T ≅ A' // ∀ n, T.map (u n) ≫ e.hom.app (op n) = u₁ n})
    (ck : {k : A' ⟶ B' // ∀ n, u₁ n ≫ k.app (op n) = bc.app N ≫ u₂ n})
    (cd : {e : Q ⋙ H ≅ Q' // ∀ n,
      H.map (v n) ≫ e.hom.app (op n) = v' n})
    (hu : ∀ n, Epi (T.map (u n))) :
    Functor.whiskerRight cψ.val T ≫
        (Functor.associator Q P T ≪≫ Functor.isoWhiskerLeft Q (asIso bc) ≪≫
          (Functor.associator Q H S).symm ≪≫ Functor.isoWhiskerRight cd.val S).hom =
      (cc.val.hom ≫ ck.val) ≫ cψ'.val := by
  apply NatTrans.ext
  funext ⟨n⟩
  simpa only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Iso.app_hom, Functor.comp_obj,
    asIso_hom,
    Category.id_comp, Category.comp_id, Category.assoc] using
    diagramSquare_of_unitPackets P T H S bc N A Q A' B' Q' u v u₁ u₂ v'
      cψ cψ' cc ck (fun k => ⟨cd.val.app (op k), cd.property k⟩) hu n

/-- Open base change identifies the actual coherent pushforward coefficients. -/
def properPushforwardOpenCoefficientIso :
    (coherentPullback g).obj (properPushforwardCoefficient p G) ≅
      properPushforwardCoefficient b ((coherentPullback a).obj G) := by
  exact ObjectProperty.isoMk _
    (@asIso X'.Modules _ _ _ ((cartesianBaseChangeMap a b p g h).app G.obj)
      (isIso_cartesianBaseChangeMap_of_isOpenImmersion a b p g h G.obj))

/-- Retain a specified original iso together with its whole certificate. -/
def isoUnitComparisonWithValue {C : Type*} [Category C] {M N : C}
    (P : (M ≅ N) → Prop) (c : {e : M ≅ N // P e})
    (e : M ≅ N) (h : c.val = e) : {e' : M ≅ N // P e'} :=
  ⟨e, h ▸ c.property⟩

/-- The original pullback completion iso, with its original unit family. -/
def originalPullbackCompletionUnitComparison
    {Z W : Scheme.{u}} [IsLocallyNoetherian Z]
    (r : W ⟶ Z) (q : Z ⟶ Spec (CommRingCat.of R)) (J : Ideal R)
    (M : Z.CoherentSheaf) :
    {e : idealSheafQuotientTower Z (idealThickeningIdealSheaf q J) M.obj ⋙ pullback r ≅
      idealSheafQuotientTower W (idealThickeningIdealSheaf (r ≫ q) J)
        ((pullback r).obj M.obj) //
      ∀ n, (pullback r).map
        ((idealSheafQuotientUnit Z (idealThickeningIdealSheaf q J ^ n)).app M.obj) ≫
        e.hom.app (op n) =
          (idealSheafQuotientUnit W (idealThickeningIdealSheaf (r ≫ q) J ^ n)).app
            ((pullback r).obj M.obj)} :=
  isoUnitComparisonWithValue _ (pullbackCompletionDiagramComparison r q J M)
    (baseIdealPullbackCompletionDiagramIso r q J M)
    (pullbackCompletionDiagramComparison_val r q J M)

/-- Lift the original iso and its units together into the native formal category. -/
def originalFormalPullbackCompletionUnitComparison
    {Z W : Scheme.{u}} [IsLocallyNoetherian Z] [IsLocallyNoetherian W]
    (r : W ⟶ Z) (q : Z ⟶ Spec (CommRingCat.of R)) (J : Ideal R)
    (M : Z.CoherentSheaf) :
    {e : (baseIdealPullbackFunctor r q J).obj
        ((completionFunctor Z (idealThickeningIdealSheaf q J)).obj M) ≅
      (completionFunctor W (idealThickeningIdealSheaf (r ≫ q) J)).obj
        ((coherentPullback r).obj M) //
      ∀ n, (pullback r).map
        ((idealSheafQuotientUnit Z (idealThickeningIdealSheaf q J ^ n)).app M.obj) ≫
        e.hom.hom.app (op n) =
          (idealSheafQuotientUnit W (idealThickeningIdealSheaf (r ≫ q) J ^ n)).app
            ((pullback r).obj M.obj)} :=
  formalIsoComparisonOfDiagram _
    ((baseIdealPullbackFunctor r q J).obj
      ((completionFunctor Z (idealThickeningIdealSheaf q J)).obj M))
    ((completionFunctor W (idealThickeningIdealSheaf (r ≫ q) J)).obj
      ((coherentPullback r).obj M))
    (fun e => ∀ n, (pullback r).map
      ((idealSheafQuotientUnit Z (idealThickeningIdealSheaf q J ^ n)).app M.obj) ≫
      e.app (op n) =
        (idealSheafQuotientUnit W (idealThickeningIdealSheaf (r ≫ q) J ^ n)).app
          ((pullback r).obj M.obj))
    (originalPullbackCompletionUnitComparison r q J M)

/-- Completion of a specified coherent iso retains its entire original unit law. -/
def completionIsoUnitComparison {Z : Scheme.{u}} [IsLocallyNoetherian Z]
    (J : Z.IdealSheafData) {M N : Z.CoherentSheaf} (e : M ≅ N) :
    {e' : (completionFunctor Z J).obj M ≅ (completionFunctor Z J).obj N //
      ∀ n, (idealSheafQuotientUnit Z (J ^ n)).app M.obj ≫ e'.hom.hom.app (op n) =
        e.hom.hom ≫ (idealSheafQuotientUnit Z (J ^ n)).app N.obj} := by
  refine ⟨(completionFunctor Z J).mapIso e, ?_⟩
  intro n
  exact ((idealSheafQuotientUnit Z (J ^ n)).naturality e.hom.hom).symm

/-- Construct the original formal target iso, ambient iso, and their square
as one packet while all diagrams and unit laws are abstract. -/
def formalOpenDiagramComparisonData
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    (P : D ⥤ C) (T : C ⥤ C') (H : D ⥤ D') (S : D' ⥤ C')
    (bc : P ⋙ T ⟶ H ⋙ S) [IsIso bc] (N : D)
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
    (ck : {e : (⟨A', hA'⟩ : ℙ.FullSubcategory) ≅ ⟨B', hB'⟩ //
      ∀ n, u₁ n ≫ e.hom.hom.app (op n) = bc.app N ≫ u₂ n})
    (cd : {e : Q ⋙ H ≅ Q' // ∀ n,
      H.map (v n) ≫ e.hom.app (op n) = v' n})
    (hu : ∀ n, Epi (T.map (u n))) :
    {e : ((⟨A ⋙ T, hA⟩ : ℙ.FullSubcategory) ≅ ⟨B', hB'⟩) ×
        (((Q ⋙ P) ⋙ T) ≅ (Q' ⋙ S)) //
      Functor.whiskerRight cψ.val T ≫ e.2.hom = e.1.hom.hom ≫ cψ'.val} := by
  refine ⟨(cc.val ≪≫ ck.val,
    Functor.associator Q P T ≪≫ Functor.isoWhiskerLeft Q (asIso bc) ≪≫
      (Functor.associator Q H S).symm ≪≫ Functor.isoWhiskerRight cd.val S), ?_⟩
  exact openDiagramSquare_of_unitPackets P T H S bc N A Q A' B' Q' u v u₁ u₂ v'
    cψ cψ' ⟨ℙ.ι.mapIso cc.val, cc.property⟩ ⟨ck.val.hom.hom, ck.property⟩ cd hu

/-- The upstairs completion comparison, with the actual structural ideal. -/
def squarePullbackCompletionDiagramIso :
    ((completionFunctor Y (idealThickeningIdealSheaf (p ≫ f) I)).obj G).obj ⋙ pullback a ≅
      ((completionFunctor Y' (idealThickeningIdealSheaf (b ≫ (g ≫ f)) I)).obj
        ((coherentPullback a).obj G)).obj :=
  baseIdealPullbackCompletionDiagramIso a (p ≫ f) I G ≪≫
    eqToIso (congrArg (fun K => idealSheafQuotientTower Y' K ((pullback a).obj G.obj))
      (formalModificationBaseChange_ideal a b p g h.w f I))

/-- The original target and ambient comparisons together with their square. -/
def formalPushforwardOpenComparisonData :
    {e : ((baseIdealPullbackFunctor g f I).obj
        ((completionFunctor X (idealThickeningIdealSheaf f I)).obj
          (properPushforwardCoefficient p G)) ≅
      (completionFunctor X' (idealThickeningIdealSheaf (g ≫ f) I)).obj
        (properPushforwardCoefficient b ((coherentPullback a).obj G))) ×
      ((((completionFunctor Y (idealThickeningIdealSheaf (p ≫ f) I)).obj G).obj ⋙
          pushforward p) ⋙ pullback g ≅
        ((completionFunctor Y' (idealThickeningIdealSheaf (b ≫ (g ≫ f)) I)).obj
          ((coherentPullback a).obj G)).obj ⋙ pushforward b) //
      Functor.whiskerRight (formalPushforwardComparison p f I G) (pullback g) ≫
        e.2.hom = e.1.hom.hom ≫
          formalPushforwardComparison b (g ≫ f) I ((coherentPullback a).obj G)} := by
  letI : IsIso (cartesianBaseChangeMap a b p g h) :=
    (NatTrans.isIso_iff_isIso_app _).mpr
      (fun M => isIso_cartesianBaseChangeMap_of_isOpenImmersion a b p g h M)
  letI : ((pushforward p).obj G.obj).IsQuasicoherent :=
    QuasiCoherent.quasicoherent_of_affineCharts _
      (fun B j _ => ((properPushforwardCoefficient p G).property B j).1)
  exact formalOpenDiagramComparisonData (pushforward p) (pullback g) (pullback a)
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
    (completionIsoUnitComparison (idealThickeningIdealSheaf (g ≫ f) I)
      (properPushforwardOpenCoefficientIso a b p g h G))
    (transportDiagramUnitComparison
      (fun K => idealSheafQuotientTower Y' K ((pullback a).obj G.obj))
      (idealSheafQuotientTower Y (idealThickeningIdealSheaf (p ≫ f) I) G.obj ⋙ pullback a)
      ((pullback a).obj G.obj)
      (fun k => (pullback a).map
        ((idealSheafQuotientUnit Y (idealThickeningIdealSheaf (p ≫ f) I ^ k)).app G.obj))
      (fun K k => (idealSheafQuotientUnit Y' (K ^ k)).app ((pullback a).obj G.obj))
      (formalModificationBaseChange_ideal a b p g h.w f I)
      (originalPullbackCompletionUnitComparison a (p ≫ f) I G))
    (fun k => by
      let : Epi ((idealSheafQuotientUnit X
          (idealThickeningIdealSheaf f I ^ k)).app ((pushforward p).obj G.obj)) :=
        pullbackPushforwardUnit_epi
          (idealThickeningIdealSheaf f I ^ k).subschemeι ((pushforward p).obj G.obj)
      exact (pullback g).map_epi
        ((idealSheafQuotientUnit X (idealThickeningIdealSheaf f I ^ k)).app
          ((pushforward p).obj G.obj)))

/-- The original adic completion target on an open chart. -/
def formalPushforwardOpenTargetIso :
    (baseIdealPullbackFunctor g f I).obj
        ((completionFunctor X (idealThickeningIdealSheaf f I)).obj
          (properPushforwardCoefficient p G)) ≅
      (completionFunctor X' (idealThickeningIdealSheaf (g ≫ f) I)).obj
        (properPushforwardCoefficient b ((coherentPullback a).obj G)) :=
  (formalPushforwardOpenComparisonData a b p g h f I G).val.1

/-- The original ambient tower identification on an open chart. No adic
compatibility is asserted for either ambient tower. -/
def formalPushforwardOpenAmbientIso :
    (((completionFunctor Y (idealThickeningIdealSheaf (p ≫ f) I)).obj G).obj ⋙
      pushforward p) ⋙ pullback g ≅
    ((completionFunctor Y' (idealThickeningIdealSheaf (b ≫ (g ≫ f)) I)).obj
      ((coherentPullback a).obj G)).obj ⋙ pushforward b :=
  (formalPushforwardOpenComparisonData a b p g h f I G).val.2

/-- The original comparison square holds for the complete diagrams, not just
for an arbitrary identification of their objects. -/
theorem formalPushforwardOpenComparison_square :
    Functor.whiskerRight (formalPushforwardComparison p f I G) (pullback g) ≫
        (formalPushforwardOpenAmbientIso a b p g h f I G).hom =
      (formalPushforwardOpenTargetIso a b p g h f I G).hom.hom ≫
        formalPushforwardComparison b (g ≫ f) I ((coherentPullback a).obj G) :=
  (formalPushforwardOpenComparisonData a b p g h f I G).property

end AlgebraicGeometry.Scheme.Modules.Coherent
