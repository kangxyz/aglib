/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Blowup.AffineCenter.Restriction
public import Aglib.AlgebraicGeometry.Blowup.FlatBaseChange
public import Aglib.AlgebraicGeometry.Blowup.ProjectivePresentation.AffineRow
public import Aglib.AlgebraicGeometry.IdealSheaf.BaseChange.OpenImmersion
public import Aglib.AlgebraicGeometry.Modules.BaseChange.Affine.Square
public import Aglib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting

/-!
# Restriction of the original blowup presentation to affine frames

The blowup is restricted along an actual affine open of its original base.
Subsequent scalar change is arbitrary. The degree-one comparison retains the
full pulled ideal module, and the local coproduct row is the pullback of the
specified original row through this canonical comparison.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.Hom AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.BaseChange.Affine.Square
open AlgebraicGeometry.ProjectiveSpace.FromSections

universe u

namespace AlgebraicGeometry.Scheme.Blowup.ProjectivePresentation.Restriction

/-- The equation for the actual quotient maps and their specified comparisons. -/
def QuotientRestrictionEq {W S P T : Scheme.{u}}
    (u : S ⟶ W) (q : P ⟶ W) (p : T ⟶ S) (t : T ⟶ P)
    (M : W.Modules) (N : S.Modules) (L : P.Modules) (K : T.Modules)
    (eSource : (Modules.pullback t).obj ((Modules.pullback q).obj M) ≅
      (Modules.pullback p).obj ((Modules.pullback u).obj M))
    (eDegree : (Modules.pullback u).obj M ≅ N)
    (Q : (Modules.pullback q).obj M ⟶ L)
    (eLine : (Modules.pullback t).obj L ≅ K)
    (Q' : (Modules.pullback p).obj N ⟶ K) : Prop :=
  eSource.hom ≫ (Modules.pullback p).map eDegree.hom ≫ Q' =
    (Modules.pullback t).map Q ≫ eLine.hom

/-- The equation for one original row entry in the specified actual source frame. -/
def RowRestrictionEq {P S T : Scheme.{u}} (t : T ⟶ P) (p : T ⟶ S)
    (D L : P.Modules) (N : S.Modules) (K : T.Modules)
    (eSource : (Modules.pullback t).obj D ≅ SheafOfModules.unit T.ringCatSheaf)
    (d : D ⟶ L) (eLine : (Modules.pullback t).obj L ≅ K)
    (s : SheafOfModules.unit S.ringCatSheaf ⟶ N)
    (Q : (Modules.pullback p).obj N ⟶ K) : Prop :=
  eSource.inv ≫ (Modules.pullback t).map d ≫ eLine.hom = pullbackSection p s ≫ Q

private theorem pulledQuotient_constructor {X W : Scheme.{u}} {I : X.IdealSheafData}
    (B : BlowupDatum I) (f : W ⟶ X) :
    pulledTautologicalQuotient B f =
      (pullbackSquareIso (pullback.fst B.map f) (pullback.snd B.map f)
        B.map f pullback.condition).hom.app (idealModule I.subschemeι) ≫
          (Modules.pullback (pullback.fst B.map f)).map (tautologicalQuotient B) := rfl

section IdealComparison

variable {X Y : Scheme.{u}} (I : X.IdealSheafData) (v : Y ⟶ X)
  (J : Y.IdealSheafData) (hI : I.comap v = J)

/-- The actual map between the original centre and its specified inverse image. -/
def centreMap : J.subscheme ⟶ I.subscheme :=
  J.subschemeMap I v (by rw [← hI]; exact I.le_map_comap v)

@[reassoc]
theorem centreMap_ι : centreMap I v J hI ≫ I.subschemeι = J.subschemeι ≫ v :=
  IdealSheafData.subschemeMap_subschemeι _ _ _ _

theorem centre_isPullback :
    IsPullback (centreMap I v J hI) J.subschemeι I.subschemeι v := by
  apply IsPullback.flip
  apply isPullback_of_isClosedImmersion J.subschemeι I.subschemeι
    (centreMap I v J hI) v (centreMap_ι I v J hI).symm
  simpa only [IdealSheafData.ker_subschemeι] using hI

/-- The canonical comparison for this actual square of closed centres. -/
def idealComparison : (Modules.pullback v).obj (idealModule I.subschemeι) ⟶
    idealModule J.subschemeι :=
  idealPullbackMap I.subschemeι J.subschemeι v (centreMap I v J hI)
    (centreMap_ι I v J hI)

/-- The canonical comparison is inverted only along the specified open immersion. -/
def openIdealIso [IsOpenImmersion v] :
    (Modules.pullback v).obj (idealModule I.subschemeι) ≅ idealModule J.subschemeι := by
  let : IsIso (idealComparison I v J hI) :=
    idealPullbackMap_isIso_of_isOpenImmersion _ _ _ _ _ (centre_isPullback I v J hI)
  exact asIso (idealComparison I v J hI)

@[simp]
theorem openIdealIso_hom [IsOpenImmersion v] :
    (openIdealIso I v J hI).hom = idealComparison I v J hI := rfl

end IdealComparison

private theorem idealPullbackMap_changeBase
    {D D' X Y : Scheme.{u}} (i : D ⟶ X) (i' : D' ⟶ Y)
    (b b' : Y ⟶ X) (a a' : D' ⟶ D)
    (h : a ≫ i = i' ≫ b) (h' : a' ≫ i = i' ≫ b') (hb : b = b') :
    (pullbackCongr hb).hom.app (idealModule i) ≫ idealPullbackMap i i' b' a' h' =
      idealPullbackMap i i' b a h := by
  subst b'
  simpa [pullbackCongr] using idealPullbackMap_eq_of_same_base i i' b a' a h' h

private theorem idealPullbackMap_twoPaths
    {D₀ D₁ D₂ D₃ X₀ X₁ X₂ X₃ : Scheme.{u}}
    (i₀ : D₀ ⟶ X₀) (i₁ : D₁ ⟶ X₁) (i₂ : D₂ ⟶ X₂) (i₃ : D₃ ⟶ X₃)
    (v : X₁ ⟶ X₀) (b : X₂ ⟶ X₀) (r : X₃ ⟶ X₁) (g : X₃ ⟶ X₂)
    (hv : D₁ ⟶ D₀) (hb : D₂ ⟶ D₀) (hr : D₃ ⟶ D₁) (hg : D₃ ⟶ D₂)
    (wv : hv ≫ i₀ = i₁ ≫ v) (wb : hb ≫ i₀ = i₂ ≫ b)
    (wr : hr ≫ i₁ = i₃ ≫ r) (wg : hg ≫ i₂ = i₃ ≫ g)
    (w : g ≫ b = r ≫ v) :
    (Modules.pullback r).map (idealPullbackMap i₀ i₁ v hv wv) ≫
        idealPullbackMap i₁ i₃ r hr wr =
      (pullbackComp r v).hom.app (idealModule i₀) ≫
        (pullbackCongr w.symm).hom.app (idealModule i₀) ≫
          (pullbackComp g b).inv.app (idealModule i₀) ≫
            (Modules.pullback g).map (idealPullbackMap i₀ i₂ b hb wb) ≫
              idealPullbackMap i₂ i₃ g hg wg := by
  apply (cancel_epi ((pullbackComp r v).inv.app (idealModule i₀))).mp
  simp only [Iso.inv_hom_id_app_assoc]
  rw [idealPullbackMap_comp i₀ i₁ i₃ v r hv hr wv wr,
    idealPullbackMap_comp i₀ i₂ i₃ b g hb hg wb wg]
  exact (idealPullbackMap_changeBase i₀ i₃ (r ≫ v) (g ≫ b)
    (hr ≫ hv) (hg ≫ hb) _ _ w.symm).symm

section BlowupRestriction

variable {X : Scheme.{u}} {I : X.IdealSheafData} (B : BlowupDatum I)
  (V : X.affineOpens)

/-- The literal flat pullback along the affine open, with its actual section ideal. -/
def restrictedDatum : BlowupDatum (affineCenter Γ(X, V.val) (I.ideal V)) where
  Y := pullback B.map V.property.fromSpec
  map := pullback.snd B.map V.property.fromSpec
  cartier := by
    rw [← comap_fromSpec_eq_affineCenter I V]
    exact (flatPullbackDatum B V.property.fromSpec).cartier
  universal T t ht := by
    apply (flatPullbackDatum B V.property.fromSpec).universal T t
    rwa [comap_fromSpec_eq_affineCenter I V]

/-- The original first projection of the restricted blowup. -/
def toOriginal : (restrictedDatum B V).Y ⟶ B.Y :=
  pullback.fst B.map V.property.fromSpec

@[reassoc]
theorem toOriginal_map :
    toOriginal B V ≫ B.map = (restrictedDatum B V).map ≫ V.property.fromSpec :=
  pullback.condition

instance toOriginal_isOpenImmersion : IsOpenImmersion (toOriginal B V) :=
  inferInstanceAs (IsOpenImmersion (pullback.fst B.map V.property.fromSpec))

/-- The tautological centre is the actual inverse image along the open projection. -/
theorem tautologicalCentre_comap :
    (I.comap B.map).comap (toOriginal B V) =
      (affineCenter Γ(X, V.val) (I.ideal V)).comap (restrictedDatum B V).map := by
  rw [← IdealSheafData.comap_comp, toOriginal_map, IdealSheafData.comap_comp,
    comap_fromSpec_eq_affineCenter I V]

/-- The canonical restriction of the original invertible image ideal. -/
def tautologicalRestrictionIso :
    (Modules.pullback (toOriginal B V)).obj (tautologicalLine B).val ≅
      (tautologicalLine (restrictedDatum B V)).val :=
  openIdealIso (I.comap B.map) (toOriginal B V)
    ((affineCenter Γ(X, V.val) (I.ideal V)).comap (restrictedDatum B V).map)
    (tautologicalCentre_comap B V)

/-- The two original ways to pull the degree-one module to the restricted blowup. -/
def openDegreeSquareIso :
    (Modules.pullback (restrictedDatum B V).map).obj
        ((Modules.pullback V.property.fromSpec).obj (idealModule I.subschemeι)) ≅
      (Modules.pullback (toOriginal B V)).obj
        ((Modules.pullback B.map).obj (idealModule I.subschemeι)) :=
  (pullbackSquareIso (toOriginal B V) (restrictedDatum B V).map B.map
    V.property.fromSpec (toOriginal_map B V)).app (idealModule I.subschemeι)

/-- The canonical ideal comparison preserves the original quotient before
arbitrary scalar change. -/
theorem tautologicalRestrictionQuotient :
    (Modules.pullback (restrictedDatum B V).map).map
        (openIdealIso I V.property.fromSpec
          (affineCenter Γ(X, V.val) (I.ideal V)) (comap_fromSpec_eq_affineCenter I V)).hom ≫
      tautologicalQuotient (restrictedDatum B V) =
    (openDegreeSquareIso B V).hom ≫
      (Modules.pullback (toOriginal B V)).map (tautologicalQuotient B) ≫
        (tautologicalRestrictionIso B V).hom := by
  exact idealPullbackMap_twoPaths
    I.subschemeι (affineCenter Γ(X, V.val) (I.ideal V)).subschemeι
    (I.comap B.map).subschemeι
    ((affineCenter Γ(X, V.val) (I.ideal V)).comap (restrictedDatum B V).map).subschemeι
    V.property.fromSpec B.map (restrictedDatum B V).map (toOriginal B V)
    (centreMap I V.property.fromSpec (affineCenter Γ(X, V.val) (I.ideal V))
      (comap_fromSpec_eq_affineCenter I V))
    (ProjectivePresentation.centreMap B)
    (ProjectivePresentation.centreMap (restrictedDatum B V))
    (centreMap (I.comap B.map) (toOriginal B V)
      ((affineCenter Γ(X, V.val) (I.ideal V)).comap (restrictedDatum B V).map)
      (tautologicalCentre_comap B V))
    (centreMap_ι I V.property.fromSpec (affineCenter Γ(X, V.val) (I.ideal V))
      (comap_fromSpec_eq_affineCenter I V))
    (ProjectivePresentation.centreMap_ι B)
    (ProjectivePresentation.centreMap_ι (restrictedDatum B V))
    (centreMap_ι (I.comap B.map) (toOriginal B V)
      ((affineCenter Γ(X, V.val) (I.ideal V)).comap (restrictedDatum B V).map)
      (tautologicalCentre_comap B V)) (toOriginal_map B V)

variable {W : Scheme.{u}} (f : W ⟶ X) {S : Type u} [CommRing S]
  [Algebra Γ(X, V.val) S] (u : Spec (.of S) ⟶ W)
  (hsq : Spec.map (CommRingCat.ofHom (algebraMap Γ(X, V.val) S)) ≫
    V.property.fromSpec = u ≫ f)

/-- The actual affine ring map, with its source and target spectra fixed. -/
def affineScalarMap (V : X.affineOpens) (S : Type u) [CommRing S]
    [Algebra Γ(X, V.val) S] : Spec (.of S) ⟶ Spec Γ(X, V.val) :=
  Spec.map (CommRingCat.ofHom (algebraMap Γ(X, V.val) S))

local notation "s" => affineScalarMap V S

/-- Pasting the two literal fibre products, without a flatness assumption on s. -/
def affinePullbackIso :
    pullback (restrictedDatum B V).map s ≅ pullback B.map (u ≫ f) :=
  pullbackLeftPullbackSndIso B.map V.property.fromSpec s ≪≫ pullback.congrHom rfl hsq

@[reassoc (attr := simp)]
theorem affinePullbackIso_hom_fst :
    (affinePullbackIso B V f u hsq).hom ≫ pullback.fst B.map (u ≫ f) =
      pullback.fst (restrictedDatum B V).map s ≫ toOriginal B V := by
  simp only [affinePullbackIso, toOriginal, Iso.trans_hom, Category.assoc,
    pullback.congrHom_hom, pullback.map, pullback.lift_fst, Category.comp_id]
  exact pullbackLeftPullbackSndIso_hom_fst B.map V.property.fromSpec s

@[reassoc (attr := simp)]
theorem affinePullbackIso_hom_snd :
    (affinePullbackIso B V f u hsq).hom ≫ pullback.snd B.map (u ≫ f) =
      pullback.snd (restrictedDatum B V).map s := by
  simp only [affinePullbackIso, Iso.trans_hom, Category.assoc,
    pullback.congrHom_hom, pullback.map, pullback.lift_snd, Category.comp_id]
  exact pullbackLeftPullbackSndIso_hom_snd B.map V.property.fromSpec s

/-- The same local source identified with the literal base change of the global projection. -/
def baseChangeIso :
    pullback (restrictedDatum B V).map s ≅ pullback (pullback.snd B.map f) u :=
  affinePullbackIso B V f u hsq ≪≫ (pullbackLeftPullbackSndIso B.map f u).symm

@[reassoc (attr := simp)]
theorem baseChangeIso_hom_snd :
    (baseChangeIso B V f u hsq).hom ≫ pullback.snd (pullback.snd B.map f) u =
      pullback.snd (restrictedDatum B V).map s := by
  simp [baseChangeIso]

/-- The actual affine chart map into the original fibre product. -/
def chartMap : pullback (restrictedDatum B V).map s ⟶ pullback B.map f :=
  (baseChangeIso B V f u hsq).hom ≫ pullback.fst (pullback.snd B.map f) u

@[reassoc]
theorem chartMap_snd :
    chartMap B V f u hsq ≫ pullback.snd B.map f =
      pullback.snd (restrictedDatum B V).map s ≫ u := by
  rw [chartMap, Category.assoc, pullback.condition, ← Category.assoc,
    baseChangeIso_hom_snd]

@[reassoc]
theorem chartMap_fst :
    chartMap B V f u hsq ≫ pullback.fst B.map f =
      pullback.fst (restrictedDatum B V).map s ≫ toOriginal B V := by
  simp only [chartMap, baseChangeIso, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    pullbackLeftPullbackSndIso_inv_fst, affinePullbackIso_hom_fst]

/-- The source chart is the actual pullback along u. -/
theorem chartMap_isPullback :
    IsPullback (chartMap B V f u hsq) (pullback.snd (restrictedDatum B V).map s)
      (pullback.snd B.map f) u :=
  IsPullback.of_iso_pullback ⟨chartMap_snd B V f u hsq⟩
    (baseChangeIso B V f u hsq) rfl (baseChangeIso_hom_snd B V f u hsq)

instance chartMap_isOpenImmersion [IsOpenImmersion u] :
    IsOpenImmersion (chartMap B V f u hsq) := by
  dsimp only [chartMap]
  infer_instance

/-- The actual tautological-line isomorphism on the original affine source chart. -/
def pulledLineRestrictionIso :
    (Modules.pullback (chartMap B V f u hsq)).obj (pulledTautologicalLine B f).val ≅
      (pulledTautologicalLine (restrictedDatum B V) s).val :=
  (pullbackSquareIso (pullback.fst (restrictedDatum B V).map s) (chartMap B V f u hsq)
    (toOriginal B V) (pullback.fst B.map f) (chartMap_fst B V f u hsq).symm).app
      (tautologicalLine B).val ≪≫
    (Modules.pullback (pullback.fst (restrictedDatum B V).map s)).mapIso
      (tautologicalRestrictionIso B V)

/-- The exact source-line comparison from the original cartesian square. -/
def sourceRestrictionIso (D : W.Modules) :
    (Modules.pullback (chartMap B V f u hsq)).obj
        ((Modules.pullback (pullback.snd B.map f)).obj D) ≅
      (Modules.pullback (pullback.snd (restrictedDatum B V).map s)).obj
        ((Modules.pullback u).obj D) :=
  (pullbackSquareIso (pullback.snd (restrictedDatum B V).map s) (chartMap B V f u hsq)
    u (pullback.snd B.map f) (chartMap_snd B V f u hsq).symm).app D

/-- The original source-line frame pulled through the actual affine chart square. -/
def sourceFrame (D : W.Modules)
    (eD : (Modules.pullback u).obj D ≅ SheafOfModules.unit (Spec (.of S)).ringCatSheaf) :
    (Modules.pullback (chartMap B V f u hsq)).obj
        ((Modules.pullback (pullback.snd B.map f)).obj D) ≅
      SheafOfModules.unit (pullback (restrictedDatum B V).map s).ringCatSheaf :=
  sourceRestrictionIso B V f u hsq D ≪≫
    (Modules.pullback (pullback.snd (restrictedDatum B V).map s)).mapIso eD ≪≫
      pullbackUnitIso (pullback.snd (restrictedDatum B V).map s)

/-- The canonical full ideal-module comparison on the actual affine source chart. -/
def degreeOneRestrictionIso :
    (Modules.pullback u).obj (degreeOneModule (I := I) f) ≅
      degreeOneModule (I := affineCenter Γ(X, V.val) (I.ideal V)) s :=
  (pullbackSquareIso s u V.property.fromSpec f hsq).app (idealModule I.subschemeι) ≪≫
    (Modules.pullback s).mapIso
      (openIdealIso I V.property.fromSpec
        (affineCenter Γ(X, V.val) (I.ideal V)) (comap_fromSpec_eq_affineCenter I V))

variable (D : W.Modules) {ι : Type u}
  (π : (∐ fun _ : ι => D) ⟶ degreeOneModule (I := I) f)

/-- The specified original coproduct presentation pulled through the full ideal comparison. -/
def localPresentation :
    (∐ fun _ : ι => (Modules.pullback u).obj D) ⟶
      degreeOneModule (I := affineCenter Γ(X, V.val) (I.ideal V)) s :=
  sigmaComparison (Modules.pullback u) (fun _ : ι => D) ≫
    (Modules.pullback u).map π ≫ (degreeOneRestrictionIso V f u hsq).hom

instance localPresentation_epi [Epi π] : Epi (localPresentation V f u hsq D π) := by
  dsimp only [localPresentation]
  infer_instance

/-- Each local summand is the same original summand through the canonical comparison. -/
theorem localPresentation_row (i : ι) :
    Sigma.ι (fun _ : ι => (Modules.pullback u).obj D) i ≫
        localPresentation V f u hsq D π =
      (Modules.pullback u).map (Sigma.ι (fun _ : ι => D) i ≫ π) ≫
        (degreeOneRestrictionIso V f u hsq).hom := by
  simp [localPresentation, Functor.map_comp, Category.assoc]

/-- The local frame retains the actual original row in full tensor coordinates. -/
theorem localPresentation_framed_row
    (eD : (Modules.pullback u).obj D ≅ SheafOfModules.unit (Spec (.of S)).ringCatSheaf)
    (i : ι) :
    eD.inv ≫ Sigma.ι (fun _ : ι => (Modules.pullback u).obj D) i ≫
        localPresentation V f u hsq D π =
      eD.inv ≫ (Modules.pullback u).map (Sigma.ι (fun _ : ι => D) i ≫ π) ≫
        (degreeOneRestrictionIso V f u hsq).hom := by
  exact congrArg (fun k => eD.inv ≫ k) (localPresentation_row V f u hsq D π i)

/-- The indexed local generators span the full tensor ideal, including its torsion. -/
theorem localPresentation_generators_span [Epi π]
    (eD : (Modules.pullback u).obj D ≅ SheafOfModules.unit (Spec (.of S)).ringCatSheaf) :
    Submodule.span S (Set.range (AffineRow.generators (I.ideal V) S
      ((Modules.pullback u).obj D) eD (localPresentation V f u hsq D π))) = ⊤ :=
  AffineRow.span_generators (I.ideal V) S ((Modules.pullback u).obj D) eD
    (localPresentation V f u hsq D π)

end BlowupRestriction

open AlgebraicGeometry.Scheme.Modules.BaseChange.Affine.Square

section Cube

variable {T P B Y S W V X : Scheme.{u}}
  (t : T ⟶ P) (l : T ⟶ B) (p : T ⟶ S)
  (a : P ⟶ Y) (q : P ⟶ W) (g : B ⟶ Y) (r : B ⟶ V)
  (u : S ⟶ W) (s : S ⟶ V) (b : Y ⟶ X) (f : W ⟶ X) (v : V ⟶ X)
  (htq : t ≫ q = p ≫ u) (hsv : s ≫ v = u ≫ f)
  (hlr : l ≫ r = p ≫ s) (hgb : g ≫ b = r ≫ v)
  (hab : a ≫ b = q ≫ f) (hta : t ≫ a = l ≫ g)

private def cubeLeft :
    Modules.pullback f ⋙ Modules.pullback q ⋙ Modules.pullback t ⟶
      Modules.pullback b ⋙ Modules.pullback g ⋙ Modules.pullback l :=
  Functor.whiskerLeft (Modules.pullback f) (pullbackSquareIso p t u q htq.symm).hom ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (pullbackSquareIso s u v f hsv).hom (Modules.pullback p) ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft (Modules.pullback v) (pullbackSquareIso l p r s hlr).hom ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (pullbackSquareIso g r b v hgb).hom (Modules.pullback l) ≫
    (Functor.associator _ _ _).hom

private def cubeRight :
    Modules.pullback f ⋙ Modules.pullback q ⋙ Modules.pullback t ⟶
      Modules.pullback b ⋙ Modules.pullback g ⋙ Modules.pullback l :=
  (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (pullbackSquareIso a q b f hab).hom (Modules.pullback t) ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft (Modules.pullback b) (pullbackSquareIso l t g a hta.symm).hom

private theorem cube_comm :
    cubeLeft t l p q g r u s b f v htq hsv hlr hgb =
      cubeRight t l a q g b f hab hta := by
  let AF := (pullbackPushforwardAdjunction f).comp
    ((pullbackPushforwardAdjunction q).comp (pullbackPushforwardAdjunction t))
  let AG := (pullbackPushforwardAdjunction b).comp
    ((pullbackPushforwardAdjunction g).comp (pullbackPushforwardAdjunction l))
  apply (conjugateEquiv AG AF).injective
  unfold cubeLeft cubeRight
  dsimp only [AF, AG]
  rw [← conjugateEquiv_comp _
    ((pullbackPushforwardAdjunction f).comp
      ((pullbackPushforwardAdjunction u).comp (pullbackPushforwardAdjunction p))) _]
  rw [← conjugateEquiv_comp _
    (((pullbackPushforwardAdjunction f).comp
      (pullbackPushforwardAdjunction u)).comp (pullbackPushforwardAdjunction p)) _]
  rw [← conjugateEquiv_comp _
    (((pullbackPushforwardAdjunction v).comp
      (pullbackPushforwardAdjunction s)).comp (pullbackPushforwardAdjunction p)) _]
  rw [← conjugateEquiv_comp _
    ((pullbackPushforwardAdjunction v).comp
      ((pullbackPushforwardAdjunction s).comp (pullbackPushforwardAdjunction p))) _]
  rw [← conjugateEquiv_comp _
    ((pullbackPushforwardAdjunction v).comp
      ((pullbackPushforwardAdjunction r).comp (pullbackPushforwardAdjunction l))) _]
  rw [← conjugateEquiv_comp _
    (((pullbackPushforwardAdjunction v).comp
      (pullbackPushforwardAdjunction r)).comp (pullbackPushforwardAdjunction l)) _]
  rw [← conjugateEquiv_comp _
    (((pullbackPushforwardAdjunction b).comp
      (pullbackPushforwardAdjunction g)).comp (pullbackPushforwardAdjunction l)) _]
  rw [conjugateEquiv_whiskerLeft, conjugateEquiv_whiskerRight,
    conjugateEquiv_associator_hom, conjugateEquiv_associator_inv,
    conjugateEquiv_pullbackSquareIso]
  simp only [conjugateEquiv_whiskerLeft, conjugateEquiv_whiskerRight,
    conjugateEquiv_associator_hom, conjugateEquiv_associator_inv,
    conjugateEquiv_pullbackSquareIso]
  rw [← conjugateEquiv_comp _
    (((pullbackPushforwardAdjunction f).comp
      (pullbackPushforwardAdjunction q)).comp (pullbackPushforwardAdjunction t)) _]
  rw [← conjugateEquiv_comp _
    (((pullbackPushforwardAdjunction b).comp
      (pullbackPushforwardAdjunction a)).comp (pullbackPushforwardAdjunction t)) _]
  rw [← conjugateEquiv_comp _
    ((pullbackPushforwardAdjunction b).comp
      ((pullbackPushforwardAdjunction a).comp (pullbackPushforwardAdjunction t))) _]
  simp only [conjugateEquiv_whiskerLeft, conjugateEquiv_whiskerRight,
    conjugateEquiv_associator_hom, conjugateEquiv_associator_inv,
    conjugateEquiv_pullbackSquareIso]
  apply NatTrans.ext
  funext M
  apply Modules.hom_ext
  intro U
  unfold pushforwardSquareIso
  simp only [Functor.whiskerRight_app, Functor.whiskerLeft_app, NatTrans.comp_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Iso.trans_hom, Iso.symm_hom,
    Modules.Hom.comp_app, Modules.pushforward_map_app,
    Modules.pushforwardComp_hom_app_app, Modules.pushforwardComp_inv_app_app,
    Modules.pushforwardCongr_hom_app_app, Category.id_comp, Category.comp_id,
    Modules.pushforward_obj_presheaf_map]
  repeat' erw [Category.id_comp]
  simp only [← Functor.map_comp]
  congr 1

private theorem cube_app (M : X.Modules) :
    (pullbackSquareIso p t u q htq.symm).hom.app ((Modules.pullback f).obj M) ≫
      (Modules.pullback p).map ((pullbackSquareIso s u v f hsv).hom.app M) ≫
        (pullbackSquareIso l p r s hlr).hom.app ((Modules.pullback v).obj M) ≫
          (Modules.pullback l).map ((pullbackSquareIso g r b v hgb).hom.app M) =
      (Modules.pullback t).map ((pullbackSquareIso a q b f hab).hom.app M) ≫
        (pullbackSquareIso l t g a hta.symm).hom.app ((Modules.pullback b).obj M) := by
  have H := congrArg (fun α => α.app M)
    (cube_comm t l p a q g r u s b f v htq hsv hlr hgb hab hta)
  simpa only [cubeLeft, cubeRight, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.comp_id, Category.assoc] using H

private theorem quotient_cube
    (M : X.Modules) (M' : V.Modules) (L : Y.Modules) (L' : B.Modules)
    (eI : (Modules.pullback v).obj M ≅ M') (eL : (Modules.pullback g).obj L ≅ L')
    (Q : (Modules.pullback b).obj M ⟶ L) (Q' : (Modules.pullback r).obj M' ⟶ L')
    (hQ : (Modules.pullback r).map eI.hom ≫ Q' =
      (pullbackSquareIso g r b v hgb).hom.app M ≫ (Modules.pullback g).map Q ≫ eL.hom) :
    (pullbackSquareIso p t u q htq.symm).hom.app ((Modules.pullback f).obj M) ≫
      (Modules.pullback p).map
        ((pullbackSquareIso s u v f hsv).hom.app M ≫ (Modules.pullback s).map eI.hom) ≫
        (pullbackSquareIso l p r s hlr).hom.app M' ≫ (Modules.pullback l).map Q' =
      (Modules.pullback t).map
        ((pullbackSquareIso a q b f hab).hom.app M ≫ (Modules.pullback a).map Q) ≫
          (pullbackSquareIso l t g a hta.symm).hom.app L ≫
            (Modules.pullback l).map eL.hom := by
  have hn := (pullbackSquareIso l p r s hlr).hom.naturality eI.hom
  have ht := (pullbackSquareIso l t g a hta.symm).hom.naturality Q
  simp only [Functor.comp_map] at hn ht
  have hQl := congrArg (fun z => (Modules.pullback l).map z) hQ
  simp only [Functor.map_comp] at hQl
  have hc := cube_app t l p a q g r u s b f v htq hsv hlr hgb hab hta M
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% hn, hQl, reassoc_of% hc, ← reassoc_of% ht]

/-- The cube comparison with the actual supplied constructors kept as arguments. -/
private theorem quotient_cube_actual
    (M : X.Modules) (M' : V.Modules) (L : Y.Modules) (L' : B.Modules)
    (eI : (Modules.pullback v).obj M ≅ M') (eL : (Modules.pullback g).obj L ≅ L')
    (Q : (Modules.pullback b).obj M ⟶ L) (Q' : (Modules.pullback r).obj M' ⟶ L')
    (hQ : (Modules.pullback r).map eI.hom ≫ Q' =
      (pullbackSquareIso g r b v hgb).hom.app M ≫ (Modules.pullback g).map Q ≫ eL.hom)
    (eSource : (Modules.pullback t).obj ((Modules.pullback q).obj
        ((Modules.pullback f).obj M)) ≅
      (Modules.pullback p).obj ((Modules.pullback u).obj ((Modules.pullback f).obj M)))
    (eDegree : (Modules.pullback u).obj ((Modules.pullback f).obj M) ≅
      (Modules.pullback s).obj M')
    (qGlobal : (Modules.pullback q).obj ((Modules.pullback f).obj M) ⟶
      (Modules.pullback a).obj L)
    (eLine : (Modules.pullback t).obj ((Modules.pullback a).obj L) ≅
      (Modules.pullback l).obj L')
    (qLocal : (Modules.pullback p).obj ((Modules.pullback s).obj M') ⟶
      (Modules.pullback l).obj L')
    (hSource : eSource.hom =
      (pullbackSquareIso p t u q htq.symm).hom.app ((Modules.pullback f).obj M))
    (hDegree : eDegree.hom =
      (pullbackSquareIso s u v f hsv).hom.app M ≫ (Modules.pullback s).map eI.hom)
    (hGlobal : qGlobal =
      (pullbackSquareIso a q b f hab).hom.app M ≫ (Modules.pullback a).map Q)
    (hLine : eLine.hom =
      (pullbackSquareIso l t g a hta.symm).hom.app L ≫ (Modules.pullback l).map eL.hom)
    (hLocal : qLocal =
      (pullbackSquareIso l p r s hlr).hom.app M' ≫ (Modules.pullback l).map Q') :
    QuotientRestrictionEq u q p t ((Modules.pullback f).obj M)
      ((Modules.pullback s).obj M') ((Modules.pullback a).obj L)
      ((Modules.pullback l).obj L') eSource eDegree qGlobal eLine qLocal := by
  unfold QuotientRestrictionEq
  rw [hSource, hDegree, hGlobal, hLine, hLocal]
  exact quotient_cube t l p a q g r u s b f v htq hsv hlr hgb hab hta M M' L L' eI eL Q Q' hQ

end Cube

private theorem framed_naturality_paste {C : Type*} [Category C]
    {U V D D' M M' N K : C} (z : U ⟶ V) (w : V ⟶ D')
    (eD : D ≅ D') (h : D ⟶ M) (eM : M ≅ M') (k : D' ⟶ M')
    (v : M' ⟶ N) (q : N ⟶ K) (hn : h ≫ eM.hom = eD.hom ≫ k) :
    z ≫ w ≫ eD.inv ≫ h ≫ eM.hom ≫ v ≫ q = z ≫ w ≫ k ≫ v ≫ q := by
  rw [reassoc_of% hn, Iso.inv_hom_id_assoc]

private theorem originalRow_transport {W S P T : Scheme.{u}}
    (u : S ⟶ W) (q : P ⟶ W) (p : T ⟶ S) (t : T ⟶ P)
    (E : Modules.pullback q ⋙ Modules.pullback t ≅
      Modules.pullback u ⋙ Modules.pullback p)
    (M D : W.Modules) (N : S.Modules) (L : P.Modules) (K : T.Modules)
    (eDegree : (Modules.pullback u).obj M ≅ N)
    (Q : (Modules.pullback q).obj M ⟶ L)
    (eLine : (Modules.pullback t).obj L ≅ K)
    (Q' : (Modules.pullback p).obj N ⟶ K)
    (hQ : QuotientRestrictionEq u q p t M N L K (E.app M) eDegree Q eLine Q')
    (eD : (Modules.pullback u).obj D ≅ SheafOfModules.unit S.ringCatSheaf)
    (eFrame : (Modules.pullback t).obj ((Modules.pullback q).obj D) ≅
      SheafOfModules.unit T.ringCatSheaf)
    (hFrame : eFrame.inv = (pullbackUnitIso p).inv ≫
      (Modules.pullback p).map eD.inv ≫ (E.app D).inv)
    (d : D ⟶ M) (dGlobal : (Modules.pullback q).obj D ⟶ L)
    (hGlobal : dGlobal = (Modules.pullback q).map d ≫ Q)
    (dLocal : SheafOfModules.unit S.ringCatSheaf ⟶ N)
    (hLocal : dLocal = eD.inv ≫ (Modules.pullback u).map d ≫ eDegree.hom) :
    RowRestrictionEq t p ((Modules.pullback q).obj D) L N K eFrame dGlobal eLine dLocal Q' := by
  have hn : (Modules.pullback t).map ((Modules.pullback q).map d) ≫ (E.app M).hom =
      (E.app D).hom ≫ (Modules.pullback p).map ((Modules.pullback u).map d) :=
    E.hom.naturality d
  unfold QuotientRestrictionEq at hQ
  unfold RowRestrictionEq
  rw [hFrame, hGlobal, hLocal]
  simp only [pullbackSection, Functor.map_comp, Category.assoc]
  rw [← hQ]
  exact framed_naturality_paste (pullbackUnitIso p).inv ((Modules.pullback p).map eD.inv)
    (E.app D) ((Modules.pullback t).map ((Modules.pullback q).map d)) (E.app M)
    ((Modules.pullback p).map ((Modules.pullback u).map d))
    ((Modules.pullback p).map eDegree.hom) Q' hn

section ActualRestriction

open AlgebraicGeometry.Scheme.Hom
open AlgebraicGeometry.ProjectiveSpace.FromSections

variable {X : Scheme.{u}} {I : X.IdealSheafData} (B : BlowupDatum I)
  (V : X.affineOpens) {W : Scheme.{u}} (f : W ⟶ X)
  {S : Type u} [CommRing S] [Algebra Γ(X, V.val) S]
  (u : Spec (.of S) ⟶ W)
  (hsq : Spec.map (CommRingCat.ofHom (algebraMap Γ(X, V.val) S)) ≫
    V.property.fromSpec = u ≫ f)

/-- The original projection of the affine restricted blowup, with its spectrum fixed. -/
abbrev affineBlowupMap :
    (restrictedDatum B V).Y ⟶ Spec Γ(X, V.val) := (restrictedDatum B V).map

local notation "s" => affineScalarMap V S
local notation "BR" => restrictedDatum B V
local notation "t" => chartMap B V f u hsq
local notation "p" =>
  Limits.pullback.snd (BlowupDatum.map (restrictedDatum B V)) (affineScalarMap V S)
local notation "l" =>
  Limits.pullback.fst (BlowupDatum.map (restrictedDatum B V)) (affineScalarMap V S)
local notation "a" => Limits.pullback.fst B.map f
local notation "q" => Limits.pullback.snd B.map f

/-- The original degree-one quotient is preserved after the arbitrary affine scalar change. -/
theorem pulledQuotient_restriction :
    QuotientRestrictionEq u q p t (degreeOneModule (I := I) f)
      (degreeOneModule (I := affineCenter Γ(X, V.val) (I.ideal V)) s)
      (pulledTautologicalLine B f).val (pulledTautologicalLine BR s).val
      (sourceRestrictionIso B V f u hsq (degreeOneModule (I := I) f))
      (degreeOneRestrictionIso V f u hsq) (pulledTautologicalQuotient B f)
      (pulledLineRestrictionIso B V f u hsq) (pulledTautologicalQuotient BR s) :=
  quotient_cube_actual t l p a q (toOriginal B V) (BlowupDatum.map (restrictedDatum B V)) u s
    B.map f V.property.fromSpec
    (chartMap_snd B V f u hsq) hsq Limits.pullback.condition (toOriginal_map B V)
    Limits.pullback.condition (chartMap_fst B V f u hsq)
    (idealModule I.subschemeι) (idealModule (affineCenter Γ(X, V.val) (I.ideal V)).subschemeι)
    (tautologicalLine B).val (tautologicalLine BR).val
    (openIdealIso I V.property.fromSpec (affineCenter Γ(X, V.val) (I.ideal V))
      (comap_fromSpec_eq_affineCenter I V))
    (tautologicalRestrictionIso B V) (tautologicalQuotient B) (tautologicalQuotient BR)
    (tautologicalRestrictionQuotient B V)
    (sourceRestrictionIso B V f u hsq (degreeOneModule (I := I) f))
    (degreeOneRestrictionIso V f u hsq) (pulledTautologicalQuotient B f)
    (pulledLineRestrictionIso B V f u hsq) (pulledTautologicalQuotient BR s)
    rfl rfl (pulledQuotient_constructor B f) rfl (pulledQuotient_constructor BR s)

variable (D : W.Modules) {ι : Type u}
  (π : (∐ fun _ : ι => D) ⟶ degreeOneModule (I := I) f)

/-- The original coproduct quotient on the unchanged global fibre product. -/
def originalQuotient :
    (∐ fun _ : ι => (Modules.pullback q).obj D) ⟶ (pulledTautologicalLine B f).val :=
  sigmaComparison (Modules.pullback q) (fun _ : ι => D) ≫
    (Modules.pullback q).map π ≫ pulledTautologicalQuotient B f

/-- The actual original summand before restriction. -/
def originalRow (i : ι) :
    (Modules.pullback q).obj D ⟶ (pulledTautologicalLine B f).val :=
  Sigma.ι (fun _ : ι => (Modules.pullback q).obj D) i ≫ originalQuotient B f D π

theorem originalRow_eq (i : ι) :
    originalRow B f D π i =
      (Modules.pullback q).map (Sigma.ι (fun _ : ι => D) i ≫ π) ≫
        pulledTautologicalQuotient B f := by
  simp [originalRow, originalQuotient, Functor.map_comp, Category.assoc]

/-- The supplied source frame and actual line comparison preserve each original indexed row. -/
theorem originalRow_restriction
    (eD : (Modules.pullback u).obj D ≅ SheafOfModules.unit (Spec (.of S)).ringCatSheaf)
    (i : ι) :
    RowRestrictionEq t p ((Modules.pullback q).obj D) (pulledTautologicalLine B f).val
      (degreeOneModule (I := affineCenter Γ(X, V.val) (I.ideal V)) s)
      (pulledTautologicalLine BR s).val (sourceFrame B V f u hsq D eD)
      (originalRow B f D π i) (pulledLineRestrictionIso B V f u hsq)
      (eD.inv ≫ Sigma.ι (fun _ : ι => (Modules.pullback u).obj D) i ≫
        localPresentation V f u hsq D π) (pulledTautologicalQuotient BR s) :=
  originalRow_transport u q p t
    (pullbackSquareIso p t u q (chartMap_snd B V f u hsq).symm)
    (degreeOneModule (I := I) f) D
    (degreeOneModule (I := affineCenter Γ(X, V.val) (I.ideal V)) s)
    (pulledTautologicalLine B f).val (pulledTautologicalLine BR s).val
    (degreeOneRestrictionIso V f u hsq) (pulledTautologicalQuotient B f)
    (pulledLineRestrictionIso B V f u hsq) (pulledTautologicalQuotient BR s)
    (pulledQuotient_restriction B V f u hsq) eD (sourceFrame B V f u hsq D eD)
    rfl (Sigma.ι (fun _ : ι => D) i ≫ π) (originalRow B f D π i)
    (originalRow_eq B f D π i)
    (eD.inv ≫ Sigma.ι (fun _ : ι => (Modules.pullback u).obj D) i ≫
      localPresentation V f u hsq D π)
    (localPresentation_framed_row V f u hsq D π eD i)

end ActualRestriction

end AlgebraicGeometry.Scheme.Blowup.ProjectivePresentation.Restriction
