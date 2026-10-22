/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Blowup.RegularPoint.Normal
public import Aglib.AlgebraicGeometry.Blowup.RegularPoint.Scheme
public import Aglib.AlgebraicGeometry.IdealSheaf.BaseChange.FlatMorphism

/-!
# Actual exceptional lines at closed points of schemes

The literal residue fibre of the original point blowup is compared with the
blowup of the original stalk. Canonical flat ideal base change preserves the
actual kernel and its inclusion. The local positive twist and the original
dual evaluation then identify the actual global exceptional normal with O(-1).
Only the closed point and its two-dimensional regular local ring are used.
-/

@[expose] public section
noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing
open Scheme.Hom Scheme.Modules Scheme.Modules.Invertible

universe u

namespace AlgebraicGeometry.Scheme.Blowup.RegularPoint

section CanonicalHelpers

variable {D X Y : Scheme.{u}} (q : D ⟶ X) [IsClosedImmersion q] (p : Y ⟶ X)

/-- An actual closed immersion is canonically isomorphic to its kernel subscheme. -/
def closedImmersionImageIso : D ≅ q.ker.subscheme := asIso q.toImage

/-- The original closed-immersion map is retained by the image comparison. -/
@[reassoc]
theorem closedImmersionImageIso_hom_ι :
    (closedImmersionImageIso q).hom ≫ q.ker.subschemeι = q := q.toImage_imageι

/-- The literal closed fibre remains Cartesian over the original kernel subscheme. -/
theorem closedFibreCentreSquare :
    IsPullback (pullback.fst p q)
      (pullback.snd p q ≫ (closedImmersionImageIso q).hom) p q.ker.subschemeι := by
  apply (IsPullback.of_hasPullback p q).of_iso
    (Iso.refl _) (Iso.refl _) (closedImmersionImageIso q) (Iso.refl _)
  · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
  · simp only [Iso.refl_hom, Category.id_comp]
  · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
  · simp only [Iso.refl_hom, Category.comp_id, closedImmersionImageIso_hom_ι]

/-- The actual inverse-image centre is canonically the literal closed fibre. -/
def closedFibreCentreIso : (q.ker.comap p).subscheme ≅ pullback p q :=
  q.ker.comapIso p ≪≫ (closedFibreCentreSquare q p).isoPullback.symm

/-- The centre-to-fibre isomorphism preserves the original immersion into the ambient scheme. -/
@[reassoc]
theorem closedFibreCentreIso_hom_ι :
    (closedFibreCentreIso q p).hom ≫ pullback.fst p q =
      (q.ker.comap p).subschemeι := by
  have ht : (closedFibreCentreSquare q p).isoPullback.inv ≫ pullback.fst p q =
      pullback.fst p q.ker.subschemeι := by
    apply (cancel_epi (closedFibreCentreSquare q p).isoPullback.hom).mp
    rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
    exact (closedFibreCentreSquare q p).isoPullback_hom_fst.symm
  simp only [closedFibreCentreIso, Iso.trans_hom, Iso.symm_hom, Category.assoc]
  rw [ht, Scheme.IdealSheafData.comapIso_hom_fst]

end CanonicalHelpers

section ModuleHelpers

variable {D D' X : Scheme.{u}} (i : D ⟶ X) (i' : D' ⟶ X)
  (e : D' ≅ D) (h : e.hom ≫ i = i')

/-- The canonical ideal comparison for an original source isomorphism over the identity. -/
def identityBaseIdealIso : idealModule i ≅ idealModule i' := by
  have : IsIso (idealPullbackMap i i' (𝟙 X) e.hom
      (h.trans (Category.comp_id i').symm)) :=
    idealPullbackMap_isIso_of_iso_square _ _ _ _ _
  exact ((pullbackId X).app (idealModule i)).symm ≪≫
    asIso (idealPullbackMap i i' (𝟙 X) e.hom (h.trans (Category.comp_id i').symm))

@[reassoc]
private theorem identityBaseIdealIso_hom_inclusion :
    (identityBaseIdealIso i i' e h).hom ≫ idealInclusion i' = idealInclusion i := by
  simp only [identityBaseIdealIso, Iso.trans_hom, Iso.symm_hom, asIso_hom, Category.assoc]
  rw [idealPullbackMap_inclusion]
  change (pullbackId X).inv.app (idealModule i) ≫
      (Scheme.Modules.pullback (𝟙 X)).map (idealInclusion i) ≫
        (pullbackUnitIso (𝟙 X)).hom = idealInclusion i
  have hn := (pullbackId X).inv.naturality (idealInclusion i)
  simp only [CategoryTheory.Functor.id_map] at hn
  rw [← reassoc_of% hn, ← pullbackUnitIso_id X, Iso.inv_hom_id_app]
  exact Category.comp_id _

end ModuleHelpers

/-- The conormal comparison of a displayed actual ideal square, using its original
module comparison and the native pullback associators. -/
def conormalSquareIso {D D' X Y : Scheme.{u}}
    (i : D ⟶ X) (i' : D' ⟶ Y) (b : Y ⟶ X) (a : D' ⟶ D)
    (h : a ≫ i = i' ≫ b) (L : LineBundle X) (L' : LineBundle Y)
    (c : (Scheme.Modules.pullback b).obj L.val ≅ L'.val) :
    (Scheme.Modules.pullback a).obj (pullbackLineBundle i L).val ≅
      (pullbackLineBundle i' L').val :=
  (pullbackComp a i).app L.val ≪≫ (pullbackCongr h).app L.val ≪≫
    ((pullbackComp i' b).app L.val).symm ≪≫ (Scheme.Modules.pullback i').mapIso c

private theorem conormalSquareIso_hom {D D' X Y : Scheme.{u}}
    (i : D ⟶ X) (i' : D' ⟶ Y) (b : Y ⟶ X) (a : D' ⟶ D)
    (h : a ≫ i = i' ≫ b) (L : LineBundle X) (L' : LineBundle Y)
    (c : (Scheme.Modules.pullback b).obj L.val ≅ L'.val) :
    (conormalSquareIso i i' b a h L L' c).hom =
      (pullbackComp a i).hom.app L.val ≫ (pullbackCongr h).hom.app L.val ≫
        (pullbackComp i' b).inv.app L.val ≫ (Scheme.Modules.pullback i').map c.hom := by
  simp only [conormalSquareIso, Iso.trans_hom, Iso.symm_hom, Iso.app_hom,
    Iso.app_inv, CategoryTheory.Functor.mapIso_hom]

/-- An original comparison on an isomorphic scheme descends by the native unit and
composition maps. The supplied comparison is constructed explicitly in the consumer. -/
def moduleIsoFromPullbackIso {T E P : Scheme.{u}} (e : T ≅ E) (g : T ⟶ P)
    (M : E.Modules) (F : P.Modules)
    (c : (Scheme.Modules.pullback e.hom).obj M ≅ (Scheme.Modules.pullback g).obj F) :
    M ≅ (Scheme.Modules.pullback (e.inv ≫ g)).obj F :=
  ((pullbackId E).app M).symm ≪≫ (pullbackCongr e.inv_hom_id.symm).app M ≪≫
    ((pullbackComp e.inv e.hom).app M).symm ≪≫
    (Scheme.Modules.pullback e.inv).mapIso c ≪≫ (pullbackComp e.inv g).app F

private theorem moduleIsoFromPullbackIso_hom {T E P : Scheme.{u}} (e : T ≅ E) (g : T ⟶ P)
    (M : E.Modules) (F : P.Modules)
    (c : (Scheme.Modules.pullback e.hom).obj M ≅ (Scheme.Modules.pullback g).obj F) :
    (moduleIsoFromPullbackIso e g M F c).hom =
      (pullbackId E).inv.app M ≫ (pullbackCongr e.inv_hom_id.symm).hom.app M ≫
        (pullbackComp e.inv e.hom).inv.app M ≫ (Scheme.Modules.pullback e.inv).map c.hom ≫
          (pullbackComp e.inv g).hom.app F := by
  simp only [moduleIsoFromPullbackIso, Iso.trans_hom, Iso.symm_hom, Iso.app_hom,
    Iso.app_inv, CategoryTheory.Functor.mapIso_hom]

/-- The original blowup datum of the actual residue-field kernel. -/
abbrev pointBlowupDatum (X : Scheme.{u}) (x : X) :=
  blowupDatum (X.fromSpecResidueField x).ker

/-- The scheme of that same original point blowup. -/
abbrev pointBlowup (X : Scheme.{u}) (x : X) : Scheme.{u} := (pointBlowupDatum X x).Y

/-- The original point blowdown. -/
abbrev pointBlowdown (X : Scheme.{u}) (x : X) : pointBlowup X x ⟶ X :=
  (pointBlowupDatum X x).map

/-- The literal exceptional fibre over the original residue-field map. -/
abbrev pointExceptionalFibre (X : Scheme.{u}) (x : X) : Scheme.{u} :=
  pullback (pointBlowdown X x) (X.fromSpecResidueField x)

/-- Its original first projection, retained as the actual exceptional immersion. -/
abbrev pointExceptionalι (X : Scheme.{u}) (x : X) : pointExceptionalFibre X x ⟶ pointBlowup X x :=
  pullback.fst (pointBlowdown X x) (X.fromSpecResidueField x)

/-- Its original projection to the same residue field. -/
abbrev pointExceptionalStructureMap (X : Scheme.{u}) (x : X) :
    pointExceptionalFibre X x ⟶ Spec (X.residueField x) :=
  pullback.snd (pointBlowdown X x) (X.fromSpecResidueField x)

/-- The stalk residue quotient factors through the original residue-field point map. -/
theorem pointResidueFactor (X : Scheme.{u}) (x : X) :
    quotientImmersion (maximalIdeal (X.presheaf.stalk x)) ≫ X.fromSpecStalk x =
      X.fromSpecResidueField x := rfl

instance stalkBlowupComparisonMono (X : Scheme.{u}) (x : X) (hx : IsClosed ({x} : Set X)) :
    Mono (stalkBlowupComparison X x hx) :=
  (stalkBlowupComparison_isPullback X x hx).mono_fst_of_mono

instance stalkBlowupComparisonFlat (X : Scheme.{u}) (x : X) (hx : IsClosed ({x} : Set X)) :
    Flat (stalkBlowupComparison X x hx) := by
  have : Flat (X.fromSpecStalk x) := Scheme.fromSpecStalk_flat X x
  rw [← stalkBlowupIso_hom_fst X x hx]
  infer_instance

/-- The actual local fibre is itself Cartesian over the original global blowdown. -/
theorem stalkExceptionalSquare (X : Scheme.{u}) (x : X) (hx : IsClosed ({x} : Set X)) :
    IsPullback
      (exceptionalι (maximalIdeal (X.presheaf.stalk x)) ≫ stalkBlowupComparison X x hx)
      (exceptionalStructureMap (maximalIdeal (X.presheaf.stalk x)))
      (pointBlowdown X x) (X.fromSpecResidueField x) := by
  simpa only [pointResidueFactor X x] using
    (IsPullback.of_hasPullback (blowdown (maximalIdeal (X.presheaf.stalk x)))
      (quotientImmersion (maximalIdeal (X.presheaf.stalk x)))).paste_horiz
        (stalkBlowupComparison_isPullback X x hx)

/-- The original local and global literal residue fibres are canonically isomorphic. -/
def stalkExceptionalIso (X : Scheme.{u}) (x : X) (hx : IsClosed ({x} : Set X)) :
    exceptionalFibre (maximalIdeal (X.presheaf.stalk x)) ≅ pointExceptionalFibre X x :=
  (stalkExceptionalSquare X x hx).isoPullback

@[reassoc (attr := simp)]
theorem stalkExceptionalIso_hom_ι (X : Scheme.{u}) (x : X) (hx : IsClosed ({x} : Set X)) :
    (stalkExceptionalIso X x hx).hom ≫ pointExceptionalι X x =
      exceptionalι (maximalIdeal (X.presheaf.stalk x)) ≫ stalkBlowupComparison X x hx :=
  (stalkExceptionalSquare X x hx).isoPullback_hom_fst

@[reassoc (attr := simp)]
theorem stalkExceptionalIso_hom_over (X : Scheme.{u}) (x : X) (hx : IsClosed ({x} : Set X)) :
    (stalkExceptionalIso X x hx).hom ≫ pointExceptionalStructureMap X x =
      exceptionalStructureMap (maximalIdeal (X.presheaf.stalk x)) :=
  (stalkExceptionalSquare X x hx).isoPullback_hom_snd

/-- The same actual local inverse-image centre identifies with the literal global fibre. -/
def stalkCentreFibreIso (X : Scheme.{u}) (x : X) (hx : IsClosed ({x} : Set X)) :
    centreScheme (maximalIdeal (X.presheaf.stalk x)) ≅ pointExceptionalFibre X x :=
  centreFibreIso (maximalIdeal (X.presheaf.stalk x)) ≪≫ stalkExceptionalIso X x hx

@[reassoc (attr := simp)]
theorem stalkCentreFibreIso_hom_ι (X : Scheme.{u}) (x : X) (hx : IsClosed ({x} : Set X)) :
    (stalkCentreFibreIso X x hx).hom ≫ pointExceptionalι X x =
      ((affineCenter (X.presheaf.stalk x) (maximalIdeal (X.presheaf.stalk x))).comap
        (blowdown (maximalIdeal (X.presheaf.stalk x)))).subschemeι ≫
          stalkBlowupComparison X x hx := by
  simp only [stalkCentreFibreIso, Iso.trans_hom, Category.assoc,
    stalkExceptionalIso_hom_ι, centreFibreIso_hom_ι_assoc]

@[reassoc (attr := simp)]
theorem stalkCentreFibreIso_hom_over (X : Scheme.{u}) (x : X) (hx : IsClosed ({x} : Set X)) :
    (stalkCentreFibreIso X x hx).hom ≫ pointExceptionalStructureMap X x =
      centreStructureMap (maximalIdeal (X.presheaf.stalk x)) := by
  simp only [stalkCentreFibreIso, Iso.trans_hom, Category.assoc,
    stalkExceptionalIso_hom_over, centreStructureMap]

/-- The canonical exceptional comparison is Cartesian as a square of original immersions. -/
theorem stalkCentreFibre_isPullback (X : Scheme.{u}) (x : X) (hx : IsClosed ({x} : Set X)) :
    IsPullback (stalkCentreFibreIso X x hx).hom
      ((affineCenter (X.presheaf.stalk x) (maximalIdeal (X.presheaf.stalk x))).comap
        (blowdown (maximalIdeal (X.presheaf.stalk x)))).subschemeι
      (pointExceptionalι X x) (stalkBlowupComparison X x hx) :=
  IsPullback.of_horiz_isIso_mono ⟨stalkCentreFibreIso_hom_ι X x hx⟩

/-- The actual comparison preserves the original residue-field structure maps. -/
def stalkCentreFibreOverIso (X : Scheme.{u}) (x : X) (hx : IsClosed ({x} : Set X)) :
    Over.mk (centreStructureMap (maximalIdeal (X.presheaf.stalk x))) ≅
      Over.mk (pointExceptionalStructureMap X x) :=
  Over.isoMk (stalkCentreFibreIso X x hx) (stalkCentreFibreIso_hom_over X x hx)

/-- The literal exceptional projection is a closed immersion at an original closed point. -/
theorem pointExceptionalι_isClosedImmersion (X : Scheme.{u}) (x : X)
    (hx : IsClosed ({x} : Set X)) : IsClosedImmersion (pointExceptionalι X x) := by
  have : IsClosedImmersion (X.fromSpecResidueField x) :=
    isClosed_singleton_iff_isClosedImmersion.mp hx
  infer_instance

/-- The actual kernel of the literal fibre and the Cartier image ideal have their
canonical identity-base comparison, induced by the original source isomorphism. -/
def pointIdealCentreIso (X : Scheme.{u}) (x : X) (hx : IsClosed ({x} : Set X)) :
    idealModule (pointExceptionalι X x) ≅
      idealModule (((X.fromSpecResidueField x).ker.comap (pointBlowdown X x)).subschemeι) := by
  have : IsClosedImmersion (X.fromSpecResidueField x) :=
    isClosed_singleton_iff_isClosedImmersion.mp hx
  exact identityBaseIdealIso (pointExceptionalι X x) _
    (closedFibreCentreIso (X.fromSpecResidueField x) (pointBlowdown X x))
    (closedFibreCentreIso_hom_ι (X.fromSpecResidueField x) (pointBlowdown X x))

@[reassoc]
theorem pointIdealCentreIso_hom_inclusion (X : Scheme.{u}) (x : X)
    (hx : IsClosed ({x} : Set X)) :
    (pointIdealCentreIso X x hx).hom ≫
        idealInclusion (((X.fromSpecResidueField x).ker.comap (pointBlowdown X x)).subschemeι) =
      idealInclusion (pointExceptionalι X x) := by
  have : IsClosedImmersion (X.fromSpecResidueField x) :=
    isClosed_singleton_iff_isClosedImmersion.mp hx
  exact identityBaseIdealIso_hom_inclusion (pointExceptionalι X x)
    (((X.fromSpecResidueField x).ker.comap (pointBlowdown X x)).subschemeι)
    (closedFibreCentreIso (X.fromSpecResidueField x) (pointBlowdown X x))
    (closedFibreCentreIso_hom_ι (X.fromSpecResidueField x) (pointBlowdown X x))

/-- The original Cartier image ideal, presented on the literal exceptional immersion. -/
def pointIdealLine (X : Scheme.{u}) (x : X) (hx : IsClosed ({x} : Set X)) :
    LineBundle (pointBlowup X x) :=
  ⟨idealModule (pointExceptionalι X x),
    isLocallyRankOne_of_iso (pointBlowup X x)
      (pointIdealCentreIso X x hx).symm (pointBlowupDatum X x).cartier⟩

/-- The actual conormal is pullback of the original exceptional kernel ideal. -/
def pointConormalLine (X : Scheme.{u}) (x : X) (hx : IsClosed ({x} : Set X)) :
    LineBundle (pointExceptionalFibre X x) :=
  pullbackLineBundle (pointExceptionalι X x) (pointIdealLine X x hx)

/-- The actual normal is restriction of the dual of that same kernel ideal. -/
def pointNormalLine (X : Scheme.{u}) (x : X) (hx : IsClosed ({x} : Set X)) :
    LineBundle (pointExceptionalFibre X x) :=
  pullbackLineBundle (pointExceptionalι X x)
    (dualLineBundle (pointBlowup X x) (pointIdealLine X x hx))

/-- Flat stalk comparison inverts the ACTUAL canonical ideal module map. -/
def stalkPointIdealIso (X : Scheme.{u}) (x : X) (hx : IsClosed ({x} : Set X)) :
    (Scheme.Modules.pullback (stalkBlowupComparison X x hx)).obj (pointIdealLine X x hx).val ≅
      (centreIdealLine (maximalIdeal (X.presheaf.stalk x))).val := by
  have : IsClosedImmersion (pointExceptionalι X x) := pointExceptionalι_isClosedImmersion X x hx
  have : IsIso (idealPullbackMap (pointExceptionalι X x)
      ((affineCenter (X.presheaf.stalk x) (maximalIdeal (X.presheaf.stalk x))).comap
        (blowdown (maximalIdeal (X.presheaf.stalk x)))).subschemeι
      (stalkBlowupComparison X x hx) (stalkCentreFibreIso X x hx).hom
      (stalkCentreFibreIso_hom_ι X x hx)) :=
    idealPullbackMap_isIso_of_flat _ _ _ _ _ (stalkCentreFibre_isPullback X x hx)
  exact asIso (idealPullbackMap (pointExceptionalι X x)
    ((affineCenter (X.presheaf.stalk x) (maximalIdeal (X.presheaf.stalk x))).comap
      (blowdown (maximalIdeal (X.presheaf.stalk x)))).subschemeι
    (stalkBlowupComparison X x hx) (stalkCentreFibreIso X x hx).hom
    (stalkCentreFibreIso_hom_ι X x hx))

/-- The actual flat ideal comparison keeps the original inclusions and unit map. -/
@[reassoc]
theorem stalkPointIdealIso_hom_inclusion (X : Scheme.{u}) (x : X)
    (hx : IsClosed ({x} : Set X)) :
    (stalkPointIdealIso X x hx).hom ≫
        idealInclusion
          ((affineCenter (X.presheaf.stalk x) (maximalIdeal (X.presheaf.stalk x))).comap
            (blowdown (maximalIdeal (X.presheaf.stalk x)))).subschemeι =
      (Scheme.Modules.pullback (stalkBlowupComparison X x hx)).map
        (idealInclusion (pointExceptionalι X x)) ≫
          (pullbackUnitIso (stalkBlowupComparison X x hx)).hom :=
  idealPullbackMap_inclusion _ _ _ _ _

/-- Restricting the actual flat ideal comparison gives the actual conormal comparison. -/
def stalkPointConormalIso (X : Scheme.{u}) (x : X) (hx : IsClosed ({x} : Set X)) :
    (Scheme.Modules.pullback (stalkCentreFibreIso X x hx).hom).obj
        (pointConormalLine X x hx).val ≅
      (centreConormalLine (maximalIdeal (X.presheaf.stalk x))).val :=
  conormalSquareIso (pointExceptionalι X x)
    ((affineCenter (X.presheaf.stalk x) (maximalIdeal (X.presheaf.stalk x))).comap
      (blowdown (maximalIdeal (X.presheaf.stalk x)))).subschemeι
    (stalkBlowupComparison X x hx) (stalkCentreFibreIso X x hx).hom
    (stalkCentreFibreIso_hom_ι X x hx) (pointIdealLine X x hx)
    (centreIdealLine (maximalIdeal (X.presheaf.stalk x))) (stalkPointIdealIso X x hx)

/-- The conormal comparison retains every original pullback and ideal-map component. -/
theorem stalkPointConormalIso_hom (X : Scheme.{u}) (x : X) (hx : IsClosed ({x} : Set X)) :
    (stalkPointConormalIso X x hx).hom =
      (pullbackComp (stalkCentreFibreIso X x hx).hom (pointExceptionalι X x)).hom.app
          (pointIdealLine X x hx).val ≫
        (pullbackCongr (stalkCentreFibreIso_hom_ι X x hx)).hom.app (pointIdealLine X x hx).val ≫
          (pullbackComp
            ((affineCenter (X.presheaf.stalk x) (maximalIdeal (X.presheaf.stalk x))).comap
              (blowdown (maximalIdeal (X.presheaf.stalk x)))).subschemeι
            (stalkBlowupComparison X x hx)).inv.app (pointIdealLine X x hx).val ≫
            (Scheme.Modules.pullback
              ((affineCenter (X.presheaf.stalk x) (maximalIdeal (X.presheaf.stalk x))).comap
                (blowdown (maximalIdeal (X.presheaf.stalk x)))).subschemeι).map
              (stalkPointIdealIso X x hx).hom :=
  conormalSquareIso_hom (pointExceptionalι X x)
    ((affineCenter (X.presheaf.stalk x) (maximalIdeal (X.presheaf.stalk x))).comap
      (blowdown (maximalIdeal (X.presheaf.stalk x)))).subschemeι
    (stalkBlowupComparison X x hx) (stalkCentreFibreIso X x hx).hom
    (stalkCentreFibreIso_hom_ι X x hx) (pointIdealLine X x hx)
    (centreIdealLine (maximalIdeal (X.presheaf.stalk x))) (stalkPointIdealIso X x hx)

section RegularPoint

variable (X : Scheme.{u}) (x : X) (hx : IsClosed ({x} : Set X))
  [IsRegularLocalRing (X.presheaf.stalk x)] (hd : ringKrullDim (X.presheaf.stalk x) = 2)

/-- The literal global exceptional fibre is the native projective line over the SAME
original residue field. No global regularity or Noetherianity is assumed. -/
def pointExceptionalOverIsoProjectiveP1 :
    Over.mk (pointExceptionalStructureMap X x) ≅
      Over.mk (ProjectiveLine.structureMap (ResidueField (X.presheaf.stalk x))) :=
  (stalkCentreFibreOverIso X x hx).symm ≪≫
    centreOverIsoProjectiveP1 (X.presheaf.stalk x) hd

/-- The forward comparison preserves the literal original residue-field projection. -/
@[reassoc]
theorem pointExceptionalOverIsoProjectiveP1_hom_over :
    (pointExceptionalOverIsoProjectiveP1 X x hx hd).hom.left ≫
        ProjectiveLine.structureMap (ResidueField (X.presheaf.stalk x)) =
      pointExceptionalStructureMap X x :=
  (pointExceptionalOverIsoProjectiveP1 X x hx hd).hom.w

/-- The original local centre comparison is recovered after the canonical fibre isomorphism. -/
@[reassoc]
theorem stalkCentreFibreIso_hom_projectiveP1 :
    (stalkCentreFibreIso X x hx).hom ≫
        (pointExceptionalOverIsoProjectiveP1 X x hx hd).hom.left =
      (centreOverIsoProjectiveP1 (X.presheaf.stalk x) hd).hom.left := by
  simp only [pointExceptionalOverIsoProjectiveP1, Iso.trans_hom, Iso.symm_hom,
    Over.comp_left, stalkCentreFibreOverIso, Over.isoMk_inv_left, Iso.hom_inv_id_assoc]

/-- The same original exceptional comparison, in the native twisting-sheaf coordinates. -/
def pointNativeComparison : pointExceptionalFibre X x ⟶
    AlgebraicGeometry.ProjectiveSpace (ResidueField (X.presheaf.stalk x)) (ULift.{u} (Fin 2)) :=
  (stalkCentreFibreIso X x hx).inv ≫ nativeCentreComparison (X.presheaf.stalk x) hd

/-- The native comparison is exactly the actual Over-P1 map followed by its canonical
coordinate lift; no unrelated projective model is substituted. -/
theorem pointNativeComparison_projectiveP1 :
    pointNativeComparison X x hx hd =
      (pointExceptionalOverIsoProjectiveP1 X x hx hd).hom.left ≫
        (AlgebraicGeometry.ProjectiveSpace.finUliftIso
          (ResidueField (X.presheaf.stalk x)) 2).hom := by
  simp only [pointNativeComparison, nativeCentreComparison, centreOverIsoNativeProjectiveLine,
    pointExceptionalOverIsoProjectiveP1, Iso.trans_hom, Iso.symm_hom, Over.comp_left,
    Scheme.OverField.Curve.ProjectiveLine.projectiveLineOverIsoNative,
    AlgebraicGeometry.ProjectiveSpace.finUliftOverIso, stalkCentreFibreOverIso,
    Over.isoMk_inv_left, Over.isoMk_hom_left, Category.assoc]

@[reassoc]
theorem stalkCentreFibreIso_hom_native :
    (stalkCentreFibreIso X x hx).hom ≫ pointNativeComparison X x hx hd =
      nativeCentreComparison (X.presheaf.stalk x) hd := by
  simp only [pointNativeComparison, Iso.hom_inv_id_assoc]

/-- Transport of the checked local O(1) comparison through the actual fibre and ideal
isomorphisms identifies the actual global conormal module. -/
def pointConormalTwistingIso :
    (Scheme.Modules.pullback (pointNativeComparison X x hx hd)).obj
        (AlgebraicGeometry.ProjectiveSpace.twistingSheaf (ResidueField (X.presheaf.stalk x))
          (ULift.{u} (Fin 2)) 1) ≅
      (pointConormalLine X x hx).val :=
  (moduleIsoFromPullbackIso (stalkCentreFibreIso X x hx)
    (nativeCentreComparison (X.presheaf.stalk x) hd) (pointConormalLine X x hx).val
    (AlgebraicGeometry.ProjectiveSpace.twistingSheaf (ResidueField (X.presheaf.stalk x))
      (ULift.{u} (Fin 2)) 1)
    (stalkPointConormalIso X x hx ≪≫
      (centreConormalTwistingIso (X.presheaf.stalk x) hd).symm)).symm

/-- The global conormal comparison retains its original local ideal map and the native
unit, equality and composition isomorphisms used in descent. -/
theorem pointConormalTwistingIso_inv_formula :
    (pointConormalTwistingIso X x hx hd).inv =
      (pullbackId (pointExceptionalFibre X x)).inv.app (pointConormalLine X x hx).val ≫
        (pullbackCongr (stalkCentreFibreIso X x hx).inv_hom_id.symm).hom.app
          (pointConormalLine X x hx).val ≫
          (pullbackComp (stalkCentreFibreIso X x hx).inv
            (stalkCentreFibreIso X x hx).hom).inv.app (pointConormalLine X x hx).val ≫
            (Scheme.Modules.pullback (stalkCentreFibreIso X x hx).inv).map
              (stalkPointConormalIso X x hx ≪≫
                (centreConormalTwistingIso (X.presheaf.stalk x) hd).symm).hom ≫
              (pullbackComp (stalkCentreFibreIso X x hx).inv
                (nativeCentreComparison (X.presheaf.stalk x) hd)).hom.app
                  (AlgebraicGeometry.ProjectiveSpace.twistingSheaf
                    (ResidueField (X.presheaf.stalk x)) (ULift.{u} (Fin 2)) 1) :=
  moduleIsoFromPullbackIso_hom (stalkCentreFibreIso X x hx)
    (nativeCentreComparison (X.presheaf.stalk x) hd) (pointConormalLine X x hx).val
    (AlgebraicGeometry.ProjectiveSpace.twistingSheaf (ResidueField (X.presheaf.stalk x))
      (ULift.{u} (Fin 2)) 1)
    (stalkPointConormalIso X x hx ≪≫
      (centreConormalTwistingIso (X.presheaf.stalk x) hd).symm)

/-- The same actual conormal comparison directly over the literal polynomial projective
line and the original exceptional Over-isomorphism. -/
def pointConormalProjectiveP1Iso :
    (Scheme.Modules.pullback (pointExceptionalOverIsoProjectiveP1 X x hx hd).hom.left).obj
        ((Scheme.Modules.pullback
          (AlgebraicGeometry.ProjectiveSpace.finUliftIso
            (ResidueField (X.presheaf.stalk x)) 2).hom).obj
              (AlgebraicGeometry.ProjectiveSpace.twistingSheaf
                (ResidueField (X.presheaf.stalk x)) (ULift.{u} (Fin 2)) 1)) ≅
      (pointConormalLine X x hx).val :=
  (pullbackComp (pointExceptionalOverIsoProjectiveP1 X x hx hd).hom.left
    (AlgebraicGeometry.ProjectiveSpace.finUliftIso
      (ResidueField (X.presheaf.stalk x)) 2).hom).app
        (AlgebraicGeometry.ProjectiveSpace.twistingSheaf
          (ResidueField (X.presheaf.stalk x)) (ULift.{u} (Fin 2)) 1) ≪≫
    ((pullbackCongr (pointNativeComparison_projectiveP1 X x hx hd)).app
      (AlgebraicGeometry.ProjectiveSpace.twistingSheaf
        (ResidueField (X.presheaf.stalk x)) (ULift.{u} (Fin 2)) 1)).symm ≪≫
    pointConormalTwistingIso X x hx hd

end RegularPoint

/-- The actual global conormal and restricted dual have their original evaluation.
No flatness of the exceptional closed immersion is required. -/
def pointNormalEvaluationIso (X : Scheme.{u}) (x : X) (hx : IsClosed ({x} : Set X)) :
    tensorSheaf (pointExceptionalFibre X x) (pointConormalLine X x hx).val
      (pointNormalLine X x hx).val ≅
        SheafOfModules.unit (pointExceptionalFibre X x).ringCatSheaf :=
  (PullbackTensor.Local.pullbackLineBundleTensorIso (pointExceptionalι X x)
      (pointIdealLine X x hx) (dualLineBundle (pointBlowup X x) (pointIdealLine X x hx))).symm ≪≫
    (Scheme.Modules.pullback (pointExceptionalι X x)).mapIso
      (tensorSheafBraiding (pointBlowup X x) (pointIdealLine X x hx).val
        (dualLineBundle (pointBlowup X x) (pointIdealLine X x hx)).val ≪≫
        dualEvaluationIso (pointBlowup X x) (pointIdealLine X x hx)) ≪≫
    pullbackUnitIso (pointExceptionalι X x)

section RegularPoint

variable (X : Scheme.{u}) (x : X) (hx : IsClosed ({x} : Set X))
  [IsRegularLocalRing (X.presheaf.stalk x)] (hd : ringKrullDim (X.presheaf.stalk x) = 2)

/-- The actual conormal O(1) comparison and native twist multiplication evaluate the
negative twist against the original global kernel restriction. -/
def pointConormalNegativeTwistEvaluation :
    tensorSheaf (pointExceptionalFibre X x) (pointConormalLine X x hx).val
      (pullbackLineBundle (pointNativeComparison X x hx hd)
        (AlgebraicGeometry.ProjectiveSpace.twistingLineBundle (ResidueField (X.presheaf.stalk x))
          (ULift.{u} (Fin 2)) (-1))).val ≅
        SheafOfModules.unit (pointExceptionalFibre X x).ringCatSheaf :=
  tensorSheafIso _ (pointConormalTwistingIso X x hx hd).symm (Iso.refl _) ≪≫
    (PullbackTensor.Local.pullbackLineBundleTensorIso (pointNativeComparison X x hx hd)
      (AlgebraicGeometry.ProjectiveSpace.twistingLineBundle (ResidueField (X.presheaf.stalk x))
        (ULift.{u} (Fin 2)) 1)
      (AlgebraicGeometry.ProjectiveSpace.twistingLineBundle (ResidueField (X.presheaf.stalk x))
        (ULift.{u} (Fin 2)) (-1))).symm ≪≫
    (Scheme.Modules.pullback (pointNativeComparison X x hx hd)).mapIso
      (AlgebraicGeometry.ProjectiveSpace.twistingTensorIso (ResidueField (X.presheaf.stalk x))
        (ULift.{u} (Fin 2)) 1 (-1) ≪≫
        eqToIso (congrArg
          (AlgebraicGeometry.ProjectiveSpace.twistingSheaf (ResidueField (X.presheaf.stalk x))
            (ULift.{u} (Fin 2))) (show (1 : ℤ) + -1 = 0 by decide)) ≪≫
        AlgebraicGeometry.ProjectiveSpace.twistingZeroIso (ResidueField (X.presheaf.stalk x))
          (ULift.{u} (Fin 2))) ≪≫
    pullbackUnitIso (pointNativeComparison X x hx hd)

/-- The ACTUAL normal of the literal global exceptional fibre is O(-1), through the
same original residue-field P1 comparison and canonical coordinates. -/
def pointNormalTwistingIso :
    (pointNormalLine X x hx).val ≅
      (Scheme.Modules.pullback (pointNativeComparison X x hx hd)).obj
        (AlgebraicGeometry.ProjectiveSpace.twistingSheaf (ResidueField (X.presheaf.stalk x))
          (ULift.{u} (Fin 2)) (-1)) :=
  rightDualComparison (pointExceptionalFibre X x)
    (pointConormalLine X x hx) (pointNormalLine X x hx)
    (pullbackLineBundle (pointNativeComparison X x hx hd)
      (AlgebraicGeometry.ProjectiveSpace.twistingLineBundle (ResidueField (X.presheaf.stalk x))
        (ULift.{u} (Fin 2)) (-1)))
    (pointNormalEvaluationIso X x hx) (pointConormalNegativeTwistEvaluation X x hx hd)

/-- The global negative-twist comparison preserves the original actual evaluation map. -/
theorem pointNormalTwistingIso_tensor_hom :
    (lineBundleDualTensorEquivalence (pointExceptionalFibre X x)
      (pointConormalLine X x hx)).inverse.map (pointNormalTwistingIso X x hx hd).hom =
      (pointNormalEvaluationIso X x hx).hom ≫
        (pointConormalNegativeTwistEvaluation X x hx hd).inv :=
  rightDualComparison_tensor_hom _ _ _ _ _ _

/-- The same actual normal is the negative line on the literal native projective P1
via the original exceptional Over-isomorphism. -/
def pointNormalProjectiveP1Iso :
    (pointNormalLine X x hx).val ≅
      (Scheme.Modules.pullback (pointExceptionalOverIsoProjectiveP1 X x hx hd).hom.left).obj
        ((Scheme.Modules.pullback
          (AlgebraicGeometry.ProjectiveSpace.finUliftIso
            (ResidueField (X.presheaf.stalk x)) 2).hom).obj
              (AlgebraicGeometry.ProjectiveSpace.twistingSheaf
                (ResidueField (X.presheaf.stalk x)) (ULift.{u} (Fin 2)) (-1))) :=
  pointNormalTwistingIso X x hx hd ≪≫
    (pullbackCongr (pointNativeComparison_projectiveP1 X x hx hd)).app
      (AlgebraicGeometry.ProjectiveSpace.twistingSheaf
        (ResidueField (X.presheaf.stalk x)) (ULift.{u} (Fin 2)) (-1)) ≪≫
    ((pullbackComp (pointExceptionalOverIsoProjectiveP1 X x hx hd).hom.left
      (AlgebraicGeometry.ProjectiveSpace.finUliftIso
        (ResidueField (X.presheaf.stalk x)) 2).hom).app
          (AlgebraicGeometry.ProjectiveSpace.twistingSheaf
            (ResidueField (X.presheaf.stalk x)) (ULift.{u} (Fin 2)) (-1))).symm

end RegularPoint

end AlgebraicGeometry.Scheme.Blowup.RegularPoint
