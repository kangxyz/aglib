/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Godement.DerivedPushforward.Total
public import Aglib.AlgebraicGeometry.Cohomology.Functoriality.PushforwardSection
public import Aglib.AlgebraicGeometry.Modules.Pushforward.ClosedImmersion

/-!
Source: `Quillen/AlgebraicGeometry/Scheme/Sheaf/GodementClosedSectionSpan.lean` at LOCAL Quillen
`189a8e779f0c68b2dfc6f8195daebb3e684a5905`. Selection: whole_general;
source ranges [[1, 200]]. Actual objects, maps and hypotheses are preserved.
-/

/-! # Original Godement weak span along a closed geometric section

The two arrows use the actual augmentation and the original geometric section
comparison. No direct image of a non-flasque augmentation is declared weak.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Modules.Godement

variable {X Y : Scheme.{u}} (s : X ⟶ Y) (p : Y ⟶ X)
  (h : s ≫ p = 𝟙 X) [IsClosedImmersion s]

/-- The literal complex direct images retain the original geometric section iso. -/
def sectionComplexPlusIso :
    (Scheme.Modules.pushforward s).mapCochainComplexPlus ⋙
      (Scheme.Modules.pushforward p).mapCochainComplexPlus ≅
        𝟭 (CochainComplex.Plus X.Modules) :=
  ((Scheme.Modules.pushforward s).mapCochainComplexPlusCompIso
    (Scheme.Modules.pushforward p)).symm ≪≫
  NatIso.mapCochainComplexPlus (sectionPushforwardIso s p h) ≪≫
  Functor.mapCochainComplexPlusIdIso X.Modules

/-- The original section image, totalized once before the ordinary projection. -/
def sectionTotalImage :
    CochainComplex.Plus X.Modules ⥤ CochainComplex.Plus X.Modules :=
  (Scheme.Modules.pushforward s).mapCochainComplexPlus ⋙
    godementTotalPlus Y ⋙ (Scheme.Modules.pushforward p).mapCochainComplexPlus

/-- The common vertex retains a source total as well as the product total. -/
def sectionRepeatedTotalImage :
    CochainComplex.Plus X.Modules ⥤ CochainComplex.Plus X.Modules :=
  godementTotalPlus X ⋙ sectionTotalImage s p

/-- The first arrow is the literal section image of the original source augmentation. -/
def sectionTotalToRepeated :
    sectionTotalImage s p ⟶ sectionRepeatedTotalImage s p where
  app K := (Scheme.Modules.pushforward p).mapCochainComplexPlus.map
    ((godementTotalPlus Y).map
      ((Scheme.Modules.pushforward s).mapCochainComplexPlus.map
        ((godementTotalPlusUnit X).app K)))
  naturality {K L} f := by
    have hn := (godementTotalPlusUnit X).naturality f
    dsimp only [Functor.id_map] at hn
    dsimp only [sectionTotalImage, sectionRepeatedTotalImage, Functor.comp_map]
    rw [← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp]
    rw [hn]
    simp only [Functor.map_comp]

/-- The second arrow is the inverse actual section iso, followed by the pushed
augmentation of the actual flasque section image of the source total. -/
def sectionSourceTotalToRepeated :
    godementTotalPlus X ⟶ sectionRepeatedTotalImage s p where
  app K := (sectionComplexPlusIso s p h).inv.app ((godementTotalPlus X).obj K) ≫
    (Scheme.Modules.pushforward p).mapCochainComplexPlus.map
      ((godementTotalPlusUnit Y).app
        ((Scheme.Modules.pushforward s).mapCochainComplexPlus.obj
          ((godementTotalPlus X).obj K)))
  naturality {K L} f := by
    have hn := (godementTotalPlusUnit Y).naturality
      ((Scheme.Modules.pushforward s).mapCochainComplexPlus.map
        ((godementTotalPlus X).map f))
    have hs := (sectionComplexPlusIso s p h).inv.naturality
      ((godementTotalPlus X).map f)
    dsimp only [Functor.id_map, Functor.comp_map] at hn hs
    dsimp only [sectionRepeatedTotalImage, sectionTotalImage, Functor.comp_map] at ⊢
    rw [← Category.assoc, hs, Category.assoc, ← Functor.map_comp]
    rw [hn, Functor.map_comp, Category.assoc]

/-- Ordinary pushforward preserves the actual totalized weak arrow on its
lower-bounded flasque totalizations. -/
private lemma pushforward_godementTotal_map_quasiIso
    {A B : CochainComplex Y.Modules ℤ} (q : A ⟶ B) [QuasiIso q]
    (a b : ℤ) [A.IsStrictlyGE a] [B.IsStrictlyGE b] :
    QuasiIso (((Scheme.Modules.pushforward p).mapHomologicalComplex (.up ℤ)).map
      ((godementTotal Y).map q)) := by
  let APlus : CochainComplex.Plus Y.Modules := ⟨A, ⟨a, inferInstance⟩⟩
  let BPlus : CochainComplex.Plus Y.Modules := ⟨B, ⟨b, inferInstance⟩⟩
  let qPlus : APlus ⟶ BPlus := ObjectProperty.homMk q
  let : QuasiIso qPlus.hom := by
    change QuasiIso q
    infer_instance
  let : QuasiIso ((godementTotal Y).map q) := godementTotalPlus_map_quasiIso qPlus
  let hA := fun n hn => CochainComplex.isZero_of_isStrictlyGE A a n hn
  let hB := fun n hn => CochainComplex.isZero_of_isStrictlyGE B b n hn
  let : ((godementTotal Y).obj A).IsStrictlyGE a := godementTotal_isStrictlyGE A a hA
  let : ((godementTotal Y).obj B).IsStrictlyGE b := godementTotal_isStrictlyGE B b hB
  exact quasiIso_pushforward_of_flasque p ((godementTotal Y).map q) a b
    (fun n hn => CochainComplex.isZero_of_isStrictlyGE ((godementTotal Y).obj A) a n hn)
    (fun n hn => CochainComplex.isZero_of_isStrictlyGE ((godementTotal Y).obj B) b n hn)
    (godementTotal_isFlasque A a hA) (godementTotal_isFlasque B b hB)

/-- The raw first arrow uses the actual source augmentation and exact closed pushforward. -/
private lemma closedSectionTotalUnit_quasiIso (K : CochainComplex.Plus X.Modules) :
    QuasiIso (((Scheme.Modules.pushforward p).mapHomologicalComplex (.up ℤ)).map
      ((godementTotal Y).map
        (((Scheme.Modules.pushforward s).mapHomologicalComplex (.up ℤ)).map
          ((godementTotalUnit X).app K.obj)))) := by
  obtain ⟨a, ha⟩ := K.property
  let := ha
  let hK := fun n hn => CochainComplex.isZero_of_isStrictlyGE K.obj a n hn
  let : ((godementTotal X).obj K.obj).IsStrictlyGE a :=
    godementTotal_isStrictlyGE K.obj a hK
  let hSa : CochainComplex.IsStrictlyGE
      (((Scheme.Modules.pushforward s).mapHomologicalComplex (.up ℤ)).obj K.obj) a :=
    inferInstance
  let hSb : CochainComplex.IsStrictlyGE
      (((Scheme.Modules.pushforward s).mapHomologicalComplex (.up ℤ)).obj
        ((godementTotal X).obj K.obj)) a := inferInstance
  let : (Scheme.Modules.pushforward s).PreservesHomology :=
    Functor.preservesHomology_of_preservesEpis_and_kernels (Scheme.Modules.pushforward s)
  let : QuasiIso ((godementTotalUnit X).app K.obj) := godementTotalUnit_quasiIso X K
  let hq : QuasiIso (((Scheme.Modules.pushforward s).mapHomologicalComplex (.up ℤ)).map
      ((godementTotalUnit X).app K.obj)) :=
    HomologicalComplex.quasiIso_map_of_preservesHomology
      ((godementTotalUnit X).app K.obj) (Scheme.Modules.pushforward s)
  exact @pushforward_godementTotal_map_quasiIso X Y p
    (((Scheme.Modules.pushforward s).mapHomologicalComplex (.up ℤ)).obj K.obj)
    (((Scheme.Modules.pushforward s).mapHomologicalComplex (.up ℤ)).obj
      ((godementTotal X).obj K.obj))
    (((Scheme.Modules.pushforward s).mapHomologicalComplex (.up ℤ)).map
      ((godementTotalUnit X).app K.obj)) hq a a hSa hSb

/-- The first actual natural arrow is a genuine quasi-isomorphism. -/
lemma sectionTotalToRepeated_quasiIso (K : CochainComplex.Plus X.Modules) :
    QuasiIso ((sectionTotalToRepeated s p).app K).hom := by
  dsimp only [sectionTotalToRepeated, sectionTotalImage, sectionRepeatedTotalImage,
    godementTotalPlusUnit, godementTotalPlus,
    Functor.mapCochainComplexPlus, ObjectProperty.lift, CochainComplex.Plus.ι,
    ObjectProperty.ι, inducedFunctor, Functor.comp_map, Functor.comp_obj,
    Functor.id_obj, ObjectProperty.homMk]
  exact closedSectionTotalUnit_quasiIso s p K

/-- The ordinary image of a flasque lower-bounded complex's actual augmentation is weak. -/
lemma pushforwardPlusUnit_quasiIso_of_flasque (J : CochainComplex.Plus Y.Modules)
    (hfJ : ∀ n, TopCat.Presheaf.IsFlasque (J.obj.X n).presheaf) :
    QuasiIso ((Scheme.Modules.pushforward p).mapCochainComplexPlus.map
      ((godementTotalPlusUnit Y).app J)).hom := by
  obtain ⟨b, hb⟩ := J.property
  let := hb
  let hJ := fun n hn => CochainComplex.isZero_of_isStrictlyGE J.obj b n hn
  let : ((godementTotalPlus Y).obj J).obj.IsStrictlyGE b :=
    godementTotal_isStrictlyGE J.obj b hJ
  let : QuasiIso ((godementTotalPlusUnit Y).app J).hom :=
    godementTotalPlusUnit_quasiIso Y J
  exact quasiIso_pushforward_of_flasque p ((godementTotalPlusUnit Y).app J).hom b b hJ
    (fun n hn => CochainComplex.isZero_of_isStrictlyGE
      ((godementTotalPlus Y).obj J).obj b n hn)
    hfJ (godementTotal_isFlasque J.obj b hJ)

omit [IsClosedImmersion s] in
/-- The actual closed section image of the source total has flasque terms. -/
lemma sectionTotalPlus_isFlasque (K : CochainComplex.Plus X.Modules) (n : ℤ) :
    TopCat.Presheaf.IsFlasque
      (((Scheme.Modules.pushforward s).mapCochainComplexPlus.obj
        ((godementTotalPlus X).obj K)).obj.X n).presheaf := by
  obtain ⟨a, ha⟩ := K.property
  let := ha
  let hK := fun m hm => CochainComplex.isZero_of_isStrictlyGE K.obj a m hm
  let : TopCat.Presheaf.IsFlasque
      (((godementTotalPlus X).obj K).obj.X n).presheaf :=
    godementTotal_isFlasque K.obj a hK n
  exact pushforward_isFlasque s (((godementTotalPlus X).obj K).obj.X n)

omit [IsClosedImmersion s] in
/-- The second actual natural arrow is a genuine quasi-isomorphism because
its section image already has flasque terms before the product augmentation. -/
lemma sectionSourceTotalToRepeated_quasiIso (K : CochainComplex.Plus X.Modules) :
    QuasiIso ((sectionSourceTotalToRepeated s p h).app K).hom := by
  let J := (Scheme.Modules.pushforward s).mapCochainComplexPlus.obj
    ((godementTotalPlus X).obj K)
  let : QuasiIso
      ((Scheme.Modules.pushforward p).mapCochainComplexPlus.map
        ((godementTotalPlusUnit Y).app J)).hom :=
    pushforwardPlusUnit_quasiIso_of_flasque p J (sectionTotalPlus_isFlasque s K)
  change QuasiIso
    (((sectionComplexPlusIso s p h).inv.app ((godementTotalPlus X).obj K)).hom ≫
      ((Scheme.Modules.pushforward p).mapCochainComplexPlus.map
        ((godementTotalPlusUnit Y).app J)).hom)
  let : IsIso (((sectionComplexPlusIso s p h).inv.app ((godementTotalPlus X).obj K)).hom) :=
    inferInstanceAs (IsIso ((CochainComplex.Plus.ι X.Modules).map
      ((sectionComplexPlusIso s p h).inv.app ((godementTotalPlus X).obj K))))
  infer_instance

end AlgebraicGeometry.Scheme.Modules.Godement
