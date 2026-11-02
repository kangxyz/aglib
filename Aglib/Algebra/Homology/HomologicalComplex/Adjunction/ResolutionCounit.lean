/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.HomologicalComplex.Adjunction.CounitNaturality
public import Aglib.Algebra.Homology.ShortComplex.Adjunction.SectionsRestriction
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact

/-!
# Complete resolution and counit transport of original sections

The original resolution isomorphisms and counit factors identify the actual
higher-image section map with homology of the actual sections-complex map.
A commuting square of those complexes and the original cohomology
normalization then gives the cohomology square. The derived square is a
conclusion, not an input. All maps and homology objects are the original ones.
-/

@[expose] public section
noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace CategoryTheory.Adjunction

universe u₀ v₀ u₁ v₁ w₀ w₁ vM uι uH₀ uH₁

variable {R : Type w₀} {S : Type w₁} [CommRing R] [CommRing S]
  {D₀ : Type u₀} [Category.{v₀} D₀] [Abelian D₀]
  {D₁ : Type u₁} [Category.{v₁} D₁] [Abelian D₁]
  {F₀ : ModuleCat.{vM} R ⥤ D₀} {G₀ : D₀ ⥤ ModuleCat.{vM} R}
  {F₁ : ModuleCat.{vM} S ⥤ D₁} {G₁ : D₁ ⥤ ModuleCat.{vM} S}
  [F₀.Additive] [G₀.Additive] [F₁.Additive] [G₁.Additive]
  [F₀.PreservesHomology] [F₁.PreservesHomology]
  (adj₀ : F₀ ⊣ G₀) (adj₁ : F₁ ⊣ G₁)
  (A : D₀ ⥤ D₁) [A.Additive] [A.PreservesHomology]
  (σ : R →+* S) (η : G₀ ⟶ A ⋙ G₁ ⋙ ModuleCat.restrictScalars σ)
  {ι : Type uι} {c : ComplexShape ι}
  (K : HomologicalComplex D₀ c) (L : HomologicalComplex D₁ c)
  (ψ : (A.mapHomologicalComplex c).obj K ⟶ L) (n : ι)
  {U : D₀} {V : D₁}

/-- Original resolution factors and counit factors construct the whole section-to-homology
square. Invertibility of the target mate is deduced from its actual counit factor. -/
theorem resolutionCounit_homology
    (eI : U ≅ K.homology n) (eJ : V ≅ L.homology n)
    (aX : G₀.obj U ⟶ ((G₀.mapHomologicalComplex c).obj K).homology n)
    (aY : G₁.obj V ⟶ ((G₁.mapHomologicalComplex c).obj L).homology n) [IsIso aY]
    (haX : aX ≫ adj₀.homologyCounitMate (K.sc n) = G₀.map eI.hom)
    (haY : aY ≫ adj₁.homologyCounitMate (L.sc n) = G₁.map eJ.hom)
    (k : A.obj U ⟶ V)
    (hk : k = A.map eI.hom ≫
      (((K.sc n).mapHomologyIso A).inv ≫ homologyMap ψ n) ≫ eJ.inv) :
    η.app U ≫ (ModuleCat.restrictScalars σ).map (G₁.map k) ≫
        (ModuleCat.restrictScalars σ).map aY =
      aX ≫ homologyMap (counitSectionsComplexMap A (ModuleCat.restrictScalars σ) η K L ψ) n ≫
        ((((G₁.mapHomologicalComplex c).obj L).sc n).mapHomologyIso
          (ModuleCat.restrictScalars σ)).hom := by
  let T := ModuleCat.restrictScalars σ
  let mY := adj₁.homologyCounitMate (L.sc n)
  let : IsIso mY := IsIso.of_isIso_fac_left haY
  have hs := sectionsSquare_of_resolution_factorization A G₀ G₁ σ η eI eJ
    (((K.sc n).mapHomologyIso A).inv ≫ homologyMap ψ n) k hk
    aX (adj₀.homologyCounitMate (K.sc n)) haX
  have hn := homologyCounitMate_complex_naturality A T η K L ψ adj₀ adj₁ n
  apply (cancel_mono (T.map mY)).mp
  simp only [Category.assoc]
  rw [← T.map_comp, haY]
  exact hs.trans (congrArg (fun z => aX ≫ z) hn.symm)

/-- An actual square of coefficient complexes and its original Ext normalization transport
all the way to the original higher-image sections. No derived restriction square is assumed. -/
theorem resolutionCounit_cohomology_values
    (eI : U ≅ K.homology n) (eJ : V ≅ L.homology n)
    (aX : G₀.obj U ⟶ ((G₀.mapHomologicalComplex c).obj K).homology n)
    (aY : G₁.obj V ⟶ ((G₁.mapHomologicalComplex c).obj L).homology n) [IsIso aY]
    (haX : aX ≫ adj₀.homologyCounitMate (K.sc n) = G₀.map eI.hom)
    (haY : aY ≫ adj₁.homologyCounitMate (L.sc n) = G₁.map eJ.hom)
    (k : A.obj U ⟶ V)
    (hk : k = A.map eI.hom ≫
      (((K.sc n).mapHomologyIso A).inv ≫ homologyMap ψ n) ≫ eJ.inv)
    (C : HomologicalComplex (ModuleCat.{vM} R) c)
    (D : HomologicalComplex (ModuleCat.{vM} S) c)
    (i : (G₀.mapHomologicalComplex c).obj K ⟶ C)
    (j : (G₁.mapHomologicalComplex c).obj L ⟶ D)
    (r : C ⟶ ((ModuleCat.restrictScalars σ).mapHomologicalComplex c).obj D)
    (hsquare : counitSectionsComplexMap A (ModuleCat.restrictScalars σ) η K L ψ ≫
      ((ModuleCat.restrictScalars σ).mapHomologicalComplex c).map j = i ≫ r)
    {HX : Type uH₀} {HY : Type uH₁}
    (eX : C.homology n → HX) (eY : D.homology n → HY) (g : HX → HY)
    (hnorm : ∀ z : C.homology n,
      eY (((D.sc n).mapHomologyIso (ModuleCat.restrictScalars σ)).hom (homologyMap r n z)) =
        g (eX z)) (x : G₀.obj U) :
    eY (homologyMap j n (aY (G₁.map k (η.app U x)))) =
      g (eX (homologyMap i n (aX x))) := by
  let T := ModuleCat.restrictScalars σ
  let q := counitSectionsComplexMap A T η K L ψ
  have hc := congrArg (fun z => homologyMap z n) hsquare
  simp only [homologyMap_comp] at hc
  have ht := ShortComplex.mapHomologyIso_hom_naturality
    ((shortComplexFunctor (ModuleCat.{vM} S) c n).map j) T
  have hH : homologyMap q n ≫
        ((((G₁.mapHomologicalComplex c).obj L).sc n).mapHomologyIso T).hom ≫
          T.map (homologyMap j n) =
      homologyMap i n ≫ homologyMap r n ≫ ((D.sc n).mapHomologyIso T).hom := by
    calc
      _ = homologyMap q n ≫
          (homologyMap ((T.mapHomologicalComplex c).map j) n ≫
            ((D.sc n).mapHomologyIso T).hom) :=
        congrArg (fun z => homologyMap q n ≫ z) ht.symm
      _ = _ := by rw [← Category.assoc, hc, Category.assoc]
  have hb := congrArg (fun z => z ≫ T.map (homologyMap j n))
    (resolutionCounit_homology adj₀ adj₁ A σ η K L ψ n eI eJ aX aY haX haY k hk)
  simp only [Category.assoc] at hb
  rw [hH] at hb
  have hab := congrArg ((forget₂ (ModuleCat.{vM} R) AddCommGrpCat.{vM}).map) hb
  simp only [Functor.map_comp, ModuleCat.forget₂_map_restrictScalars] at hab
  have hx := ConcreteCategory.congr_hom hab x
  simp only [ConcreteCategory.comp_apply] at hx
  exact (congrArg eY hx).trans (hnorm _)

/-- The original additive interface is a thin specialization of the complete value-level
construction. No additional cohomology or scalar-action model is selected. -/
theorem resolutionCounit_cohomology
    (eI : U ≅ K.homology n) (eJ : V ≅ L.homology n)
    (aX : G₀.obj U ⟶ ((G₀.mapHomologicalComplex c).obj K).homology n)
    (aY : G₁.obj V ⟶ ((G₁.mapHomologicalComplex c).obj L).homology n) [IsIso aY]
    (haX : aX ≫ adj₀.homologyCounitMate (K.sc n) = G₀.map eI.hom)
    (haY : aY ≫ adj₁.homologyCounitMate (L.sc n) = G₁.map eJ.hom)
    (k : A.obj U ⟶ V)
    (hk : k = A.map eI.hom ≫
      (((K.sc n).mapHomologyIso A).inv ≫ homologyMap ψ n) ≫ eJ.inv)
    (C : HomologicalComplex (ModuleCat.{vM} R) c)
    (D : HomologicalComplex (ModuleCat.{vM} S) c)
    (i : (G₀.mapHomologicalComplex c).obj K ⟶ C)
    (j : (G₁.mapHomologicalComplex c).obj L ⟶ D)
    (r : C ⟶ ((ModuleCat.restrictScalars σ).mapHomologicalComplex c).obj D)
    (hsquare : counitSectionsComplexMap A (ModuleCat.restrictScalars σ) η K L ψ ≫
      ((ModuleCat.restrictScalars σ).mapHomologicalComplex c).map j = i ≫ r)
    {HX : Type uH₀} {HY : Type uH₁} [AddCommGroup HX] [AddCommGroup HY]
    (eX : C.homology n →+ HX) (eY : D.homology n →+ HY) (g : HX →+ HY)
    (hnorm : ∀ z : C.homology n,
      eY (((D.sc n).mapHomologyIso (ModuleCat.restrictScalars σ)).hom (homologyMap r n z)) =
        g (eX z)) (x : G₀.obj U) :
    eY (homologyMap j n (aY (G₁.map k (η.app U x)))) =
      g (eX (homologyMap i n (aX x))) := by
  exact resolutionCounit_cohomology_values adj₀ adj₁ A σ η K L ψ n eI eJ aX aY
    haX haY k hk C D i j r hsquare eX eY g hnorm x

end CategoryTheory.Adjunction
