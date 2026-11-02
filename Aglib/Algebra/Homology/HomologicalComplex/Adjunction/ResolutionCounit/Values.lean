/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.HomologicalComplex.Adjunction.ResolutionCounit

/-!
# Original coordinates for the resolution and counit comparison

The complete counit calculation is expressed directly through the original
section coordinates, using their proved formulas on the same resolution.
-/

@[expose] public section
noncomputable section

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

/-- Original section coordinates retain the whole resolution and counit comparison.
The coordinate equations identify the supplied maps with the same resolution classes;
the conclusion keeps those original maps without unfolding their implementations. -/
theorem resolutionCounit_cohomology_original_values
    (eI : U ≅ K.homology n) (eJ : V ≅ L.homology n)
    (aX : G₀.obj U ⟶ ((G₀.mapHomologicalComplex c).obj K).homology n)
    (aY : G₁.obj V ⟶ ((G₁.mapHomologicalComplex c).obj L).homology n) [IsIso aY]
    (haX : aX ≫ adj₀.homologyCounitMate (K.sc n) = G₀.map eI.hom)
    (haY : aY ≫ adj₁.homologyCounitMate (L.sc n) = G₁.map eJ.hom)
    (k : A.obj U ⟶ V)
    (hk : k = A.map eI.hom ≫
      ((K.sc n).mapHomologyIso A).inv ≫ homologyMap ψ n ≫ eJ.inv)
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
        g (eX z))
    (eU : G₀.obj U → HX) (eV : G₁.obj V → HY)
    (heU : ∀ x, eU x = eX (homologyMap i n (aX x)))
    (heV : ∀ y, eV y = eY (homologyMap j n (aY y))) (x : G₀.obj U) :
    eV (G₁.map k (η.app U x)) = g (eU x) := by
  have hk' : k = A.map eI.hom ≫
      (((K.sc n).mapHomologyIso A).inv ≫ homologyMap ψ n) ≫ eJ.inv := by
    exact hk.trans (congrArg (fun t => A.map eI.hom ≫ t)
      (Category.assoc ((K.sc n).mapHomologyIso A).inv (homologyMap ψ n) eJ.inv).symm)
  have h := resolutionCounit_cohomology_values adj₀ adj₁ A σ η K L ψ n eI eJ aX aY
    haX haY k hk' C D i j r hsquare eX eY g hnorm x
  exact (heV _).trans (h.trans (congrArg g (heU x).symm))

end CategoryTheory.Adjunction
