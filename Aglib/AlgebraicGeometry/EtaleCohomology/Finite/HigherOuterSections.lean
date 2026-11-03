/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Finite.HigherOuterComposition
public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.PullbackCycleSections
public import Aglib.CategoryTheory.Sites.SheafCohomology.ModuleCoefficients.DerivedPostcompResolution
public import Aglib.Algebra.Homology.ShortComplex.MapHomology.Components
public import
  Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.BaseChange.CycleSectionChase

/-! # The fixed original class under finite-target reduction

Both higher-image sections are represented using the same original injective
resolution and the same cocycle. Exact finite postcomposition, the original
terminal-section coherence, and cycle projection determine the comparison.
The original Ext world remains independent; no edge-map injectivity or
external compatibility certificate is assumed.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian HomologicalComplex

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Finite

universe u w

attribute [local instance] hasSheafifyLarge

variable {Y X S : Scheme.{u}} (f : X ⟶ S) [IsFinite f] (k : Y ⟶ X)

/-- The original finite-outer comparison on any supplied integer resolution. -/
private theorem finiteOuter_resolution {M : AbelianSheaf.{u, u + 1} Y}
    (I : InjectiveResolution M) (q : ℕ) :
    let K := ((directImage k).mapHomologicalComplex (.up ℤ)).obj I.cochainComplex
    let d := (NatTrans.mapHomologicalComplex
      (directImageCompIso f k).inv (.up ℤ)).app I.cochainComplex
    (higherDirectImageFiniteOuterIso f k q).hom.app M ≫
        (directImage f).map (I.isoRightDerivedObjCochain (directImage k) q).hom =
      (I.isoRightDerivedObjCochain (directImage (k ≫ f)) q).hom ≫
        homologyMap d (q : ℤ) ≫ ((K.sc (q : ℤ)).mapHomologyIso (directImage f)).hom := by
  dsimp only
  have hp := Sheaf.ModuleCoefficients.rightDerivedPostcompIso_hom_resolution_cochain
    (directImage k) (directImage f) I q
  have hn := InjectiveResolution.isoRightDerivedObjCochain_hom_natTrans
    (directImageCompIso f k).inv I q
  change ((NatTrans.rightDerived (directImageCompIso f k).inv q).app M ≫
      (Functor.rightDerivedPostcompIso (directImage k) (directImage f) q).hom.app M) ≫
        (directImage f).map (I.isoRightDerivedObjCochain (directImage k) q).hom = _
  erw [Category.assoc, hp, ← Category.assoc, hn, Category.assoc]

/-- Finite-target reduction preserves the section of the same original class.
This is the class-dependent compatibility needed after two-field effacement,
not merely an abstract isomorphism between global-section groups. -/
theorem finiteOuterHigherGlobalSectionsIso_cohomologyToHigherSections
    [HasExt.{w} (AbelianSheaf.{u, u + 1} Y)]
    (M : AbelianSheaf.{u, u + 1} Y) (q : ℕ) (x : Sheaf.H.{w} M q) :
    (finiteOuterHigherGlobalSectionsIso f k q M).hom
        (cohomologyToHigherSections (k ≫ f) M q x) =
      cohomologyToHigherSections k M q x := by
  let I := injectiveResolution M
  obtain ⟨a, ha, rfl⟩ := I.extMk_surjective x (q + 1) rfl
  let K := ((directImage k).mapHomologicalComplex (.up ℤ)).obj I.cochainComplex
  let L := ((directImage (k ≫ f)).mapHomologicalComplex (.up ℤ)).obj I.cochainComplex
  let d := (NatTrans.mapHomologicalComplex
    (directImageCompIso f k).inv (.up ℤ)).app I.cochainComplex
  let G := directImage f
  let Γ := globalSections S
  let Δ := globalSections X
  let η := directImageGlobalSectionsIso f
  let c := cyclesMap d (q : ℤ) ≫ ((K.sc (q : ℤ)).mapCyclesIso G).hom
  let v := Γ.map (d.f (q : ℤ)) ≫ η.hom.app (K.X (q : ℤ))
  let zmap := Γ.map c ≫ η.hom.app (K.cycles (q : ℤ))
  obtain ⟨z, hz, hx⟩ := cohomologyToHigherSections_cycles_extMk (k ≫ f) I q a ha
  obtain ⟨z', hz', hy⟩ := cohomologyToHigherSections_cycles_extMk k I q a ha
  have hci : c ≫ G.map (K.iCycles (q : ℤ)) =
      L.iCycles (q : ℤ) ≫ d.f (q : ℤ) := by
    dsimp only [c]
    erw [Category.assoc]
    change cyclesMap d (q : ℤ) ≫
      ((K.sc (q : ℤ)).mapCyclesIso G).hom ≫ G.map (K.sc (q : ℤ)).iCycles = _
    erw [ShortComplex.mapCyclesIso_hom_iCycles]
    exact HomologicalComplex.cyclesMap_i d (q : ℤ)
  have hcp : L.homologyπ (q : ℤ) ≫ homologyMap d (q : ℤ) ≫
      ((K.sc (q : ℤ)).mapHomologyIso G).hom = c ≫ G.map (K.homologyπ (q : ℤ)) := by
    erw [← Category.assoc, HomologicalComplex.homologyπ_naturality, Category.assoc]
    change cyclesMap d (q : ℤ) ≫ ((K.sc (q : ℤ)).map G).homologyπ ≫
      ((K.sc (q : ℤ)).mapHomologyIso G).hom = _
    erw [ShortComplex.homologyπ_mapHomologyIso_hom]
    exact (Category.assoc _ _ _).symm
  have hi : zmap ≫ Δ.map (K.iCycles (q : ℤ)) = Γ.map (L.iCycles (q : ℤ)) ≫ v := by
    have hn := η.hom.naturality (K.iCycles (q : ℤ))
    change Γ.map (G.map (K.iCycles (q : ℤ))) ≫ η.hom.app (K.X (q : ℤ)) =
      η.hom.app (K.cycles (q : ℤ)) ≫ Δ.map (K.iCycles (q : ℤ)) at hn
    dsimp only [zmap, v]
    erw [Category.assoc, ← hn, ← Category.assoc, ← Γ.map_comp, hci, Γ.map_comp,
      Category.assoc]
  have ht : v ≫ (directImageGlobalSectionsIso k).hom.app (I.cochainComplex.X (q : ℤ)) =
      (directImageGlobalSectionsIso (k ≫ f)).hom.app (I.cochainComplex.X (q : ℤ)) ≫
        𝟙 _ := by
    have h := congrArg (fun e => e.hom.app (I.cochainComplex.X (q : ℤ)))
      (directImageGlobalSectionsIso_comp f k)
    change η.hom.app (K.X (q : ℤ)) ≫
        (directImageGlobalSectionsIso k).hom.app (I.cochainComplex.X (q : ℤ)) =
      Γ.map ((directImageCompIso f k).hom.app (I.cochainComplex.X (q : ℤ))) ≫
        (directImageGlobalSectionsIso (k ≫ f)).hom.app
          (I.cochainComplex.X (q : ℤ)) at h
    dsimp only [v]
    rw [Category.assoc, h, ← Category.assoc, ← Γ.map_comp]
    change Γ.map ((directImageCompIso f k).inv.app _ ≫
      (directImageCompIso f k).hom.app _) ≫ _ = _
    rw [Iso.inv_hom_id_app, Γ.map_id, Category.id_comp, Category.comp_id]
  have hp : Γ.map (L.homologyπ (q : ℤ)) ≫
        (Γ.mapIso (I.isoRightDerivedObjCochain (directImage (k ≫ f)) q)).inv ≫
        (finiteOuterHigherGlobalSectionsIso f k q M).hom ≫
        (Δ.mapIso (I.isoRightDerivedObjCochain (directImage k) q)).hom =
      zmap ≫ Δ.map (K.homologyπ (q : ℤ)) := by
    have hn := η.hom.naturality (I.isoRightDerivedObjCochain (directImage k) q).hom
    have hπ := η.hom.naturality (K.homologyπ (q : ℤ))
    change Γ.map (G.map (I.isoRightDerivedObjCochain (directImage k) q).hom) ≫
        η.hom.app (K.homology (q : ℤ)) =
      η.hom.app ((higherDirectImage k q).obj M) ≫
        Δ.map (I.isoRightDerivedObjCochain (directImage k) q).hom at hn
    change Γ.map (G.map (K.homologyπ (q : ℤ))) ≫ η.hom.app (K.homology (q : ℤ)) =
      η.hom.app (K.cycles (q : ℤ)) ≫ Δ.map (K.homologyπ (q : ℤ)) at hπ
    simp only [Functor.mapIso_inv, Functor.mapIso_hom,
      finiteOuterHigherGlobalSectionsIso_hom, Category.assoc]
    have hβ : Γ.map ((higherDirectImageFiniteOuterIso f k q).hom.app M) ≫
        Γ.map (G.map (I.isoRightDerivedObjCochain (directImage k) q).hom) =
      Γ.map (I.isoRightDerivedObjCochain (directImage (k ≫ f)) q).hom ≫
        Γ.map (homologyMap d (q : ℤ) ≫ ((K.sc (q : ℤ)).mapHomologyIso G).hom) := by
      exact (Γ.map_comp _ _).symm.trans
        ((congrArg Γ.map (finiteOuter_resolution f k I q)).trans (Γ.map_comp _ _))
    have hcancel :
        Γ.map (I.isoRightDerivedObjCochain (directImage (k ≫ f)) q).inv ≫
          Γ.map (I.isoRightDerivedObjCochain (directImage (k ≫ f)) q).hom = 𝟙 _ := by
      rw [← Γ.map_comp, Iso.inv_hom_id, Γ.map_id]
    have hcpΓ : Γ.map (L.homologyπ (q : ℤ)) ≫
        Γ.map (homologyMap d (q : ℤ) ≫ ((K.sc (q : ℤ)).mapHomologyIso G).hom) =
      Γ.map c ≫ Γ.map (G.map (K.homologyπ (q : ℤ))) := by
      exact (Γ.map_comp _ _).symm.trans
        ((congrArg Γ.map hcp).trans (Γ.map_comp _ _))
    rw [← hn]
    have hβη := Category.assoc
      (Γ.map (I.isoRightDerivedObjCochain (directImage (k ≫ f)) q).hom)
      (Γ.map (homologyMap d (q : ℤ) ≫ ((K.sc (q : ℤ)).mapHomologyIso G).hom))
      (η.hom.app (K.homology (q : ℤ)))
    have hcη := Category.assoc (Γ.map c) (Γ.map (G.map (K.homologyπ (q : ℤ))))
      (η.hom.app (K.homology (q : ℤ)))
    erw [reassoc_of% hβ, hβη, reassoc_of% hcancel,
      reassoc_of% hcpΓ, hcη, hπ]
    rfl
  have hzterm :
      (directImageGlobalSectionsIso k).hom.app (I.cochainComplex.X (q : ℤ))
          (Δ.map (K.iCycles (q : ℤ)) z') =
        (𝟙 ((globalSections Y).obj (I.cochainComplex.X (q : ℤ))))
          ((directImageGlobalSectionsIso (k ≫ f)).hom.app
            (I.cochainComplex.X (q : ℤ)) (Γ.map (L.iCycles (q : ℤ)) z)) := by
    rw [hz, hz']
    exact (ConcreteCategory.congr_hom ((directImageGlobalSectionsIso k).inv_hom_id_app _) _).trans
      (ConcreteCategory.congr_hom
        ((directImageGlobalSectionsIso (k ≫ f)).inv_hom_id_app _) _).symm
  exact cycle_section_chase
    (Γ.map (L.iCycles (q : ℤ))) (Δ.map (K.iCycles (q : ℤ)))
    (Γ.map (L.homologyπ (q : ℤ))) (Δ.map (K.homologyπ (q : ℤ)))
    (Γ.mapIso (I.isoRightDerivedObjCochain (directImage (k ≫ f)) q))
    (Δ.mapIso (I.isoRightDerivedObjCochain (directImage k) q)) zmap v
    (finiteOuterHigherGlobalSectionsIso f k q M).hom
    ((directImageGlobalSectionsIso (k ≫ f)).hom.app (I.cochainComplex.X (q : ℤ)))
    ((directImageGlobalSectionsIso k).app (I.cochainComplex.X (q : ℤ))) (𝟙 _)
    hi ht hp _ _ z z' hx hy hzterm

end AlgebraicGeometry.Scheme.EtaleCohomology.Finite
