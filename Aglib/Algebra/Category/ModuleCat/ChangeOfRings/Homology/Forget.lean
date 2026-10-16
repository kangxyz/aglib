/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.ChangeOfRings.Homology

/-!
# Scalar-extension units and additive homology

Forgetting scalars identifies the native scalar-extension adjunction unit with
the literal map `m ↦ 1 ⊗ m`. The original adjunction mate retains this same
unit under the additive homology comparisons for every ring map. Only the
right adjoint and scalar-forgetting functor preserve homology. The statement
also allows a subsequent actual complex map. Ring, module-carrier and
complex-index universes remain independent.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped TensorProduct ChangeOfRings

namespace ModuleCat

universe u v w t

variable {R : Type u} {S : Type w} [CommRing R] [CommRing S] (φ : R →+* S)

/-- The underlying additive transformation of the original scalar-extension unit. -/
def extendScalarsForgetUnit :
    forget₂ (ModuleCat.{max v w} R) AddCommGrpCat.{max v w} ⟶
      extendScalars φ ⋙ forget₂ (ModuleCat.{max v w} S) AddCommGrpCat.{max v w} :=
  Functor.whiskerRight (extendRestrictScalarsAdj φ).unit
    (forget₂ (ModuleCat.{max v w} R) AddCommGrpCat.{max v w})

/-- The scalar-forgetting unit is literally the unit pure tensor. -/
theorem extendScalarsForgetUnit_app_apply (M : ModuleCat.{max v w} R) (x : M) :
    (extendScalarsForgetUnit φ).app M x = (1 : S) ⊗ₜ[R,φ] x := rfl

/-- The original short-complex homology mate retains the original additive
unit under the native exact scalar-forgetting comparisons. -/
@[reassoc]
theorem extendScalarsForgetUnit_homology_shortComplex
    (A : ShortComplex (ModuleCat.{max v w} R)) :
    (extendScalarsForgetUnit φ).app A.homology ≫
      (forget₂ (ModuleCat.{max v w} S) AddCommGrpCat.{max v w}).map
        (homologyBaseChangeMap φ A) =
    (A.mapHomologyIso
        (forget₂ (ModuleCat.{max v w} R) AddCommGrpCat.{max v w})).inv ≫
      ShortComplex.homologyMap (A.mapNatTrans (extendScalarsForgetUnit φ)) ≫
        ((A.map (extendScalars φ)).mapHomologyIso
          (forget₂ (ModuleCat.{max v w} S) AddCommGrpCat.{max v w})).hom := by
  let T : ModuleCat.{max v w} R ⥤ ModuleCat.{max v w} S := extendScalars φ
  let G : ModuleCat.{max v w} S ⥤ ModuleCat.{max v w} R := restrictScalars φ
  let H : ModuleCat.{max v w} R ⥤ AddCommGrpCat.{max v w} := forget₂ _ _
  let η : 𝟭 (ModuleCat.{max v w} R) ⟶ T ⋙ G :=
    (extendRestrictScalarsAdj.{v, u, w} φ).unit
  have hu := congrArg (fun f => H.map f) (homologyBaseChangeMap_unit φ A)
  rw [Functor.map_comp] at hu
  change (extendScalarsForgetUnit φ).app A.homology ≫
      (forget₂ (ModuleCat.{max v w} S) AddCommGrpCat.{max v w}).map
        (homologyBaseChangeMap φ A) =
      H.map ((extendRestrictScalarsAdj.{v, u, w} φ).homologyUnit A)
    at hu
  rw [hu]
  have hid : (A.mapHomologyIso H).hom ≫
      H.map (A.mapHomologyIso (𝟭 (ModuleCat.{max v w} R))).inv =
      ((A.map (𝟭 (ModuleCat.{max v w} R))).mapHomologyIso H).hom := by
    have h := congrArg (fun f => f ≫
        H.map (A.mapHomologyIso (𝟭 (ModuleCat.{max v w} R))).inv)
      (ShortComplex.mapHomologyIso_comp_hom (𝟭 (ModuleCat.{max v w} R)) H A)
    simpa only [Functor.id_comp, Category.assoc, ← H.map_comp, Iso.hom_inv_id,
      H.map_id, Category.comp_id]
      using h
  have hn := ShortComplex.mapHomologyIso_hom_naturality (A.mapNatTrans η) H
  have hg := ShortComplex.mapHomologyIso_comp_hom G H (A.map T)
  unfold CategoryTheory.Adjunction.homologyUnit
  simp only [Functor.map_comp]
  apply (cancel_epi (A.mapHomologyIso H).hom).mp
  erw [Iso.hom_inv_id_assoc]
  erw [reassoc_of% hid, ← reassoc_of% hn, ← hg]
  rfl

variable {ι : Type t} {c : ComplexShape ι}
  (C : HomologicalComplex (ModuleCat.{max v w} R) c) (n : ι)

/-- The original homology base-change map has the original additive unit formula. -/
@[reassoc]
theorem extendScalarsForgetUnit_homology :
    (extendScalarsForgetUnit φ).app (C.homology n) ≫
      (forget₂ (ModuleCat.{max v w} S) AddCommGrpCat.{max v w}).map
        (extendScalarsHomologyMap φ C n) =
    ((C.sc n).mapHomologyIso
        (forget₂ (ModuleCat.{max v w} R) AddCommGrpCat.{max v w})).inv ≫
      homologyMap ((NatTrans.mapHomologicalComplex (extendScalarsForgetUnit φ) c).app C) n ≫
        (((((extendScalars φ).mapHomologicalComplex c).obj C).sc n).mapHomologyIso
          (forget₂ (ModuleCat.{max v w} S) AddCommGrpCat.{max v w})).hom :=
  extendScalarsForgetUnit_homology_shortComplex φ (C.sc n)

/-- Homology of a scalar-extension unit followed by an actual complex map. -/
@[reassoc]
theorem extendScalarsForgetUnit_homology_map
    (D : HomologicalComplex (ModuleCat.{max v w} S) c)
    (β : ((extendScalars φ).mapHomologicalComplex c).obj C ⟶ D) :
    (extendScalarsForgetUnit φ).app (C.homology n) ≫
      (forget₂ (ModuleCat.{max v w} S) AddCommGrpCat.{max v w}).map
        (extendScalarsHomologyMap φ C n ≫ homologyMap β n) ≫
      ((D.sc n).mapHomologyIso
        (forget₂ (ModuleCat.{max v w} S) AddCommGrpCat.{max v w})).inv =
    ((C.sc n).mapHomologyIso
        (forget₂ (ModuleCat.{max v w} R) AddCommGrpCat.{max v w})).inv ≫
      homologyMap
        ((NatTrans.mapHomologicalComplex (extendScalarsForgetUnit φ) c).app C ≫
          ((forget₂ (ModuleCat.{max v w} S) AddCommGrpCat.{max v w}).mapHomologicalComplex c).map β)
        n := by
  let G := forget₂ (ModuleCat.{max v w} S) AddCommGrpCat.{max v w}
  let T := extendScalars φ
  have hn : G.map (homologyMap β n) ≫ ((D.sc n).mapHomologyIso G).inv =
      ((((T.mapHomologicalComplex c).obj C).sc n).mapHomologyIso G).inv ≫
        homologyMap ((G.mapHomologicalComplex c).map β) n :=
    ShortComplex.mapHomologyIso_inv_naturality
      ((shortComplexFunctor (ModuleCat.{max v w} S) c n).map β) G
  rw [Functor.map_comp]
  simp only [Category.assoc, homologyMap_comp]
  erw [extendScalarsForgetUnit_homology_assoc]
  erw [hn]
  erw [Iso.hom_inv_id_assoc]

/-- An actual additive complex square transports the canonical tensor homology unit. -/
theorem extendScalarsForgetUnit_homology_map_of_square
    (D : HomologicalComplex (ModuleCat.{max v w} S) c)
    (δ : ((extendScalars φ).mapHomologicalComplex c).obj C ⟶ D)
    {A B : HomologicalComplex AddCommGrpCat.{max v w} c}
    (i : ((forget₂ (ModuleCat.{max v w} R) AddCommGrpCat.{max v w}).mapHomologicalComplex c).obj
      C ⟶ A)
    (j : ((forget₂ (ModuleCat.{max v w} S) AddCommGrpCat.{max v w}).mapHomologicalComplex c).obj
      D ⟶ B)
    (g : A ⟶ B)
    (h : (NatTrans.mapHomologicalComplex (extendScalarsForgetUnit φ) c).app C ≫
        ((forget₂ (ModuleCat.{max v w} S) AddCommGrpCat.{max v w}).mapHomologicalComplex c).map
          δ ≫ j =
      i ≫ g) :
    (extendScalarsForgetUnit φ).app (C.homology n) ≫
        (forget₂ (ModuleCat.{max v w} S) AddCommGrpCat.{max v w}).map
          (extendScalarsHomologyMap φ C n ≫ homologyMap δ n) ≫
        ((D.sc n).mapHomologyIso
          (forget₂ (ModuleCat.{max v w} S) AddCommGrpCat.{max v w})).inv ≫
        homologyMap j n =
      ((C.sc n).mapHomologyIso
          (forget₂ (ModuleCat.{max v w} R) AddCommGrpCat.{max v w})).inv ≫
        homologyMap i n ≫ homologyMap g n := by
  have ht := congrArg (fun q => q ≫ homologyMap j n)
    (extendScalarsForgetUnit_homology_map φ C n D δ)
  have hc := congrArg (fun q => homologyMap q n) h
  simp only [homologyMap_comp, Category.assoc] at ht hc
  exact ht.trans (congrArg (fun q => ((C.sc n).mapHomologyIso
    (forget₂ (ModuleCat.{max v w} R) AddCommGrpCat.{max v w})).inv ≫ q) hc)

end ModuleCat
