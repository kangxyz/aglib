/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Aglib.Algebra.Category.ModuleCat.ChangeOfRings.Homology.Forget

/-!
# Composition of the original homology base-change maps

The canonical scalar-extension homology mates commute with the native
`extendScalarsComp` isomorphism for every two ring maps. Only the exact
scalar-forgetting functors are used in the proof; neither scalar extension
is required to preserve homology. As in the native composition isomorphism,
the three rings have a common universe. The module-carrier and complex-index
universes remain independent.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped TensorProduct ChangeOfRings

universe u v w

namespace ModuleCat

variable {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
  (σ : R →+* S) (τ : S →+* T)

/-- The original scalar units compose through the native scalar-extension
composition isomorphism, after forgetting to additive groups. -/
@[reassoc]
theorem extendScalarsForgetUnit_comp (M : ModuleCat.{max u v} R) :
    (extendScalarsForgetUnit (τ.comp σ)).app M ≫
        (forget₂ (ModuleCat.{max u v} T) AddCommGrpCat.{max u v}).map
          ((extendScalarsComp σ τ).hom.app M) =
      (extendScalarsForgetUnit σ).app M ≫
        (extendScalarsForgetUnit τ).app ((extendScalars σ).obj M) := by
  ext x
  exact extendScalarsComp_hom_app_one_tmul σ τ M x

/-- The same original unit identity holds on the actual mapped complex. -/
theorem extendScalarsForgetUnit_comp_complex {ι : Type w} {c : ComplexShape ι}
    (K : HomologicalComplex (ModuleCat.{max u v} R) c) :
    (NatTrans.mapHomologicalComplex (extendScalarsForgetUnit (τ.comp σ)) c).app K ≫
        ((forget₂ (ModuleCat.{max u v} T) AddCommGrpCat.{max u v}).mapHomologicalComplex c).map
          ((NatTrans.mapHomologicalComplex (extendScalarsComp σ τ).hom c).app K) =
      (NatTrans.mapHomologicalComplex (extendScalarsForgetUnit σ) c).app K ≫
        (NatTrans.mapHomologicalComplex (extendScalarsForgetUnit τ) c).app
          (((extendScalars σ).mapHomologicalComplex c).obj K) := by
  ext1 i
  exact extendScalarsForgetUnit_comp σ τ (K.X i)

end ModuleCat

namespace HomologicalComplex

variable {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
  (σ : R →+* S) (τ : S →+* T) {ι : Type w} {c : ComplexShape ι}
  (K : HomologicalComplex (ModuleCat.{max u v} R) c) (n : ι)

/-- Canonical homology base change composes through the same native scalar
composition isomorphism on both the original homology and the actual complex.
There is no flatness or tensor-homology preservation hypothesis. -/
@[reassoc]
theorem extendScalarsHomologyMap_comp :
    (ModuleCat.extendScalarsComp σ τ).hom.app (K.homology n) ≫
        (ModuleCat.extendScalars τ).map (extendScalarsHomologyMap σ K n) ≫
        extendScalarsHomologyMap τ
          (((ModuleCat.extendScalars σ).mapHomologicalComplex c).obj K) n =
      extendScalarsHomologyMap (τ.comp σ) K n ≫
        homologyMap
          ((NatTrans.mapHomologicalComplex (ModuleCat.extendScalarsComp σ τ).hom c).app K)
          n := by
  let F := ModuleCat.extendScalars σ
  let G := ModuleCat.extendScalars τ
  let U := forget₂ (ModuleCat.{max u v} T) AddCommGrpCat.{max u v}
  let L := (F.mapHomologicalComplex c).obj K
  let D := (G.mapHomologicalComplex c).obj L
  let χ := (NatTrans.mapHomologicalComplex (ModuleCat.extendScalarsComp σ τ).hom c).app K
  let a := extendScalarsHomologyMap σ K n
  let b := extendScalarsHomologyMap τ L n
  let ησ := (NatTrans.mapHomologicalComplex (ModuleCat.extendScalarsForgetUnit σ) c).app K
  let ητ := (NatTrans.mapHomologicalComplex (ModuleCat.extendScalarsForgetUnit τ) c).app L
  let E := (K.sc n).mapHomologyIso
    (forget₂ (ModuleCat.{max u v} R) AddCommGrpCat.{max u v})
  let E'' := (D.sc n).mapHomologyIso U
  have hs := ModuleCat.extendScalarsForgetUnit_homology σ K n
  have ht := ModuleCat.extendScalarsForgetUnit_homology τ L n
  have hn := (ModuleCat.extendScalarsForgetUnit τ).naturality a
  have hleft :
      (ModuleCat.extendScalarsForgetUnit (τ.comp σ)).app (K.homology n) ≫
          U.map ((ModuleCat.extendScalarsComp σ τ).hom.app (K.homology n) ≫
            G.map a ≫ b) ≫ E''.inv =
        E.inv ≫ homologyMap ησ n ≫ homologyMap ητ n := by
    simp only [Functor.map_comp, Category.assoc]
    rw [ModuleCat.extendScalarsForgetUnit_comp_assoc]
    erw [← reassoc_of% hn]
    erw [reassoc_of% hs]
    erw [reassoc_of% ht]
    simp only [E, E'', U, L, D, F, G, ησ, ητ,
      Iso.hom_inv_id_assoc, Iso.hom_inv_id, Category.comp_id]
  have hright := ModuleCat.extendScalarsForgetUnit_homology_map_of_square
    (τ.comp σ) K n D χ (𝟙 _) (𝟙 _) (ησ ≫ ητ)
    (by simpa only [Category.comp_id, Category.id_comp, ησ, ητ, χ, L, F] using
      ModuleCat.extendScalarsForgetUnit_comp_complex σ τ K)
  simp only [homologyMap_comp, homologyMap_id] at hright
  apply ((ModuleCat.extendRestrictScalarsAdj (τ.comp σ)).homEquiv _ _).injective
  apply (forget₂ (ModuleCat.{max u v} R) AddCommGrpCat.{max u v}).map_injective
  change (ModuleCat.extendScalarsForgetUnit (τ.comp σ)).app (K.homology n) ≫
      U.map ((ModuleCat.extendScalarsComp σ τ).hom.app (K.homology n) ≫
        G.map a ≫ b) =
    (ModuleCat.extendScalarsForgetUnit (τ.comp σ)).app (K.homology n) ≫
      U.map (extendScalarsHomologyMap (τ.comp σ) K n ≫ homologyMap χ n)
  apply (cancel_mono E''.inv).mp
  exact hleft.trans hright.symm

end HomologicalComplex
