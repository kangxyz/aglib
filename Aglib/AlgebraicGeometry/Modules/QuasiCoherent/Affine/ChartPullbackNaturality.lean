/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.ChartPullbackCoordinates
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.RestrictionSectionsNaturality
public import Aglib.Algebra.Category.ModuleCat.ScalarExtensionCoordinateNaturality

/-! # Coefficient naturality on the original affine charts

The scalar-extension comparison for the actual pullback on a supplied pair
of commuting open charts preserves the original coefficient morphisms.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u
open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
  {X Z : Scheme.{u}} (p : Z ⟶ X)
  (j : Spec (CommRingCat.of R) ⟶ X) [IsOpenImmersion j]
  (c : Spec (CommRingCat.of S) ⟶ Z) [IsOpenImmersion c]
  (H : c ≫ p = Spec.map (CommRingCat.ofHom (algebraMap R S)) ≫ j)
  {M N : X.Modules} [M.IsQuasicoherent] [N.IsQuasicoherent]

local notation "φ" => CommRingCat.ofHom (algebraMap R S)

/-- The original affine-chart comparison preserves actual coefficient maps,
including the original geometric pullback and both open restrictions. -/
@[reassoc]
theorem chartPullbackSectionsIso_naturality (q : M ⟶ N) :
    (ModuleCat.extendScalars (algebraMap R S)).map
        (moduleSpecΓFunctor.map ((restrictFunctor j).map q)) ≫
      (chartPullbackSectionsIso p j c H N).hom =
    (chartPullbackSectionsIso p j c H M).hom ≫
      moduleSpecΓFunctor.map ((restrictFunctor c).map ((pullback p).map q)) := by
  have hn := (pullbackOpenSquare c (Spec.map φ) p j H).inv.naturality q
  dsimp only [Functor.comp_map, Functor.comp_obj] at hn
  have hp := affinePullbackGlobalSectionsIso_naturality φ ((restrictFunctor j).map q)
  change (ModuleCat.extendScalars (algebraMap R S)).map
      (moduleSpecΓFunctor.map ((restrictFunctor j).map q)) ≫
      (affinePullbackGlobalSectionsIso φ (N.restrict j)).hom = _ at hp
  simp only [chartPullbackSectionsIso, Iso.trans_hom, Functor.mapIso_hom,
    Iso.symm_hom, Iso.app_inv]
  rw [← Category.assoc, hp, Category.assoc,
    ← Functor.map_comp, hn, Functor.map_comp, Category.assoc]

/-- Specified source-chart coordinates identify the actual pullback of a
coefficient morphism with its scalar extension on the original target chart. -/
@[reassoc]
theorem chartPullbackCoordinatesIso_naturality {L L' : ModuleCat.{u} R}
    (q : M ⟶ N)
    (eM : moduleSpecΓFunctor.obj (M.restrict j) ≅ L)
    (eN : moduleSpecΓFunctor.obj (N.restrict j) ≅ L')
    (b : L ⟶ L')
    (he : moduleSpecΓFunctor.map ((restrictFunctor j).map q) ≫ eN.hom = eM.hom ≫ b) :
    moduleSpecΓFunctor.map ((restrictFunctor c).map ((pullback p).map q)) ≫
      (chartPullbackCoordinatesIso p j c H N eN).hom =
    (chartPullbackCoordinatesIso p j c H M eM).hom ≫
      (ModuleCat.extendScalarsAlgebraIso R S L).inv ≫
      (ModuleCat.extendScalars (algebraMap R S)).map b ≫
      (ModuleCat.extendScalarsAlgebraIso R S L').hom := by
  refine ModuleCat.scalarExtensionCoordinatesIso_naturality
    (chartPullbackSectionsIso p j c H M) (chartPullbackSectionsIso p j c H N)
    eM eN (moduleSpecΓFunctor.map ((restrictFunctor j).map q)) b
    (moduleSpecΓFunctor.map ((restrictFunctor c).map ((pullback p).map q))) ?_ he
  exact chartPullbackSectionsIso_naturality p j c H q

end AlgebraicGeometry.Scheme.Modules
