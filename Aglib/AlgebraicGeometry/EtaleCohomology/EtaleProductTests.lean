/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.EtaleRestrictionUnit

/-! # Actual product tests on the small etale site

The product test attached to `V` sends `U` to the actual scheme pullback
`U ×_X V`, viewed over `X`. Its action on coefficients is the existing
restriction followed by the existing direct image. The symmetry, terminal
comparison and original unit retain their literal scheme projections.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Scheme.EtaleCohomology

attribute [local instance] hasSheafifyLarge

variable {X : Scheme.{u}}

/-- The actual test-scheme product, with the varying object as first factor. -/
abbrev etaleProductTest (V : X.Etale) : X.Etale ⥤ X.Etale :=
  siteBaseChange (X := X) (S := V.left) V.hom ⋙
    siteEtalePostcompose (X := X) (S := V.left) V.hom

instance (V : X.Etale) : (etaleProductTest V).IsContinuous
    (Scheme.smallEtaleTopology X) (Scheme.smallEtaleTopology X) :=
  Functor.isContinuous_comp (siteBaseChange (X := X) (S := V.left) V.hom)
    (siteEtalePostcompose (X := X) (S := V.left) V.hom)
    (Scheme.smallEtaleTopology X) (Scheme.smallEtaleTopology V.left)
    (Scheme.smallEtaleTopology X)

/-- The original restriction-direct-image coefficient, evaluated on product tests. -/
abbrev etaleProductSheaf (V : X.Etale) :
    AbelianSheaf.{u, u + 1} X ⥤ AbelianSheaf.{u, u + 1} X :=
  etaleRestriction (X := X) (S := V.left) V.hom ⋙
    directImage (X := X) (S := V.left) V.hom

/-- The second projection of the actual product test. -/
def etaleProductSnd (V U : X.Etale) : (etaleProductTest V).obj U ⟶ V :=
  MorphismProperty.Over.homMk
    (P := fun {S T : Scheme.{u}} (g : S ⟶ T) => Etale g)
    (pullback.snd U.hom V.hom) rfl (by trivial)

/-- Variation of the fixed factor of the actual product tests. -/
def etaleProductMap {V W : X.Etale} (f : V ⟶ W) :
    etaleProductTest V ⟶ etaleProductTest W where
  app U := MorphismProperty.Over.homMk
    (P := fun {S T : Scheme.{u}} (g : S ⟶ T) => Etale g)
    (pullback.lift (pullback.fst U.hom V.hom)
      (pullback.snd U.hom V.hom ≫ f.left) (by
        rw [Category.assoc, MorphismProperty.Over.w f, pullback.condition])) (by
          change pullback.lift (pullback.fst U.hom V.hom)
            (pullback.snd U.hom V.hom ≫ f.left) _ ≫
              (pullback.snd U.hom W.hom ≫ W.hom) =
            pullback.snd U.hom V.hom ≫ V.hom
          rw [pullback.lift_snd_assoc, Category.assoc, MorphismProperty.Over.w f]) (by trivial)
  naturality U U' g := by
    apply MorphismProperty.Over.Hom.ext
    change pullback.lift (pullback.fst U.hom V.hom ≫ g.left)
        (pullback.snd U.hom V.hom) _ ≫
          pullback.lift (pullback.fst U'.hom V.hom)
            (pullback.snd U'.hom V.hom ≫ f.left) _ =
      pullback.lift (pullback.fst U.hom V.hom)
          (pullback.snd U.hom V.hom ≫ f.left) _ ≫
        pullback.lift (pullback.fst U.hom W.hom ≫ g.left)
          (pullback.snd U.hom W.hom) _
    apply pullback.hom_ext <;>
      simp only [Category.assoc, pullback.lift_fst, pullback.lift_snd,
        pullback.lift_fst_assoc, pullback.lift_snd_assoc]

@[reassoc]
theorem etaleProductMap_snd {V W : X.Etale} (f : V ⟶ W) (U : X.Etale) :
    (etaleProductMap f).app U ≫ etaleProductSnd W U = etaleProductSnd V U ≫ f := by
  apply MorphismProperty.Over.Hom.ext
  change pullback.lift (pullback.fst U.hom V.hom)
    (pullback.snd U.hom V.hom ≫ f.left) _ ≫ pullback.snd U.hom W.hom = _
  exact pullback.lift_snd _ _ _

/-- The induced map on the original product-test sheaves. -/
def etaleProductSheafMap {V W : X.Etale} (f : V ⟶ W) :
    etaleProductSheaf W ⟶ etaleProductSheaf V :=
  Functor.sheafPushforwardContinuousNatTrans (etaleProductMap f)
    AddCommGrpCat.{u + 1} (Scheme.smallEtaleTopology X) (Scheme.smallEtaleTopology X)

/-- Literal interchange of the two factors. -/
def etaleProductSymmetry (V U : X.Etale) :
    (etaleProductTest V).obj U ≅ (etaleProductTest U).obj V :=
  MorphismProperty.Over.isoMk
    (P := fun {S T : Scheme.{u}} (g : S ⟶ T) => Etale g) (pullbackSymmetry U.hom V.hom) (by
    change (pullbackSymmetry U.hom V.hom).hom ≫
      (pullback.snd V.hom U.hom ≫ U.hom) = pullback.snd U.hom V.hom ≫ V.hom
    rw [pullbackSymmetry_hom_comp_snd_assoc]
    exact pullback.condition)

/-- Symmetry respects variation of the actual test scheme. -/
@[reassoc]
theorem etaleProductSymmetry_naturality {V W : X.Etale} (f : V ⟶ W) (U : X.Etale) :
    (etaleProductSymmetry V U).hom ≫ (etaleProductTest U).map f =
      (etaleProductMap f).app U ≫ (etaleProductSymmetry W U).hom := by
  apply MorphismProperty.Over.Hom.ext
  change (pullbackSymmetry U.hom V.hom).hom ≫
      pullback.lift (pullback.fst V.hom U.hom ≫ f.left)
        (pullback.snd V.hom U.hom) _ =
    pullback.lift (pullback.fst U.hom V.hom)
        (pullback.snd U.hom V.hom ≫ f.left) _ ≫
      (pullbackSymmetry U.hom W.hom).hom
  apply pullback.hom_ext <;>
    simp only [Category.assoc, pullback.lift_fst, pullback.lift_snd,
      pullbackSymmetry_hom_comp_fst, pullbackSymmetry_hom_comp_snd,
      pullbackSymmetry_hom_comp_fst_assoc]

/-- Multiplication by the original terminal test is the actual second projection. -/
def etaleProductTerminalIso (V : X.Etale) :
    (etaleProductTest V).obj (etaleTerminal X) ≅ V :=
  MorphismProperty.Over.isoMk
    (P := fun {S T : Scheme.{u}} (g : S ⟶ T) => Etale g)
    (asIso (pullback.snd (𝟙 X) V.hom)) (by
      change pullback.snd (𝟙 X) V.hom ≫ V.hom = pullback.snd (𝟙 X) V.hom ≫ V.hom
      rfl)

@[simp]
theorem etaleProductTerminalIso_hom (V : X.Etale) :
    (etaleProductTerminalIso V).hom = etaleProductSnd V (etaleTerminal X) := by
  apply MorphismProperty.Over.Hom.ext
  rfl

/-- The inverse terminal comparison is natural in the test object. -/
@[reassoc]
theorem etaleProductTerminalIso_inv_naturality {V W : X.Etale} (f : V ⟶ W) :
    (etaleProductTerminalIso V).inv ≫ (etaleProductMap f).app (etaleTerminal X) =
      f ≫ (etaleProductTerminalIso W).inv := by
  apply (cancel_mono (etaleProductTerminalIso W).hom).1
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [etaleProductTerminalIso_hom, etaleProductMap_snd,
    ← etaleProductTerminalIso_hom, Iso.inv_hom_id_assoc]

/-- Symmetry followed by the first projection is the second projection. -/
@[reassoc]
theorem etaleProductSymmetry_counit (V U : X.Etale) :
    (etaleProductSymmetry V U).hom ≫ (siteEtalePostcomposeAdj U.hom).counit.app V =
      etaleProductSnd V U := by
  apply MorphismProperty.Over.Hom.ext
  change (pullbackSymmetry U.hom V.hom).hom ≫ pullback.fst V.hom U.hom =
    pullback.snd U.hom V.hom
  exact pullbackSymmetry_hom_comp_fst _ _

/-- The represented augmentation, followed by terminal transport, is the same projection. -/
@[reassoc]
theorem etaleProductTest_terminal (V U : X.Etale) :
    (etaleProductTest V).map ((etaleTerminalIsTerminal X).from U) ≫
      (etaleProductTerminalIso V).hom = etaleProductSnd V U := by
  apply MorphismProperty.Over.Hom.ext
  change pullback.lift (pullback.fst U.hom V.hom ≫ U.hom)
    (pullback.snd U.hom V.hom) _ ≫ pullback.snd (𝟙 X) V.hom = _
  exact pullback.lift_snd _ _ _

end AlgebraicGeometry.Scheme.EtaleCohomology
