/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.EtaleRestrictionUnit
public import Aglib.CategoryTheory.Sites.RepresentedTransfer.OverProducts

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
  MorphismProperty.Over.productTest etaleMorphismProperty V

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

/-- The original first projection of the selected pullback product. -/
abbrev etaleProductFst (V U : X.Etale) : (etaleProductTest V).obj U ⟶ U :=
  MorphismProperty.Over.productFst etaleMorphismProperty V U

/-- The original second projection of the selected pullback product. -/
abbrev etaleProductSnd (V U : X.Etale) : (etaleProductTest V).obj U ⟶ V :=
  MorphismProperty.Over.productSnd etaleMorphismProperty V U

/-- Variation of the fixed factor retains the actual pullback map. -/
abbrev etaleProductMap {V W : X.Etale} (f : V ⟶ W) :
    etaleProductTest V ⟶ etaleProductTest W :=
  MorphismProperty.Over.productMap etaleMorphismProperty f

@[reassoc]
theorem etaleProductMap_snd {V W : X.Etale} (f : V ⟶ W) (U : X.Etale) :
    (etaleProductMap f).app U ≫ etaleProductSnd W U = etaleProductSnd V U ≫ f :=
  MorphismProperty.Over.productMap_snd etaleMorphismProperty f U

/-- The induced map on the original product-test sheaves. -/
def etaleProductSheafMap {V W : X.Etale} (f : V ⟶ W) :
    etaleProductSheaf W ⟶ etaleProductSheaf V :=
  Functor.sheafPushforwardContinuousNatTrans (etaleProductMap f)
    AddCommGrpCat.{u + 1} (Scheme.smallEtaleTopology X) (Scheme.smallEtaleTopology X)

/-- Literal interchange of the two original pullback factors. -/
abbrev etaleProductSymmetry (V U : X.Etale) :
    (etaleProductTest V).obj U ≅ (etaleProductTest U).obj V :=
  MorphismProperty.Over.productSymmetry etaleMorphismProperty V U

@[reassoc]
theorem etaleProductSymmetry_naturality {V W : X.Etale} (f : V ⟶ W) (U : X.Etale) :
    (etaleProductSymmetry V U).hom ≫ (etaleProductTest U).map f =
      (etaleProductMap f).app U ≫ (etaleProductSymmetry W U).hom :=
  MorphismProperty.Over.productSymmetry_naturality etaleMorphismProperty f U

/-- Terminal multiplication uses the original second projection. -/
abbrev etaleProductTerminalIso (V : X.Etale) :
    (etaleProductTest V).obj (etaleTerminal X) ≅ V :=
  MorphismProperty.Over.productTerminalIso etaleMorphismProperty V

@[simp]
theorem etaleProductTerminalIso_hom (V : X.Etale) :
    (etaleProductTerminalIso V).hom = etaleProductSnd V (etaleTerminal X) :=
  MorphismProperty.Over.productTerminalIso_hom etaleMorphismProperty V

@[reassoc]
theorem etaleProductTerminalIso_inv_naturality {V W : X.Etale} (f : V ⟶ W) :
    (etaleProductTerminalIso V).inv ≫ (etaleProductMap f).app (etaleTerminal X) =
      f ≫ (etaleProductTerminalIso W).inv :=
  MorphismProperty.Over.productTerminalIso_inv_naturality etaleMorphismProperty f

@[reassoc]
theorem etaleProductSymmetry_counit (V U : X.Etale) :
    (etaleProductSymmetry V U).hom ≫ (siteEtalePostcomposeAdj U.hom).counit.app V =
      etaleProductSnd V U :=
  MorphismProperty.Over.productSymmetry_counit etaleMorphismProperty V U

@[reassoc]
theorem etaleProductTest_terminal (V U : X.Etale) :
    (etaleProductTest V).map ((etaleTerminalIsTerminal X).from U) ≫
      (etaleProductTerminalIso V).hom = etaleProductSnd V U :=
  MorphismProperty.Over.productTest_terminal etaleMorphismProperty V U

/-- The actual pullback product compared to a chosen categorical product. -/
abbrev etaleProductIso (V U : X.Etale) : (etaleProductTest V).obj U ≅ U ⨯ V :=
  MorphismProperty.Over.productIso etaleMorphismProperty V U

@[reassoc (attr := simp)]
theorem etaleProductIso_hom_fst (V U : X.Etale) :
    (etaleProductIso V U).hom ≫ prod.fst = etaleProductFst V U :=
  MorphismProperty.Over.productIso_hom_fst etaleMorphismProperty V U

@[reassoc (attr := simp)]
theorem etaleProductIso_hom_snd (V U : X.Etale) :
    (etaleProductIso V U).hom ≫ prod.snd = etaleProductSnd V U :=
  MorphismProperty.Over.productIso_hom_snd etaleMorphismProperty V U

end AlgebraicGeometry.Scheme.EtaleCohomology
