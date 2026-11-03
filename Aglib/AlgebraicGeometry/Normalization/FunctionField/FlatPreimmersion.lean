/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Normalization.BaseChange.FlatPreimmersion
public import Aglib.AlgebraicGeometry.Normalization.FunctionField
public import Aglib.AlgebraicGeometry.FunctionField.AffineCharts
public import Aglib.AlgebraicGeometry.FunctionField.FlatPreimmersion

/-!
# Generic normalization under a dominant flat preimmersion

The generic source is compared through the original function-field map.
The resulting normalization isomorphism retains both the structural and
generic-source projections of the native normalization pullback.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme

/-- The original generic-inclusion square is cartesian; its field arrow is
the `Spec.map` of the original function-field homomorphism. -/
theorem genericPoint_isPullback_of_flat_preimmersion
    {Y X : Scheme.{u}} [IsIntegral Y] [IsIntegral X]
    (g : Y ⟶ X) [IsDominant g] [Flat g] [IsPreimmersion g] :
    IsPullback (Y.fromSpecStalk (genericPoint Y))
      (Spec.map (CommRingCat.ofHom (Scheme.functionFieldMap g)))
      g (X.fromSpecStalk (genericPoint X)) := by
  let : IsIso (CommRingCat.ofHom (Scheme.functionFieldMap g)) :=
    functionFieldMap_isIso_of_flat_preimmersion g
  let : IsIso (Spec.map (CommRingCat.ofHom (Scheme.functionFieldMap g))) :=
    inferInstanceAs (IsIso (Scheme.Spec.mapIso
      (asIso (CommRingCat.ofHom (Scheme.functionFieldMap g))).op).hom)
  exact IsPullback.of_vert_isIso_mono
    ⟨Scheme.fromSpecStalk_genericPoint_naturality g⟩

/-- Generic normalization commutes with an actual dominant flat
preimmersion, through the native normalization comparison. -/
def genericNormalizationPullbackIso
    {Y X : Scheme.{u}} [IsIntegral Y] [IsIntegral X]
    (g : Y ⟶ X) [IsDominant g] [Flat g] [IsPreimmersion g] :
    (Y.fromSpecStalk (genericPoint Y)).normalization ≅
      pullback (X.fromSpecStalk (genericPoint X)).fromNormalization g := by
  let H := (genericPoint_isPullback_of_flat_preimmersion g).flip
  let e := Hom.normalizationSourceIso H.isoPullback
    (Y.fromSpecStalk (genericPoint Y))
    (pullback.snd (X.fromSpecStalk (genericPoint X)) g) H.isoPullback_hom_snd
  let : IsIso ((X.fromSpecStalk (genericPoint X)).normalizationPullback g) :=
    Hom.normalizationPullback_isIso_of_flat_preimmersion _ g
  exact e ≪≫ asIso ((X.fromSpecStalk (genericPoint X)).normalizationPullback g)

@[reassoc (attr := simp)]
theorem genericNormalizationPullbackIso_hom_snd
    {Y X : Scheme.{u}} [IsIntegral Y] [IsIntegral X]
    (g : Y ⟶ X) [IsDominant g] [Flat g] [IsPreimmersion g] :
    (genericNormalizationPullbackIso g).hom ≫
      pullback.snd (X.fromSpecStalk (genericPoint X)).fromNormalization g =
      (Y.fromSpecStalk (genericPoint Y)).fromNormalization := by
  simp [genericNormalizationPullbackIso]

/-- The second projection equation retains the actual generic-source map,
not an arbitrary isomorphism of the two function fields. -/
@[reassoc (attr := simp)]
theorem toNormalization_genericNormalizationPullbackIso_hom_fst
    {Y X : Scheme.{u}} [IsIntegral Y] [IsIntegral X]
    (g : Y ⟶ X) [IsDominant g] [Flat g] [IsPreimmersion g] :
    (Y.fromSpecStalk (genericPoint Y)).toNormalization ≫
      (genericNormalizationPullbackIso g).hom ≫
      pullback.fst (X.fromSpecStalk (genericPoint X)).fromNormalization g =
      Spec.map (CommRingCat.ofHom (Scheme.functionFieldMap g)) ≫
        (X.fromSpecStalk (genericPoint X)).toNormalization := by
  simp [genericNormalizationPullbackIso, Category.assoc,
    Hom.normalizationSourceIso_hom_generic_assoc]

end AlgebraicGeometry.Scheme
