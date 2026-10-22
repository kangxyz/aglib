/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Surfaces.Resolution.Principalization
public import Aglib.AlgebraicGeometry.FunctionField.AffineCharts

/-!
# Composition and original field maps of finite point-blowup chains

The chain type and its constructed maps are the existing native objects.
Composition concatenates those actual arrows. For an integral original
scheme each point step is away from its generic point, so the original
function-field map is an isomorphism. No regularity or Noetherianity
hypothesis is added to that field comparison.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.Scheme.Blowup.PointBlowupChain

/-- Concatenate the actual finite chains over their exact composite map. -/
def comp {X Y Z : Scheme.{u}} {f : Y ⟶ X} {g : Z ⟶ Y}
    (c : PointBlowupChain f) (d : PointBlowupChain g) : PointBlowupChain (g ≫ f) := by
  induction c generalizing Z with
  | refl X => simpa only [Category.comp_id] using d
  | @cons X Y x hx hd a tail ih =>
    simpa only [Category.assoc] using
      PointBlowupChain.cons x hx hd (g ≫ a) (ih d)

private theorem ne_genericPoint_of_dimension_two
    {X : Scheme.{u}} [IsIntegral X] (x : X)
    (hd : ringKrullDim (X.presheaf.stalk x) = 2) : x ≠ genericPoint X := by
  intro h
  subst x
  change ringKrullDim X.functionField = 2 at hd
  rw [ringKrullDim_eq_zero_of_field] at hd
  norm_num at hd

/-- The original generic-point stalk homomorphism of the actual point chain
is an isomorphism. Source integrality and dominance are derived from the chain. -/
theorem functionFieldMap_isIso {X Y : Scheme.{u}} {f : Y ⟶ X}
    (c : PointBlowupChain f) (hX : IsIntegral X) :
    let : IsIntegral X := hX
    let : IsIntegral Y := c.isIntegral hX
    let : IsDominant f := c.isDominant hX
    IsIso (CommRingCat.ofHom (Scheme.functionFieldMap f)) := by
  revert hX
  induction c with
  | refl X =>
    intro hX
    let : IsIntegral X := hX
    change IsIso (CommRingCat.ofHom (Scheme.functionFieldMap (𝟙 X)))
    have hid : CommRingCat.ofHom (Scheme.functionFieldMap (𝟙 X)) =
        𝟙 (CommRingCat.of X.functionField) := by
      apply Spec.map_injective
      apply (cancel_mono (X.fromSpecStalk (genericPoint X))).mp
      simpa using (Scheme.fromSpecStalk_genericPoint_naturality (𝟙 X)).symm
    rw [hid]
    infer_instance
  | @cons X Y x hx hd g tail ih =>
    intro hX
    let : IsIntegral X := hX
    let B := blowupDatum (X.fromSpecResidueField x).ker
    have hne := ne_genericPoint_of_dimension_two x hd
    have hcentre := genericPoint_not_mem_pointCentre x hx hne
    let hB : IsIntegral B.Y := pointBlowup_isIntegral X x hx hne
    let : IsIntegral B.Y := hB
    let : IsIntegral Y := tail.isIntegral hB
    let : IsDominant B.map := pointBlowup_isDominant X x hx hne
    let : IsDominant g := tail.isDominant hB
    let : IsIso (CommRingCat.ofHom (Scheme.functionFieldMap B.map)) :=
      B.functionFieldMap_isIso hcentre
    let : IsIso (CommRingCat.ofHom (Scheme.functionFieldMap g)) := ih hB
    change IsIso (CommRingCat.ofHom (Scheme.functionFieldMap (g ≫ B.map)))
    rw [Scheme.functionFieldMap_comp, CommRingCat.ofHom_comp]
    infer_instance

/-- The canonical field equivalence induced by the original chain map.
Its forward homomorphism is exactly the original function-field map. -/
def functionFieldEquiv {X Y : Scheme.{u}} {f : Y ⟶ X}
    (c : PointBlowupChain f) (hX : IsIntegral X) :
    letI : IsIntegral X := hX
    letI : IsIntegral Y := c.isIntegral hX
    X.functionField ≃+* Y.functionField := by
  letI : IsIntegral X := hX
  letI : IsIntegral Y := c.isIntegral hX
  letI : IsDominant f := c.isDominant hX
  letI := c.functionFieldMap_isIso hX
  exact (asIso (CommRingCat.ofHom (Scheme.functionFieldMap f))).commRingCatIsoToRingEquiv

theorem functionFieldEquiv_toRingHom {X Y : Scheme.{u}} {f : Y ⟶ X}
    (c : PointBlowupChain f) (hX : IsIntegral X) :
    let : IsIntegral X := hX
    let : IsIntegral Y := c.isIntegral hX
    let : IsDominant f := c.isDominant hX
    (c.functionFieldEquiv hX).toRingHom = Scheme.functionFieldMap f := rfl

end AlgebraicGeometry.Scheme.Blowup.PointBlowupChain
