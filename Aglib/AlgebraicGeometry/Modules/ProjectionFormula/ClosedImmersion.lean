/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz, Codex
-/
module

public import Aglib.AlgebraicGeometry.Modules.ProjectionFormula.Stalk
public import Aglib.AlgebraicGeometry.Modules.Pushforward.ClosedImmersion
public import Aglib.AlgebraicGeometry.Modules.Stalk.Reflection

/-!
Source: `Quillen/AlgebraicGeometry/Scheme/Sheaf/ClosedImmersionProjectionFormula.lean` at LOCAL
Quillen
`189a8e779f0c68b2dfc6f8195daebb3e684a5905`. Selection: whole_general;
source ranges [[1, 127]]. Actual objects, maps and hypotheses are preserved.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory

namespace AlgebraicGeometry.Scheme.Modules

theorem isIso_projectionFormulaMap_moduleStalk_off_image {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsClosedImmersion f] (E : Y.Modules) (M : X.Modules)
    (y : Y) (hy : y ∉ Set.range f) :
    IsIso ((moduleStalk Y y).map (projectionFormulaMap f E M)) := by
  let T := tensorLeft ((moduleStalk Y y).obj E)
  let : PreservesBinaryBiproducts T := preservesBinaryBiproducts_of_preservesBinaryCoproducts _
  let : T.Additive := Functor.additive_of_preservesBinaryBiproducts _
  have hq := isZero_closedImmersion_moduleStalk_of_not_mem f y hy M
  have hs : IsZero ((moduleStalk Y y).obj
      ((moduleTensorLeftFunctor Y E).obj ((Scheme.Modules.pushforward f).obj M))) :=
    (T.map_isZero hq).of_iso
      (moduleTensorStalkIso Y y E ((Scheme.Modules.pushforward f).obj M))
  have ht := isZero_closedImmersion_moduleStalk_of_not_mem f y hy
    ((moduleTensorLeftFunctor X ((Scheme.Modules.pullback f).obj E)).obj M)
  let : Mono ((moduleStalk Y y).map (projectionFormulaMap f E M)) := hs.mono _
  let : Epi ((moduleStalk Y y).map (projectionFormulaMap f E M)) := ht.epi _
  exact isIso_of_mono_of_epi _

theorem isIso_projectionFormulaMap_of_closedImmersion {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsClosedImmersion f] (E : Y.Modules) (M : X.Modules) :
    IsIso (projectionFormulaMap f E M) := by
  apply isIso_of_moduleStalk
  intro y
  by_cases hy : y ∈ Set.range f
  · obtain ⟨x, rfl⟩ := hy
    exact isIso_projectionFormulaMap_moduleStalk_of_isInducing f
      f.isClosedEmbedding.isInducing x E M
  · exact isIso_projectionFormulaMap_moduleStalk_off_image f E M y hy

/-- The actual projection-formula isomorphism for a closed immersion and arbitrary module
coefficients. -/
def closedImmersionProjectionFormulaIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsClosedImmersion f] (E : Y.Modules) (M : X.Modules) :
    (moduleTensorLeftFunctor Y E).obj ((Scheme.Modules.pushforward f).obj M) ≅
      (Scheme.Modules.pushforward f).obj
        ((moduleTensorLeftFunctor X ((Scheme.Modules.pullback f).obj E)).obj M) := by
  letI := isIso_projectionFormulaMap_of_closedImmersion f E M
  exact asIso (projectionFormulaMap f E M)

theorem closedImmersionProjectionFormulaIso_hom {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsClosedImmersion f] (E : Y.Modules) (M : X.Modules) :
    (closedImmersionProjectionFormulaIso f E M).hom = projectionFormulaMap f E M := rfl

theorem closedImmersionProjectionFormulaIso_section {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsClosedImmersion f] (E : Y.Modules) (M : X.Modules) (U : Y.Opens)
    (e : Γ(E, U)) (m : Γ((Scheme.Modules.pushforward f).obj M, U)) :
    (closedImmersionProjectionFormulaIso f E M).hom.app U
        (moduleTensorSection Y E ((Scheme.Modules.pushforward f).obj M) U e m) =
      moduleTensorSection X ((Scheme.Modules.pullback f).obj E) M (f ⁻¹ᵁ U)
        (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app E).app U e) m :=
  projectionFormulaMap_section f E M U e m

theorem closedImmersionProjectionFormulaIso_naturality_right {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsClosedImmersion f] (E : Y.Modules) {M N : X.Modules} (g : M ⟶ N) :
    (moduleTensorLeftFunctor Y E).map ((Scheme.Modules.pushforward f).map g) ≫
        (closedImmersionProjectionFormulaIso f E N).hom =
      (closedImmersionProjectionFormulaIso f E M).hom ≫ (Scheme.Modules.pushforward f).map
        ((moduleTensorLeftFunctor X ((Scheme.Modules.pullback f).obj E)).map g) :=
  projectionFormulaMap_naturality f E g

theorem closedImmersionProjectionFormulaIso_naturality_left {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsClosedImmersion f] {E E' : Y.Modules} (g : E ⟶ E') (M : X.Modules) :
    (moduleTensorCoefficientMap Y g).app ((Scheme.Modules.pushforward f).obj M) ≫
        (closedImmersionProjectionFormulaIso f E' M).hom =
      (closedImmersionProjectionFormulaIso f E M).hom ≫ (Scheme.Modules.pushforward f).map
        ((moduleTensorCoefficientMap X ((Scheme.Modules.pullback f).map g)).app M) :=
  (projectionFormulaNatTrans f M).naturality g

/-- The closed-immersion projection formula, natural in the target coefficient sheaf. -/
def closedImmersionProjectionFormulaCoefficientNatIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsClosedImmersion f] (M : X.Modules) :
    moduleTensorRightFunctor Y ((Scheme.Modules.pushforward f).obj M) ≅
      Scheme.Modules.pullback f ⋙ moduleTensorRightFunctor X M ⋙
        Scheme.Modules.pushforward f :=
  NatIso.ofComponents (fun E => closedImmersionProjectionFormulaIso f E M)
    (fun g => closedImmersionProjectionFormulaIso_naturality_left f g M)

/-- The closed-immersion projection formula, natural in the module sheaf on the source. -/
def closedImmersionProjectionFormulaModuleNatIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsClosedImmersion f] (E : Y.Modules) :
    Scheme.Modules.pushforward f ⋙ moduleTensorLeftFunctor Y E ≅
      moduleTensorLeftFunctor X ((Scheme.Modules.pullback f).obj E) ⋙
        Scheme.Modules.pushforward f :=
  NatIso.ofComponents (closedImmersionProjectionFormulaIso f E)
    (fun g => closedImmersionProjectionFormulaIso_naturality_right f E g)

end AlgebraicGeometry.Scheme.Modules
