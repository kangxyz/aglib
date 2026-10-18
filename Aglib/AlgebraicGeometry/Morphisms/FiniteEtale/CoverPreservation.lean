/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.CoverLimits
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal

/-! Preservation of finite limits by the actual cover inclusion and
field-valued finite fibre functor. No connectedness or Galois axioms are used. -/

@[expose] public section

noncomputable section
set_option autoImplicit false

open _root_.CategoryTheory _root_.CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.FiniteEtale
open _root_.AlgebraicGeometry.Scheme.FiniteEtale (fiber fiberToFinite forget forgetToScheme)

universe u
variable {X : Scheme.{u}}

/-- The terminal structure on the object over `X` underlying the terminal finite étale cover. -/
def terminalCoverForgetIsTerminal (X : Scheme.{u}) :
    IsTerminal ((forget X).obj (terminalCover X)) :=
  Over.mkIdTerminal

instance instPreservesTerminalCoverForget (X : Scheme.{u}) :
    PreservesLimit (_root_.CategoryTheory.Functor.empty.{0} (Scheme.FiniteEtale X)) (forget X) :=
  preservesLimit_of_preserves_limit_cone (terminalCoverIsTerminal X)
    ((isLimitMapConeEmptyConeEquiv (forget X) (terminalCover X)).symm
      (terminalCoverForgetIsTerminal X))

instance instPreservesEmptyLimitsCoverForget (X : Scheme.{u}) :
    PreservesLimitsOfShape (Discrete PEmpty.{1}) (forget X) :=
  preservesLimitsOfShape_pempty_of_preservesTerminal (forget X)

variable {Y Z W : Scheme.FiniteEtale X} (f : Y ⟶ W) (g : Z ⟶ W)

/-- The pullback limit structure on the underlying schemes of the finite étale pullback cone. -/
def pullbackCoverSchemeIsLimit :
    IsLimit ((pullbackCoverCone f g).map (forgetToScheme X)) := by
  change IsLimit (PullbackCone.mk (pullback.fst f.hom.left g.hom.left)
    (pullback.snd f.hom.left g.hom.left) _)
  exact pullbackIsPullback f.hom.left g.hom.left

/-- The pullback limit structure on the underlying objects over `X` of the finite étale pullback
cone. -/
def pullbackCoverForgetIsLimit :
    IsLimit ((forget X).mapCone (pullbackCoverCone f g)) := by
  apply isLimitOfReflects (Over.forget X)
  exact ((pullbackCoverCone f g).isLimitMapConeEquiv (forgetToScheme X)).symm
    (pullbackCoverSchemeIsLimit f g)

instance instPreservesPullbackCoverForget : PreservesLimit (cospan f g) (forget X) :=
  preservesLimit_of_preserves_limit_cone (pullbackCoverIsLimit f g)
    (pullbackCoverForgetIsLimit f g)

instance instPreservesPullbacksCoverForget (X : Scheme.{u}) :
    PreservesLimitsOfShape WalkingCospan (forget X) where
  preservesLimit {K} :=
    preservesLimit_of_iso_diagram (forget X) (diagramIsoCospan K).symm

instance instPreservesFiniteLimitsCoverForget (X : Scheme.{u}) :
    PreservesFiniteLimits (forget X) :=
  preservesFiniteLimits_of_preservesTerminal_and_pullbacks (forget X)

variable {K : Type u} [Field K] (s : Spec (CommRingCat.of K) ⟶ X)

instance instPreservesFiniteLimitsFiber : PreservesFiniteLimits (fiber s) := by
  dsimp only [fiber]
  infer_instance

instance instPreservesFiniteLimitsFiberToFinite : PreservesFiniteLimits (fiberToFinite s) := by
  have : PreservesFiniteLimits (fiberToFinite s ⋙ FintypeCat.incl) := by
    change PreservesFiniteLimits (fiber s)
    infer_instance
  exact preservesFiniteLimits_of_reflects_of_preserves (fiberToFinite s) FintypeCat.incl

end AlgebraicGeometry.Scheme.FiniteEtale

/- Migration source: the R5Lab/Aglib mirror; exact module in the migration record.
R5 revision c82abf3a72ce1e1cedf4a4f1fe08bea994ad4df5.
SHA256 5ae8cf6dca04f7ceb14ed0bc7aea7fd379727c88c418863edc9586d5d56f1ce6.
Definitions, hypotheses and universes are retained modulo native names. -/
