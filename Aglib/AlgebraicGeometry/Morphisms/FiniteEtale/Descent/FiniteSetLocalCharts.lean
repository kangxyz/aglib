/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.Descent.FiniteAffineRefinement
public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.FiniteTorsorRepresentation
public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.PullbackCoherence
public import Mathlib.Data.Fintype.EquivFin

/-! Concrete covering, base-change, and universe adapters for the exact
finite-locally-constant set-sheaf predicate used by Stacks03RV. -/

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.FiniteEtale.SheafDescent

universe u

/-- The actual set-valued inverse-image functors compose. -/
def setInverseImageComp {X S T : Scheme.{u}} (f : S ⟶ X) (g : T ⟶ S) :
    Scheme.EtaleCohomology.setInverseImage (g ≫ f) ≅ Scheme.EtaleCohomology.setInverseImage f ⋙
      Scheme.EtaleCohomology.setInverseImage g := by
  let adj := (Scheme.EtaleCohomology.siteBaseChange (g ≫ f)).sheafAdjunctionContinuous (Type (u +
    1))
    (Scheme.smallEtaleTopology X) (Scheme.smallEtaleTopology T)
  let adjf := (Scheme.EtaleCohomology.siteBaseChange f).sheafAdjunctionContinuous (Type (u + 1))
    (Scheme.smallEtaleTopology X) (Scheme.smallEtaleTopology S)
  let adjg := (Scheme.EtaleCohomology.siteBaseChange g).sheafAdjunctionContinuous (Type (u + 1))
    (Scheme.smallEtaleTopology S) (Scheme.smallEtaleTopology T)
  let e := Functor.sheafPushforwardContinuousComp' (Scheme.EtaleCohomology.siteBaseChangeComp f
    g).symm
    (Type (u + 1)) (Scheme.smallEtaleTopology X)
      (Scheme.smallEtaleTopology S) (Scheme.smallEtaleTopology T)
  exact (Adjunction.leftAdjointCompIso adjf adjg adj e).symm

/-- Inverse image preserves the actual constant set sheaves. -/
def setInverseImageConstantIso {X S : Scheme.{u}} (f : S ⟶ X) :
    constantSheaf (Scheme.smallEtaleTopology X) (Type (u + 1)) ⋙
      Scheme.EtaleCohomology.setInverseImage f ≅
      constantSheaf (Scheme.smallEtaleTopology S) (Type (u + 1)) := by
  let hT := MorphismProperty.Over.mkIdTerminal (@Etale : MorphismProperty Scheme.{u}) X
  exact ((constantSheafAdj (Scheme.smallEtaleTopology X) (Type (u + 1)) hT).comp
    ((Scheme.EtaleCohomology.siteBaseChange f).sheafAdjunctionContinuous (Type (u + 1))
      (Scheme.smallEtaleTopology X) (Scheme.smallEtaleTopology S))).leftAdjointUniq
    (constantSheafAdj (Scheme.smallEtaleTopology S) (Type (u + 1))
      (hT.isTerminalObj (Scheme.EtaleCohomology.siteBaseChange f)))

end AlgebraicGeometry.Scheme.FiniteEtale.SheafDescent

namespace AlgebraicGeometry.Scheme.EtaleCohomology.FiniteSetLocalTrivialization

universe u

open AlgebraicGeometry.Scheme.FiniteEtale.SheafDescent
variable {X S : Scheme.{u}} {F : Scheme.EtaleCohomology.SetSheaf X} (t :
  Scheme.EtaleCohomology.FiniteSetLocalTrivialization F)

/-- The exact chart data defines an actual jointly surjective etale cover. -/
def cover : X.Cover (Scheme.precoverage @Etale) where
  I₀ := t.index
  X i := (t.chart i).left
  f i := (t.chart i).hom
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    exact ⟨t.covers, fun _ => inferInstance⟩

/-- Pull back the given charts and their actual finite constant-sheaf isomorphisms. -/
def pullback (f : S ⟶ X) : Scheme.EtaleCohomology.FiniteSetLocalTrivialization
  ((Scheme.EtaleCohomology.setInverseImage f).obj F) where
  index := t.index
  chart i := Scheme.Etale.mk (Limits.pullback.snd (t.chart i).hom f)
  covers x := by
    obtain ⟨i, y, hy⟩ := t.covers (f x)
    obtain ⟨z, hz₁, hz₂⟩ := Scheme.Pullback.exists_preimage_pullback y x hy
    exact ⟨i, z, hz₂⟩
  value := t.value
  finite_value := t.finite_value
  trivialization i := by
    let a := (t.chart i).hom
    let g := Limits.pullback.fst a f
    let h := Limits.pullback.snd a f
    have square : h ≫ f = g ≫ a := Limits.pullback.condition.symm
    exact ((setInverseImageComp f h).app F).symm ≪≫
      eqToIso (congrArg (fun q => (Scheme.EtaleCohomology.setInverseImage q).obj F) square) ≪≫
      (setInverseImageComp a g).app F ≪≫
      (Scheme.EtaleCohomology.setInverseImage g).mapIso (t.trivialization i) ≪≫
      (setInverseImageConstantIso g).app (t.value i)

/-- The finite values can be chosen separately in the scheme universe. -/
def smallValue (i : t.index) : Type u := by
  have := t.finite_value i
  letI := Fintype.ofFinite (t.value i)
  exact ULift.{u} (Fin (Fintype.card (t.value i)))

instance smallValue_finite (i : t.index) : Finite (t.smallValue i) := by
  dsimp [smallValue]
  infer_instance

/-- The equivalence from the small finite model of the chart values to the original value
type. -/
def smallValueEquiv (i : t.index) : t.smallValue i ≃ t.value i := by
  have := t.finite_value i
  letI := Fintype.ofFinite (t.value i)
  exact Equiv.ulift.trans (Fintype.equivFin (t.value i)).symm

/-- The explicit lift returns exactly the original constant-sheaf universe. -/
def smallConstantIso (i : t.index) :
    (constantSheaf (Scheme.smallEtaleTopology (t.chart i).left) (Type (u + 1))).obj
      (ULift.{u + 1} (t.smallValue i)) ≅
    (constantSheaf (Scheme.smallEtaleTopology (t.chart i).left) (Type (u + 1))).obj
      (t.value i) :=
  (constantSheaf _ _).mapIso (Equiv.ulift.trans (t.smallValueEquiv i)).toIso

/-- The local trivialization of the inverse image of `F` using the lifted small finite value
type. -/
def smallTrivialization (i : t.index) :
    (Scheme.EtaleCohomology.setInverseImage (t.chart i).hom).obj F ≅
      (constantSheaf (Scheme.smallEtaleTopology (t.chart i).left) (Type (u + 1))).obj
        (ULift.{u + 1} (t.smallValue i)) :=
  t.trivialization i ≪≫ (t.smallConstantIso i).symm

/-- A finite affine refinement of the trivializing etale cover when `X` is compact. -/
def finiteAffineRefinement [CompactSpace X] :
    Scheme.FiniteEtale.AffineRefinement.Data t.cover :=
  Scheme.FiniteEtale.AffineRefinement.choose t.cover

end AlgebraicGeometry.Scheme.EtaleCohomology.FiniteSetLocalTrivialization

namespace AlgebraicGeometry.Scheme.FiniteEtale.SheafDescent

universe u

theorem isFiniteLocallyConstantSet_pullback {X S : Scheme.{u}} (f : S ⟶ X)
    {F : Scheme.EtaleCohomology.SetSheaf X} (hF :
      Scheme.EtaleCohomology.IsFiniteLocallyConstantSet F) :
    Scheme.EtaleCohomology.IsFiniteLocallyConstantSet ((Scheme.EtaleCohomology.setInverseImage
      f).obj F) := by
  obtain ⟨t⟩ := hF
  exact ⟨t.pullback f⟩

end AlgebraicGeometry.Scheme.FiniteEtale.SheafDescent

/- Migration source: the R5Lab/Aglib mirror; exact module in the migration record.
R5 revision c82abf3a72ce1e1cedf4a4f1fe08bea994ad4df5.
SHA256 7d1016911bdc9399bea8189543e2a7deed1f83e3f60a3282c492577e7777d401.
Definitions, hypotheses and universes are retained modulo native names. -/
