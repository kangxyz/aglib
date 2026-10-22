/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Approximation.ProperSystem
public import Aglib.AlgebraicGeometry.Approximation.ClosedSubscheme.System
public import Aglib.AlgebraicGeometry.Limits.ClosedImmersion
public import Aglib.AlgebraicGeometry.Morphisms.Proper.Chow.FinitePresentation

/-!
# Proper stages of a closed-subscheme approximation

Pull the actual closed-subscheme system to a proper-surjective modification.
Its proper limit embeds closedly in the proper target. Varying-source eventual
closedness then makes one modified stage proper, and properness descends to
the original stage. Restriction to the native cofinal tail retains the limit.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.Approximation

/-- The actual pullback of a proper closed subscheme is closed in the proper
Chow target. Properness is needed only for this limiting subscheme. -/
theorem isClosedImmersion_modified_limit {S : Scheme.{u}}
    {Y W P : Over S} (p : W ⟶ Y) (q : W ⟶ P) (Z : Over Y.left)
    [IsProper p.left] [IsImmersion q.left] [IsProper P.hom]
    [IsClosedImmersion Z.hom] [IsProper (Z.hom ≫ Y.hom)] :
    IsClosedImmersion (pullback.snd Z.hom p.left ≫ q.left) := by
  let WS : Over S := Over.mk (pullback.snd Z.hom p.left ≫ W.hom)
  let b : WS ⟶ P := Over.homMk (pullback.snd Z.hom p.left ≫ q.left) (by
    dsimp only [WS, Over.mk_hom]
    rw [Category.assoc, q.w])
  have hw : pullback.snd Z.hom p.left ≫ W.hom =
      pullback.fst Z.hom p.left ≫ (Z.hom ≫ Y.hom) := by
    rw [← p.w, ← Category.assoc, ← pullback.condition, Category.assoc]
  have : IsProper WS.hom := by
    change IsProper (pullback.snd Z.hom p.left ≫ W.hom)
    rw [hw]
    infer_instance
  have : IsImmersion b.left := inferInstanceAs
    (IsImmersion (pullback.snd Z.hom p.left ≫ q.left))
  exact isClosedImmersion_of_immersion_over_proper b

/-- A proper limiting closed subscheme makes some actual stage of its
closed-subscheme system proper. The supplied Chow packet is transported as a
whole, and eventual closedness concerns the varying modified sources. -/
theorem exists_isProper_stage_of_modification
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    {S : Scheme.{u}} [IsAffine S] {Y W P : Over S}
    (p : W ⟶ Y) (q : W ⟶ P)
    [IsSeparated Y.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    [IsProper p.left] [Surjective p.left] [IsImmersion q.left] [IsProper P.hom]
    (D : I ⥤ Over Y.left) [∀ i, IsClosedImmersion (D.obj i).hom]
    (c : Cone D) (hc : IsLimit c)
    [IsClosedImmersion c.pt.hom] [IsProper (c.pt.hom ≫ Y.hom)] :
    ∃ i, IsProper ((D.obj i).hom ≫ Y.hom) := by
  have : CompactSpace Y.left := QuasiCompact.compactSpace_of_compactSpace Y.hom
  have : QuasiSeparatedSpace Y.left := quasiSeparatedSpace_of_quasiSeparated Y.hom
  have : CompactSpace W.left := QuasiCompact.compactSpace_of_compactSpace p.left
  have : QuasiSeparatedSpace W.left := quasiSeparatedSpace_of_quasiSeparated p.left
  have : CompactSpace P.left := QuasiCompact.compactSpace_of_compactSpace P.hom
  have : QuasiSeparatedSpace P.left := quasiSeparatedSpace_of_quasiSeparated P.hom
  let F : Over Y.left ⥤ Over P.left := Over.pullback p.left ⋙ Over.map q.left
  let E : I ⥤ Over P.left := D ⋙ F
  let d : Cone E := F.mapCone c
  have hd : IsLimit ((Over.forget P.left).mapCone d) :=
    isLimitOfPreserves (Over.pullback p.left ⋙ Over.forget W.left) hc
  have (i : I) : CompactSpace (E.obj i).left := by
    change CompactSpace (pullback (D.obj i).hom p.left : Scheme)
    exact QuasiCompact.compactSpace_of_compactSpace (pullback.snd (D.obj i).hom p.left)
  have (i : I) : QuasiSeparatedSpace (E.obj i).left := by
    change QuasiSeparatedSpace (pullback (D.obj i).hom p.left : Scheme)
    exact quasiSeparatedSpace_of_quasiSeparated (pullback.snd (D.obj i).hom p.left)
  have {i j : I} (r : i ⟶ j) : IsClosedImmersion (E.map r).left := by
    change IsClosedImmersion ((Over.pullback p.left).map (D.map r)).left
    exact MorphismProperty.overPullbackMap (P := @IsClosedImmersion) p.left (D.map r)
      inferInstance
  have (i : I) : LocallyOfFiniteType (E.obj i).hom := by
    change LocallyOfFiniteType (pullback.snd (D.obj i).hom p.left ≫ q.left)
    infer_instance
  have : IsClosedImmersion d.pt.hom :=
    isClosedImmersion_modified_limit p q c.pt
  obtain ⟨i, hi⟩ := exists_isClosedImmersion_over_of_isLimit E d hd
  let : IsClosedImmersion (pullback.snd (D.obj i).hom p.left ≫ q.left) := hi
  exact ⟨i, isProper_of_closed_modified_stage p q (D.obj i)⟩

/-- A closed finitely presented approximation inside a separated finitely
presented affine-base ambient scheme has an actual proper cofinal tail.
The Chow modification is constructed internally, not supplied. -/
theorem nonempty_properSystem_of_closedApproximation
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    {X S : Scheme.{u}} [IsAffine S] (f : X ⟶ S) [IsProper f]
    (Y : Over S) [IsSeparated Y.hom] [LocallyOfFinitePresentation Y.hom]
    [QuasiCompact Y.hom] (i : X ⟶ Y.left) [IsClosedImmersion i]
    (hi : i ≫ Y.hom = f)
    (D : I ⥤ Over Y.left) [∀ j, IsClosedImmersion (D.obj j).hom]
    [∀ j, LocallyOfFinitePresentation (D.obj j).hom]
    (c : Cone D) (hpoint : c.pt = Over.mk i) (hc : IsLimit c)
    [∀ j, IsClosedImmersion (c.π.app j).left] :
    Nonempty (ProperFinitePresentationSystem f) := by
  have : IsClosedImmersion c.pt.hom := by rw [hpoint]; exact inferInstanceAs (IsClosedImmersion i)
  have : IsProper (c.pt.hom ≫ Y.hom) := by
    rw [hpoint]
    change IsProper (i ≫ Y.hom)
    rw [hi]
    infer_instance
  obtain ⟨W, P, p, q, hp, hs, hq, hP⟩ :=
    Chow.exists_immersion_proper_modification_of_finitePresentation Y
  let := hp
  let := hs
  let := hq
  let := hP
  obtain ⟨j, hj⟩ := exists_isProper_stage_of_modification p q D c hc
  let E : I ⥤ Over S := D ⋙ Over.map Y.hom
  let d : Cone E := (Over.map Y.hom).mapCone c
  have hd : IsLimit ((Over.forget S).mapCone d) :=
    isLimitOfPreserves (Over.forget Y.left) hc
  have hpoint' : d.pt = Over.mk f := by
    change (Over.map Y.hom).obj c.pt = Over.mk f
    rw [hpoint]
    exact congrArg Over.mk hi
  have (k : I) : LocallyOfFinitePresentation (E.obj k).hom := by
    change LocallyOfFinitePresentation ((D.obj k).hom ≫ Y.hom)
    infer_instance
  have {k l : I} (r : k ⟶ l) : IsClosedImmersion (E.map r).left :=
    inferInstanceAs (IsClosedImmersion (D.map r).left)
  have (k : I) : IsClosedImmersion (d.π.app k).left :=
    inferInstanceAs (IsClosedImmersion (c.π.app k).left)
  have : IsProper (E.obj j).hom := hj
  exact ⟨ProperFinitePresentationSystem.ofProperStage f E d hpoint' hd j⟩

end AlgebraicGeometry.Scheme.Approximation
