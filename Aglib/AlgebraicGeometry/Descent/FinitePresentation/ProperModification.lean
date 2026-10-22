/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Descent.FinitePresentation.RelativeClosedImmersion
public import Aglib.AlgebraicGeometry.Limits.ImmersionBaseChange
public import Aglib.AlgebraicGeometry.Morphisms.Proper.Over

/-!
# Eventual properness from an original proper modification

An actual proper surjective modification immersive in a proper target
supplies eventual properness. The later consumer constructs this modification
by weak Chow; it is not a premise of the final approximation theorem.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme

/-- A specified proper surjective modification immersive in a proper target
proves properness after a later actual base transition. -/
theorem exists_isProper_overPullback_of_modification
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u})
    [∀ {i j} (r : i ⟶ j), IsAffineHom (D.map r)]
    [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)]
    (c : Cone D) (hc : IsLimit c) (i : I)
    {X Y P : Over (D.obj i)} (p : Y ⟶ X) (q : Y ⟶ P)
    [IsSeparated X.hom] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [IsProper p.left] [Surjective p.left] [IsImmersion q.left] [IsProper P.hom]
    [IsProper ((Over.pullback (c.π.app i)).obj X).hom] :
    ∃ j : Over i, IsProper ((Over.pullback (D.map j.hom)).obj X).hom := by
  have : QuasiCompact Y.hom := by rw [← p.w]; infer_instance
  have : QuasiCompact (q.left ≫ P.hom) := by rw [q.w]; infer_instance
  have : QuasiCompact q.left := QuasiCompact.of_comp q.left P.hom
  have : IsProper ((Over.pullback (c.π.app i)).map p).left :=
    MorphismProperty.overPullbackMap (P := @IsProper) _ p inferInstance
  have : IsProper ((Over.pullback (c.π.app i)).obj Y).hom :=
    isProper_hom_of_isProper_over_map ((Over.pullback (c.π.app i)).map p)
  have : IsImmersion ((Over.pullback (c.π.app i)).map q).left :=
    MorphismProperty.overPullbackMap (P := @IsImmersion) _ q inferInstance
  have : IsSeparated ((Over.pullback (c.π.app i)).obj P).hom := by
    change IsSeparated (pullback.snd P.hom (c.π.app i))
    infer_instance
  have : IsClosedImmersion ((Over.pullback (c.π.app i)).map q).left :=
    isClosedImmersion_of_immersion_over_proper ((Over.pullback (c.π.app i)).map q)
  have hclosed := (isClosedImmersion_overPullbackMap_iff (c.π.app i) q).mp inferInstance
  obtain ⟨j, hj⟩ := exists_isClosed_preimage_range_of_isLimit D c hc i q.left P.hom
    ((isClosed_preimage_pullback_swap P.hom (c.π.app i) (Set.range q.left)).mp hclosed)
  have : IsClosedImmersion ((Over.pullback (D.map j.hom)).map q).left :=
    (isClosedImmersion_overPullbackMap_iff (D.map j.hom) q).mpr
      ((isClosed_preimage_pullback_swap P.hom (D.map j.hom) (Set.range q.left)).mpr hj)
  have : IsProper ((Over.pullback (D.map j.hom)).obj P).hom := by
    change IsProper (pullback.snd P.hom (D.map j.hom))
    infer_instance
  have : IsProper ((Over.pullback (D.map j.hom)).obj Y).hom :=
    isProper_hom_of_isProper_over_map ((Over.pullback (D.map j.hom)).map q)
  have : Surjective ((Over.pullback (D.map j.hom)).map p).left :=
    MorphismProperty.overPullbackMap (P := @Surjective) _ p inferInstance
  have : IsSeparated ((Over.pullback (D.map j.hom)).obj X).hom := by
    change IsSeparated (pullback.snd X.hom (D.map j.hom))
    infer_instance
  have : LocallyOfFiniteType ((Over.pullback (D.map j.hom)).obj X).hom := by
    change LocallyOfFiniteType (pullback.snd X.hom (D.map j.hom))
    infer_instance
  exact ⟨j, isProper_of_surjective_over_proper ((Over.pullback (D.map j.hom)).map p)⟩

end AlgebraicGeometry.Scheme
