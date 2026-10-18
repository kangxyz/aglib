/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.CategoryTheory.Functor.DiagramLift
public import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent

/-!
# GlobalPullbackReflection

General constructions and comparisons for this native mathematical family.
-/

@[expose] public section

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.FiniteEtale.PurelyInseparable.Global

universe u

/-- The underlying naturality square for the actual over-category pullback
functor is cartesian. -/
theorem overPullback_map_isPullback {X T : Scheme.{u}} (f : T ⟶ X)
    {A B : Over X} (g : A ⟶ B) :
    IsPullback ((Over.pullback f).map g).left (pullback.fst A.hom f)
      (pullback.fst B.hom f) g.left := by
  apply (IsPullback.paste_horiz_iff (IsPullback.of_hasPullback B.hom f).flip
    (show ((Over.pullback f).map g).left ≫ pullback.fst B.hom f =
      pullback.fst A.hom f ≫ g.left from pullback.lift_fst _ _ _)).mp
  simpa only [Over.pullback_map_left, pullback.lift_snd, Over.w] using
    (IsPullback.of_hasPullback A.hom f).flip

/-- Faithful-flat quasi-compact base change is conservative on actual schemes
over the base, by the pinned fpqc isomorphism-descent theorem. -/
theorem overPullback_reflectsIsomorphisms {X T : Scheme.{u}} (f : T ⟶ X)
    [Surjective f] [Flat f] [QuasiCompact f] : (Over.pullback f).ReflectsIsomorphisms where
  reflects {A B} g hg := by
    let : IsIso ((Over.pullback f).map g) := hg
    have h := overPullback_map_isPullback f g
    have hmap : IsIso ((Over.pullback f).map g).left :=
      inferInstanceAs (IsIso ((Over.forget T).map ((Over.pullback f).map g)))
    have hbase : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{u})
        (pullback.fst B.hom f) := ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩
    have : IsIso g.left := MorphismProperty.of_isPullback_of_descendsAlong
      (P := MorphismProperty.isomorphisms Scheme) h hbase hmap
    let : IsIso ((Over.forget X).map g) := this
    exact isIso_of_reflects_iso g (Over.forget X)

end AlgebraicGeometry.Scheme.FiniteEtale.PurelyInseparable.Global

/- Migration source: the R5Lab/Aglib mirror; exact module in the migration record.
R5 revision c82abf3a72ce1e1cedf4a4f1fe08bea994ad4df5.
SHA256 8c9978e0715e1aef281cddb9f130774a2e615b9c301b028805777fd51b79b2c5.
Definitions, hypotheses and universes are retained modulo native names. -/
