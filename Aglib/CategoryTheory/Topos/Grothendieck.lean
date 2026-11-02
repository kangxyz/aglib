/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.EssentiallySmall
public import Mathlib.CategoryTheory.Sites.Equivalence

/-!
# A bounded Grothendieck-topos object capability

The actual category has one small-site presentation with values in `Type w`.
Only existence is recorded. Native sheaf categories use the existing small
model and site-equivalence construction; no presentation is selected as public
data. Pure adjunction and mate laws retain their weaker hypotheses.
-/

@[expose] public noncomputable section

namespace CategoryTheory.Topos

universe w vE uE vF uF v u

/-- The actual category admits a presentation by sheaves of `w`-small types on
one `w`-small site. Its object and Hom universes remain independent of `w`. -/
-- The bound is part of the question, not determined by the input category.
-- As for EssentiallySmall, retain it in the typeclass resolution cache key.
@[univ_out_params, pp_with_univ]
class IsGrothendieckTopos (E : Type uE) [Category.{vE} E] : Prop where
  /-- One small-site presentation exists; no chosen presentation is exposed. -/
  exists_smallSite :
    ∃ (C : Type w) (_ : SmallCategory C) (J : GrothendieckTopology C),
      Nonempty (E ≌ Sheaf J (Type w))

/-- The native sheaf category has a bounded presentation when its site is
essentially small in the same value universe. -/
instance sheaf_isGrothendieckTopos
    {C : Type u} [Category.{v} C] [EssentiallySmall.{w} C]
    (J : GrothendieckTopology C) :
    IsGrothendieckTopos.{w} (Sheaf J (Type w)) where
  exists_smallSite := by
    let S := SmallModel.{w} C
    let : SmallCategory S := smallCategorySmallModel.{w} C
    let e : C ≌ S := equivSmallModel.{w} C
    let J' := e.inverse.inducedTopology J
    exact ⟨S, inferInstance, J', ⟨Equivalence.sheafCongr J J' e (Type w)⟩⟩

/-- Transport the existence of one bounded presentation along the given
equivalence, without choosing another category or operational structure. -/
theorem IsGrothendieckTopos.ofEquivalence
    {E : Type uE} [Category.{vE} E]
    {F : Type uF} [Category.{vF} F]
    (e : E ≌ F) [hF : IsGrothendieckTopos.{w} F] :
    IsGrothendieckTopos.{w} E := by
  rcases @IsGrothendieckTopos.exists_smallSite F _ hF with ⟨C, hC, J, ⟨p⟩⟩
  let : SmallCategory C := hC
  exact ⟨⟨C, hC, J, ⟨e.trans p⟩⟩⟩

end CategoryTheory.Topos
