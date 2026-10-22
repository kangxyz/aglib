/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.FiniteType.ColimitGenerators
public import Mathlib.AlgebraicGeometry.AffineTransitionLimit

/-!
# Finite-type graphs into affine approximation stages

For an affine inverse limit and a finite-type map to an affine base, the
original map together with one stage projection is a closed immersion into
the literal fiber product. Finite algebra generators are captured at one
stage. No finite-presentation condition on the limit or surjectivity of the
transition maps is assumed.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.Scheme

/-- The original finite-type structural map and one affine-limit projection
jointly define a closed immersion into their literal fiber product. -/
lemma exists_isClosedImmersion_graph_of_isLimit_of_isAffine
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) [∀ i, IsAffine (D.obj i)]
    (c : Cone D) (hc : IsLimit c)
    {S T : Scheme.{u}} [IsAffine S] [IsAffine T]
    (s : S ⟶ T) (t : ∀ i, D.obj i ⟶ T)
    (f : c.pt ⟶ S) [LocallyOfFiniteType f]
    (h : ∀ i, c.π.app i ≫ t i = f ≫ s) :
    ∃ i, IsClosedImmersion (pullback.lift (c.π.app i) f (h i)) := by
  have : IsAffine c.pt := Scheme.isAffine_of_isLimit _ hc
  let cΓ : Cocone (D.op ⋙ Scheme.Γ) := Scheme.Γ.mapCocone c.op
  let : Algebra Γ(S, ⊤) cΓ.pt := f.appTop.hom.toAlgebra
  have : Algebra.FiniteType Γ(S, ⊤) cΓ.pt :=
    (HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFiniteType) (f := f)).mp
      inferInstance
  have {i j : I} (r : i ⟶ j) : IsAffineHom (D.map r) := inferInstance
  have (i : I) : CompactSpace (D.obj i) := inferInstance
  have (i : I) : QuasiSeparatedSpace (D.obj i) := inferInstance
  obtain ⟨i, hi⟩ := CommRingCat.exists_adjoin_range_eq_top_of_isColimit
    (D.op ⋙ Scheme.Γ) cΓ (nonempty_isColimit_Γ_mapCocone D c hc).some Γ(S, ⊤)
  let : Algebra Γ(S, ⊤) Γ(c.pt, ⊤) := f.appTop.hom.toAlgebra
  let q : c.pt ⟶ pullback (t i.unop) s :=
    pullback.lift (c.π.app i.unop) f (h i.unop)
  refine ⟨i.unop, IsClosedImmersion.of_surjective_of_isAffine q ?_⟩
  apply RingHom.surjective_of_adjoin_range_eq_top q.appTop.hom
    (pullback.snd (t i.unop) s).appTop.hom
    (pullback.fst (t i.unop) s).appTop.hom (c.π.app i.unop).appTop.hom
  · change ((pullback.snd (t i.unop) s).appTop ≫ q.appTop).hom = f.appTop.hom
    rw [← Hom.comp_appTop, pullback.lift_snd]
  · change ((pullback.fst (t i.unop) s).appTop ≫ q.appTop).hom =
      (c.π.app i.unop).appTop.hom
    rw [← Hom.comp_appTop, pullback.lift_fst]
  · exact hi

end AlgebraicGeometry.Scheme
