/-
Copyright (c) 2026 Algebraic geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Pullback.FreeComp

/-!
# Pullback of module sheaves along a commutative triangle

For morphisms of schemes `a : X ⟶ Y`, `b : Y ⟶ S` and `d : X ⟶ S` with `h : a ≫ b = d`,
`Scheme.Modules.pullbackTriangleIso a b d h : pullback b ⋙ pullback a ≅ pullback d` is Mathlib's
`pullbackComp a b` followed by `pullbackCongr h`. Its associativity is
`pullbackTriangleIso_assoc_hom`, from the associativity `pullbackComp_assoc_hom` of
`pullbackComp` (Mathlib's `Scheme.Modules.pseudofunctor_associativity`). These three declarations
were moved verbatim from `Descent/FinitePresentation/Modules/Maps.lean`, where
`pullbackComp_assoc_hom` was private.

The components satisfy (`pullbackTriangleIso_hom_app`, `pullbackTriangleIso_inv_app`, `rfl`):

- for the triangle `a ≫ b = a ≫ b` the comparison is `pullbackComp a b`
  (`pullbackTriangleIso_rfl_hom_app`, `pullbackTriangleIso_rfl_inv_app`);
- unit: for `𝟙 X ≫ b = b` it is `pullbackId` (`pullbackTriangleIso_id_hom_app`, from Mathlib's
  `Scheme.Modules.pseudofunctor_right_unitality`);
- free sheaves: it is compatible with `pullbackFreeIso` (`pullbackTriangleIso_inv_app_free`);
- three triangles over `X₁ ⟶ X₂ ⟶ X₃ ⟶ Z`: `pullback_map_pullbackTriangleIso_hom_app`.

For a module sheaf `E` on `S` and a scheme `T` over `S`, `overPullback E T = (T ⟶ S)^* E`, and a
morphism `t : T' ⟶ T` over `S` gives `overPullbackIso E t : E_{T'} ≅ t^* E_T`, a component of the
inverse of `pullbackTriangleIso`, with its unit and composition laws (`overPullbackIso_id_hom_comp`,
`overPullbackIso_comp_hom`). No hypothesis on the schemes, morphisms or modules.
-/

@[expose] public section

noncomputable section

-- The options of `Descent/FinitePresentation/Modules/Maps.lean`, the source of the moved
-- declarations.
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- Native composition through an actual commuting triangle. -/
def pullbackTriangleIso {X Y S : Scheme.{u}}
    (a : X ⟶ Y) (b : Y ⟶ S) (d : X ⟶ S) (h : a ≫ b = d) :
    pullback b ⋙ pullback a ≅ pullback d :=
  pullbackComp a b ≪≫ pullbackCongr h

/-- The associativity of Mathlib's `pullbackComp` at a module, with the comparison
`pullbackCongr` of the two bracketings. -/
theorem pullbackComp_assoc_hom
    {W X Y S : Scheme.{u}} (a : W ⟶ X) (b : X ⟶ Y) (d : Y ⟶ S)
    (M : S.Modules) :
    (pullback a).map ((pullbackComp b d).hom.app M) ≫
        (pullbackComp a (b ≫ d)).hom.app M =
      (pullbackComp a b).hom.app ((pullback d).obj M) ≫
        (pullbackComp (a ≫ b) d).hom.app M ≫
          (pullbackCongr (Category.assoc a b d)).hom.app M := by
  have H := congrArg (fun t => t.app M) (pseudofunctor_associativity a b d)
  change (pullbackComp a (b ≫ d)).inv.app M ≫
      (pullback a).map ((pullbackComp b d).inv.app M) ≫
      (pullbackComp a b).hom.app ((pullback d).obj M) ≫
      (pullbackComp (a ≫ b) d).hom.app M =
        (pullbackCongr (Category.assoc a b d)).inv.app M at H
  have H' := congrArg (fun t =>
    (pullback a).map ((pullbackComp b d).hom.app M) ≫
      (pullbackComp a (b ≫ d)).hom.app M ≫ t) H
  have H'' :
      (pullbackComp a b).hom.app ((pullback d).obj M) ≫
          (pullbackComp (a ≫ b) d).hom.app M =
        (pullback a).map ((pullbackComp b d).hom.app M) ≫
          (pullbackComp a (b ≫ d)).hom.app M ≫
            (pullbackCongr (Category.assoc a b d)).inv.app M := by
    simp only [Iso.hom_inv_id_app_assoc,
      ← Functor.map_comp_assoc, Iso.hom_inv_id_app] at H'
    simpa only [CategoryTheory.Functor.map_id, Category.id_comp] using H'
  apply (cancel_mono ((pullbackCongr (Category.assoc a b d)).inv.app M)).mp
  simpa only [Category.assoc, Iso.hom_inv_id_app, Category.comp_id] using H''.symm

/-- The actual triangle comparisons compose through native pullback associativity. -/
theorem pullbackTriangleIso_assoc_hom
    {W X Y S : Scheme.{u}} (a : X ⟶ Y) (b : W ⟶ X) (d : Y ⟶ S)
    (r : X ⟶ S) (hr : a ≫ d = r) (s : W ⟶ S) (hs : b ≫ r = s)
    (M : S.Modules) :
    (pullback b).map ((pullbackTriangleIso a d r hr).hom.app M) ≫
        (pullbackTriangleIso b r s hs).hom.app M =
      (pullbackComp b a).hom.app ((pullback d).obj M) ≫
        (pullbackTriangleIso (b ≫ a) d s
          (by rw [Category.assoc, hr, hs])).hom.app M := by
  subst r
  subst s
  simpa only [pullbackTriangleIso, Iso.trans_hom, NatTrans.comp_app,
    pullbackCongr, eqToIso_refl, Iso.refl_hom, NatTrans.id_app, Category.comp_id]
    using pullbackComp_assoc_hom b a d M

section Components

variable {X Y Z W S : Scheme.{u}}

theorem pullbackTriangleIso_hom_app (a : X ⟶ Y) (b : Y ⟶ S) (d : X ⟶ S) (h : a ≫ b = d)
    (M : S.Modules) :
    (pullbackTriangleIso a b d h).hom.app M =
      (pullbackComp a b).hom.app M ≫ (pullbackCongr h).hom.app M :=
  rfl

theorem pullbackTriangleIso_inv_app (a : X ⟶ Y) (b : Y ⟶ S) (d : X ⟶ S) (h : a ≫ b = d)
    (M : S.Modules) :
    (pullbackTriangleIso a b d h).inv.app M =
      (pullbackCongr h).inv.app M ≫ (pullbackComp a b).inv.app M :=
  rfl

/-- For the triangle `a ≫ b = a ≫ b` the comparison is `pullbackComp a b`. -/
theorem pullbackTriangleIso_rfl_hom_app (a : X ⟶ Y) (b : Y ⟶ S) (M : S.Modules) :
    (pullbackTriangleIso a b (a ≫ b) rfl).hom.app M = (pullbackComp a b).hom.app M := by
  simp [pullbackTriangleIso_hom_app, pullbackCongr]

/-- For the triangle `a ≫ b = a ≫ b` the inverse comparison is the inverse of
`pullbackComp a b`. -/
theorem pullbackTriangleIso_rfl_inv_app (a : X ⟶ Y) (b : Y ⟶ S) (M : S.Modules) :
    (pullbackTriangleIso a b (a ≫ b) rfl).inv.app M = (pullbackComp a b).inv.app M := by
  simp [pullbackTriangleIso_inv_app, pullbackCongr]

/-- Naturality of the inverse comparison, with the composite functor unfolded. -/
@[reassoc]
theorem pullbackTriangleIso_inv_app_naturality (a : X ⟶ Y) (b : Y ⟶ S) (d : X ⟶ S)
    (h : a ≫ b = d) {M N : S.Modules} (φ : M ⟶ N) :
    (pullback d).map φ ≫ (pullbackTriangleIso a b d h).inv.app N =
      (pullbackTriangleIso a b d h).inv.app M ≫ (pullback a).map ((pullback b).map φ) :=
  (pullbackTriangleIso a b d h).inv.naturality φ

/-- **Unit**: for the triangle `𝟙 X ≫ b = b` the comparison is `pullbackId`. -/
theorem pullbackTriangleIso_id_hom_app (b : X ⟶ S) (M : S.Modules) :
    (pullbackTriangleIso (𝟙 X) b b (Category.id_comp b)).hom.app M =
      (pullbackId X).hom.app ((pullback b).obj M) := by
  rw [pullbackTriangleIso_hom_app]
  apply (cancel_epi ((pullbackComp (𝟙 X) b).inv.app M)).1
  have h := congrArg (fun q => q.app M) (Scheme.Modules.pseudofunctor_right_unitality b)
  simpa [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.rightUnitor_hom_app,
    Category.assoc, pullbackCongr] using h.symm

/-- **Unit**, in the form used for the functor law along identities. -/
@[reassoc]
theorem pullbackTriangleIso_id_inv_app_comp (b : X ⟶ S) (M : S.Modules) :
    (pullbackTriangleIso (𝟙 X) b b (Category.id_comp b)).inv.app M ≫
      (pullbackId X).hom.app ((pullback b).obj M) = 𝟙 _ := by
  rw [← pullbackTriangleIso_id_hom_app, Iso.inv_hom_id_app]

/-- **Free sheaves**: the inverse comparison is compatible with the pullback isomorphisms
`pullbackFreeIso` of a free sheaf. -/
@[reassoc]
theorem pullbackTriangleIso_inv_app_free (a : X ⟶ Y) (b : Y ⟶ S) (d : X ⟶ S) (h : a ≫ b = d)
    (I : Type u) :
    (pullbackTriangleIso a b d h).inv.app (SheafOfModules.free I) ≫
        (pullback a).map (pullbackFreeIso b I).hom ≫ (pullbackFreeIso a I).hom =
      (pullbackFreeIso d I).hom := by
  subst h
  rw [pullbackTriangleIso_rfl_inv_app, ← pullbackFreeIso_comp, Iso.inv_hom_id_app_assoc]

/-- **Three triangles**: for `a ≫ g = q`, `g ≫ b = c` and `a ≫ c = d`, the pullback along `a`
of the comparison for `g ≫ b = c` in terms of the comparisons for the other triangles (from
`pullbackTriangleIso_assoc_hom`). -/
theorem pullback_map_pullbackTriangleIso_hom_app {X₁ X₂ X₃ : Scheme.{u}} (a : X₁ ⟶ X₂)
    (g : X₂ ⟶ X₃) (b : X₃ ⟶ S) {q : X₁ ⟶ X₃} (hq : a ≫ g = q) {c : X₂ ⟶ S} (hc : g ≫ b = c)
    {d : X₁ ⟶ S} (hd : a ≫ c = d) (M : S.Modules) :
    (pullback a).map ((pullbackTriangleIso g b c hc).hom.app M) =
      (pullbackTriangleIso a g q hq).hom.app ((pullback b).obj M) ≫
        (pullbackTriangleIso q b d (by rw [← hq, Category.assoc, hc, hd])).hom.app M ≫
          (pullbackTriangleIso a c d hd).inv.app M := by
  subst hq hc hd
  have H := pullbackTriangleIso_assoc_hom g a b (g ≫ b) rfl (a ≫ g ≫ b) rfl M
  rw [pullbackTriangleIso_rfl_hom_app a g, ← reassoc_of% H, Iso.hom_inv_id_app]
  exact (Category.comp_id _).symm

end Components

/-! ### Schemes over a base -/

section Over

variable {S : Scheme.{u}} (E : S.Modules)

/-- The pullback `E_T = (T ⟶ S)^* E` of a module sheaf `E` on `S` to a scheme `T` over `S`. -/
abbrev overPullback (T : Over S) : T.left.Modules :=
  (pullback T.hom).obj E

/-- For a morphism `t : T' ⟶ T` over `S`, the identification `E_{T'} ≅ t^* E_T`: a component
of the inverse of `pullbackTriangleIso`. -/
def overPullbackIso {T T' : Over S} (t : T' ⟶ T) :
    overPullback E T' ≅ (pullback t.left).obj (overPullback E T) :=
  ((pullbackTriangleIso t.left T.hom T'.hom (Over.w t)).app E).symm

theorem overPullbackIso_hom {T T' : Over S} (t : T' ⟶ T) :
    (overPullbackIso E t).hom = (pullbackTriangleIso t.left T.hom T'.hom (Over.w t)).inv.app E :=
  rfl

theorem overPullbackIso_inv {T T' : Over S} (t : T' ⟶ T) :
    (overPullbackIso E t).inv = (pullbackTriangleIso t.left T.hom T'.hom (Over.w t)).hom.app E :=
  rfl

/-- The unit law of `overPullbackIso`. -/
theorem overPullbackIso_id_hom_comp (T : Over S) :
    (overPullbackIso E (𝟙 T)).hom ≫ (pullbackId T.left).hom.app (overPullback E T) = 𝟙 _ :=
  pullbackTriangleIso_id_inv_app_comp T.hom E

/-- The composition law of `overPullbackIso`, the inverse form of
`pullbackTriangleIso_assoc_hom`. -/
@[reassoc]
theorem overPullbackIso_comp_hom {T T' T'' : Over S} (s : T'' ⟶ T') (t : T' ⟶ T) :
    (overPullbackIso E s).hom ≫ (pullback s.left).map (overPullbackIso E t).hom =
      (overPullbackIso E (s ≫ t)).hom ≫
        (pullbackComp s.left t.left).inv.app (overPullback E T) :=
  (Iso.inv_eq_inv
    ((pullback s.left).mapIso ((pullbackTriangleIso t.left T.hom T'.hom (Over.w t)).app E) ≪≫
      (pullbackTriangleIso s.left T'.hom T''.hom (Over.w s)).app E)
    ((pullbackComp s.left t.left).app ((pullback T.hom).obj E) ≪≫
      (pullbackTriangleIso (s.left ≫ t.left) T.hom T''.hom
        (by rw [Category.assoc, Over.w t, Over.w s])).app E)).mpr
    (pullbackTriangleIso_assoc_hom t.left s.left T.hom T'.hom (Over.w t) T''.hom (Over.w s) E)

end Over

end AlgebraicGeometry.Scheme.Modules
