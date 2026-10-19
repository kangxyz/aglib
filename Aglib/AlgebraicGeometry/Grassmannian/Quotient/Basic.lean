/-
Copyright (c) 2026 Algebraic geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Pullback.FreeComp
public import Aglib.AlgebraicGeometry.Modules.FittingIdeal.ConstantRank

/-!
# Rank-`k` locally free quotients of `O_X^n`

For a scheme `X` and natural numbers `k n`, a `LocallyFreeQuotient X k n` is an epimorphism
`π : O_X^n ⟶ Q` of module sheaves, where `O_X^n` is the free sheaf
`SheafOfModules.free (ULift (Fin n))` and `Q` is finite locally free of constant rank `k`
(`Scheme.Modules.SheafHasRank Q k`). Two quotients are isomorphic if there is an isomorphism
`e : Q ≅ Q'` with `π ≫ e.hom = π'` (`LocallyFreeQuotient.IsoUnder`; such an isomorphism is unique).
Quotients pull back along every morphism of schemes, through Mathlib's `pullbackObjFreeIso`
(`LocallyFreeQuotient.pullback`).

The isomorphism classes form the quotient functor `quotSchemeFunctor k n : Scheme.{u}ᵒᵖ ⥤
Type (u + 1)` and its restriction `quotFunctor R k n` to schemes over `Spec R`, the functor
`Quot_k(O^n)` that the Grassmannian represents (`Grassmannian.quotFunctorRepresentableBy`).

Sources: Stacks, Tag 089S (eq. (27.22.0.1), the functor) and Tag 089T (Lemma 27.22.1), TeX
snapshot `a04446e5`; Nitsure, *Construction of Hilbert and Quot schemes*, arXiv:math/0504590v1,
§1, Elementary Examples, Exercises (2) "Grassmannian as a Quot scheme", p. 5, with the
construction on pp. 7–8 and the universal quotient on p. 9. Encoded subset:
`O^n = SheafOfModules.free (ULift (Fin n))` on schemes over `Spec R` (and on all schemes for
`quotSchemeFunctor`), all `k` and `n` (Stacks assumes `0 < k < n`). Convention: `k` is the rank
of the quotient, so this is Stacks' `G(n − k, n)` and Nitsure's `Grass(n, k)`. The functor itself
needs no premise; its comparison with the Grassmannian assumes `BaseChangeMkQFormula`, supplied by
`Aglib.RingTheory.Grassmannian.BaseChangeFormula`.

## Main results

- `Grassmannian.LocallyFreeQuotient`, its isomorphisms `LocallyFreeQuotient.IsoUnder` and its
  pullback.
- `Grassmannian.quotSchemeFunctor k n` and `Grassmannian.quotFunctor R k n`.

The coherence of `pullbackFreeIso` used for the functor laws is in
`Aglib.AlgebraicGeometry.Modules.Pullback.FreeComp`; stability of constant rank under pullback,
`Scheme.Modules.sheafHasRank_pullback`, is in
`Aglib.AlgebraicGeometry.Modules.FittingIdeal.ConstantRank`.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory Opposite Limits

namespace AlgebraicGeometry

namespace Grassmannian

open Scheme.Modules

/-- The free module sheaf `O_X^n` with basis `ULift (Fin n)`. -/
abbrev freeSheaf (X : Scheme.{u}) (n : ℕ) : X.Modules :=
  SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin n))

/-- A rank-`k` locally free quotient of `O_X^n`: an epimorphism `π : O_X^n ⟶ Q` with `Q` finite
locally free of constant rank `k`. -/
structure LocallyFreeQuotient (X : Scheme.{u}) (k n : ℕ) : Type (u + 1) where
  /-- The quotient sheaf. -/
  obj : X.Modules
  /-- The quotient map. -/
  π : freeSheaf X n ⟶ obj
  epi_π : Epi π
  /-- The quotient is finite locally free of constant rank `k`. -/
  hasRank : SheafHasRank obj k

attribute [instance] LocallyFreeQuotient.epi_π

namespace LocallyFreeQuotient

variable {X Y Z : Scheme.{u}} {k n : ℕ}

/-- An isomorphism of quotients under `O_X^n`: an isomorphism `e` of the quotient sheaves with
`π ≫ e.hom = π'`. (Named so as not to shadow `CategoryTheory.Iso`.) -/
structure IsoUnder (P Q : LocallyFreeQuotient X k n) : Type u where
  /-- The isomorphism of quotient sheaves. -/
  iso : P.obj ≅ Q.obj
  comm : P.π ≫ iso.hom = Q.π

/-- The identity isomorphism of a quotient. -/
def IsoUnder.refl (P : LocallyFreeQuotient X k n) : IsoUnder P P where
  iso := CategoryTheory.Iso.refl _
  comm := Category.comp_id _

/-- The inverse of an isomorphism of quotients. -/
def IsoUnder.symm {P Q : LocallyFreeQuotient X k n} (e : IsoUnder P Q) : IsoUnder Q P where
  iso := e.iso.symm
  comm := by rw [← e.comm, Category.assoc, CategoryTheory.Iso.symm_hom,
    CategoryTheory.Iso.hom_inv_id, Category.comp_id]

/-- The composite of isomorphisms of quotients. -/
def IsoUnder.trans {P Q R : LocallyFreeQuotient X k n} (e : IsoUnder P Q) (e' : IsoUnder Q R) :
    IsoUnder P R where
  iso := e.iso ≪≫ e'.iso
  comm := by rw [CategoryTheory.Iso.trans_hom, ← Category.assoc, e.comm, e'.comm]

/-- An isomorphism of quotients is unique: the quotient maps are epimorphisms. -/
theorem IsoUnder.ext' {P Q : LocallyFreeQuotient X k n} (e e' : IsoUnder P Q) : e = e' := by
  have : e.iso.hom = e'.iso.hom := (cancel_epi P.π).mp (e.comm.trans e'.comm.symm)
  cases e
  cases e'
  congr
  exact CategoryTheory.Iso.ext this

/-- Isomorphism of quotients. -/
instance setoid (X : Scheme.{u}) (k n : ℕ) : Setoid (LocallyFreeQuotient X k n) where
  r P Q := Nonempty (IsoUnder P Q)
  iseqv := ⟨fun P ↦ ⟨IsoUnder.refl P⟩, fun ⟨e⟩ ↦ ⟨e.symm⟩, fun ⟨e⟩ ⟨e'⟩ ↦ ⟨e.trans e'⟩⟩

/-- The pullback of a quotient along a morphism of schemes `f : X ⟶ Y`:
`O_X^n ≅ f^* O_Y^n ⟶ f^* Q`. -/
def pullback (f : X ⟶ Y) (P : LocallyFreeQuotient Y k n) : LocallyFreeQuotient X k n where
  obj := (Scheme.Modules.pullback f).obj P.obj
  π := (pullbackFreeIso f (ULift.{u} (Fin n))).inv ≫ (Scheme.Modules.pullback f).map P.π
  epi_π := epi_comp _ _
  hasRank := sheafHasRank_pullback f P.hasRank

theorem pullback_obj (f : X ⟶ Y) (P : LocallyFreeQuotient Y k n) :
    (pullback f P).obj = (Scheme.Modules.pullback f).obj P.obj := rfl

theorem pullback_π (f : X ⟶ Y) (P : LocallyFreeQuotient Y k n) :
    (pullback f P).π =
      (pullbackFreeIso f (ULift.{u} (Fin n))).inv ≫ (Scheme.Modules.pullback f).map P.π := rfl

/-- Pullback of an isomorphism of quotients. -/
def IsoUnder.pullback (f : X ⟶ Y) {P Q : LocallyFreeQuotient Y k n} (e : IsoUnder P Q) :
    IsoUnder (P.pullback f) (Q.pullback f) where
  iso := (Scheme.Modules.pullback f).mapIso e.iso
  comm := by
    simp only [LocallyFreeQuotient.pullback, Functor.mapIso_hom, Category.assoc,
      ← CategoryTheory.Functor.map_comp, e.comm]

/-- Pullback along the identity. -/
def pullbackIdIso (P : LocallyFreeQuotient X k n) : IsoUnder (P.pullback (𝟙 X)) P where
  iso := (pullbackId X).app P.obj
  comm := by
    have h := (pullbackId X).hom.naturality P.π
    dsimp only [Functor.id_map] at h
    simp only [LocallyFreeQuotient.pullback, CategoryTheory.Iso.app_hom, Category.assoc]
    rw [h, ← Category.assoc, pullbackFreeIso_id, CategoryTheory.Iso.inv_hom_id,
      Category.id_comp]

/-- Pullback along a composite. -/
def pullbackCompIso (f : X ⟶ Y) (g : Y ⟶ Z) (P : LocallyFreeQuotient Z k n) :
    IsoUnder ((P.pullback g).pullback f) (P.pullback (f ≫ g)) where
  iso := (pullbackComp f g).app P.obj
  comm := by
    have h := (pullbackComp f g).hom.naturality P.π
    dsimp only [Functor.comp_map] at h
    have hc := pullbackFreeIso_comp f g (ULift.{u} (Fin n))
    have hc' : (pullbackFreeIso f (ULift.{u} (Fin n))).inv ≫
        (Scheme.Modules.pullback f).map (pullbackFreeIso g (ULift.{u} (Fin n))).inv ≫
          (pullbackComp f g).hom.app (freeSheaf Z n) =
        (pullbackFreeIso (f ≫ g) (ULift.{u} (Fin n))).inv := by
      rw [← cancel_mono (pullbackFreeIso (f ≫ g) (ULift.{u} (Fin n))).hom, Category.assoc,
        Category.assoc, hc, ← CategoryTheory.Functor.map_comp_assoc, CategoryTheory.Iso.inv_hom_id,
        CategoryTheory.Functor.map_id, Category.id_comp, CategoryTheory.Iso.inv_hom_id,
        CategoryTheory.Iso.inv_hom_id]
    simp only [LocallyFreeQuotient.pullback, CategoryTheory.Iso.app_hom, Category.assoc,
      CategoryTheory.Functor.map_comp]
    rw [h, ← hc']
    simp only [Category.assoc]

/-- Pullback along equal morphisms. -/
def pullbackCongrIso {f g : X ⟶ Y} (h : f = g) (P : LocallyFreeQuotient Y k n) :
    IsoUnder (P.pullback f) (P.pullback g) where
  iso := (pullbackCongr h).app P.obj
  comm := by
    subst h
    simp [pullbackCongr, LocallyFreeQuotient.pullback]

end LocallyFreeQuotient

open LocallyFreeQuotient

variable (k n : ℕ)

/-- The functor `Quot_k(O^n)` on all schemes: `X` goes to the isomorphism classes of rank-`k`
locally free quotients of `O_X^n`, with pullback as maps. -/
def quotSchemeFunctor : Scheme.{u}ᵒᵖ ⥤ Type (u + 1) where
  obj X := Quotient (LocallyFreeQuotient.setoid X.unop k n)
  map {X Y} f := TypeCat.ofHom (Quotient.map (LocallyFreeQuotient.pullback f.unop)
    (fun _ _ ⟨e⟩ ↦ ⟨e.pullback f.unop⟩))
  map_id X := by
    ext x
    induction x using Quotient.inductionOn with | h P =>
    exact Quotient.sound ⟨pullbackIdIso P⟩
  map_comp {X Y Z} f g := by
    ext x
    induction x using Quotient.inductionOn with | h P =>
    exact Quotient.sound ⟨(pullbackCompIso g.unop f.unop P).symm⟩

theorem quotSchemeFunctor_map_mk {X Y : Scheme.{u}ᵒᵖ} (f : X ⟶ Y)
    (P : LocallyFreeQuotient X.unop k n) :
    (quotSchemeFunctor k n).map f (Quotient.mk _ P) = Quotient.mk _ (P.pullback f.unop) := rfl

/-- **The functor `Quot_k(O^n)` on schemes over `Spec R`**: `T` goes to the isomorphism classes
of epimorphisms `O_T^n ⟶ Q` with `Q` finite locally free of constant rank `k`, with pullback as
maps.

Sources: Stacks, Tag 089S (eq. (27.22.0.1)), TeX snapshot `a04446e5`; Nitsure,
arXiv:math/0504590v1, §1, Elementary Examples, Exercises (2) "Grassmannian as a Quot scheme",
p. 5. Encoded subset: `O^n = SheafOfModules.free (ULift (Fin n))` on schemes over `Spec R`, all `k`
and `n` (Stacks assumes `0 < k < n`). Convention: `k` is the rank of the quotient, so this is
Stacks' `G(n − k, n)` and Nitsure's `Grass(n, k)`. No premise; the comparison with the
Grassmannian (`quotFunctorIso`) assumes `BaseChangeMkQFormula`, supplied by
`Aglib.RingTheory.Grassmannian.BaseChangeFormula`. -/
def quotFunctor (R : CommRingCat.{u}) (k n : ℕ) : (Over (Spec R))ᵒᵖ ⥤ Type (u + 1) :=
  (Over.forget (Spec R)).op ⋙ quotSchemeFunctor k n

theorem quotFunctor_obj (R : CommRingCat.{u}) (k n : ℕ) (T : (Over (Spec R))ᵒᵖ) :
    (quotFunctor R k n).obj T = Quotient (LocallyFreeQuotient.setoid T.unop.left k n) := rfl

theorem quotFunctor_map_mk {R : CommRingCat.{u}} {k n : ℕ} {T T' : (Over (Spec R))ᵒᵖ}
    (t : T ⟶ T') (P : LocallyFreeQuotient T.unop.left k n) :
    (quotFunctor R k n).map t (Quotient.mk _ P) = Quotient.mk _ (P.pullback t.unop.left) := rfl

end Grassmannian

end AlgebraicGeometry
