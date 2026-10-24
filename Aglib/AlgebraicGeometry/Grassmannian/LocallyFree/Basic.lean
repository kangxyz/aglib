/-
Copyright (c) 2026 Algebraic geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Pullback.Triangle
public import Aglib.AlgebraicGeometry.Grassmannian.Quotient.Basic

/-!
# The functor `Quot_k(E)` of rank-`k` locally free quotients of a module sheaf

For a scheme `X`, a module sheaf `F` on `X` and `k : ℕ`, a `LocallyFreeQuotientOf F k` is an
epimorphism `π : F ⟶ Q` of module sheaves with `Q` finite locally free of constant rank `k`
(`Scheme.Modules.SheafHasRank Q k`). This is F8's `LocallyFreeQuotient X k n` with the source
`O_X^n` replaced by an arbitrary `F`; for `F = O_X^n` the two structures have the same data
(`LocallyFreeQuotientOf.toLocallyFreeQuotient`, `LocallyFreeQuotientOf.ofLocallyFreeQuotient`).
Isomorphisms under `F` (`LocallyFreeQuotientOf.IsoUnder`) are unique. A quotient pulls back along
every morphism `f` to a quotient of `f^* F` (`LocallyFreeQuotientOf.pullback`, with quotient map
`f^* π`), and precomposes with every epimorphism `F' ⟶ F` (`LocallyFreeQuotientOf.precomp`).

For a scheme `S`, a module sheaf `E` on `S` and a scheme `T` over `S`, write
`E_T = Scheme.Modules.overPullback E T = (T ⟶ S)^* E`. A morphism `t : T' ⟶ T` over `S` identifies
`E_{T'} ≅ t^* E_T` (`Scheme.Modules.overPullbackIso`, a component of the inverse of
`Scheme.Modules.pullbackTriangleIso`), and a quotient of `E_T` pulls back to the quotient
`E_{T'} ≅ t^* E_T ⟶ t^* Q` of `E_{T'}` (`LocallyFreeQuotientOf.pullbackOver`).
The isomorphism classes form the functor
`Grassmannian.quotBundleFunctor E k : (Over S)ᵒᵖ ⥤ Type (u + 1)`, `Quot_k(E)`.

Sources: the functor is Nitsure, *Construction of Hilbert and Quot schemes*,
arXiv:math/0504590v1, §1, Elementary Examples, Exercises (2), pp. 5–6 (the rank-`d` relative
Grassmannian `Grass(E, d) = Quot^d_{E/S/S}` of a locally free `E`, by quotients of rank `d`); for
`E = O^n` it is Stacks' `G(n − k, n)` (Tag 089S, eq. (27.22.0.1)); for `k = 1` and quasi-coherent
`E` it is the functor of points of `P(E)` in Stacks, Section 27.21 (Tag 01OA), after
Definition 27.21.1 (Tag 01OB). Encoded subset:
an arbitrary module sheaf `E` on an arbitrary scheme `S`, schemes over `S`, all `k`. Convention:
`k` is the rank of the quotient. No premise.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory Opposite Limits

namespace AlgebraicGeometry

namespace Grassmannian

open Scheme.Modules

/-- A rank-`k` locally free quotient of a module sheaf `F`: an epimorphism `π : F ⟶ Q` with `Q`
finite locally free of constant rank `k`. -/
structure LocallyFreeQuotientOf {X : Scheme.{u}} (F : X.Modules) (k : ℕ) : Type (u + 1) where
  /-- The quotient sheaf. -/
  obj : X.Modules
  /-- The quotient map. -/
  π : F ⟶ obj
  epi_π : Epi π
  /-- The quotient is finite locally free of constant rank `k`. -/
  hasRank : SheafHasRank obj k

attribute [instance] LocallyFreeQuotientOf.epi_π

namespace LocallyFreeQuotientOf

variable {X Y Z : Scheme.{u}} {F F' F'' : X.Modules} {k : ℕ}

/-- An isomorphism of quotients under `F`: an isomorphism `e` of the quotient sheaves with
`π ≫ e.hom = π'`. -/
structure IsoUnder (P Q : LocallyFreeQuotientOf F k) : Type u where
  /-- The isomorphism of quotient sheaves. -/
  iso : P.obj ≅ Q.obj
  comm : P.π ≫ iso.hom = Q.π

/-- The identity isomorphism of a quotient. -/
def IsoUnder.refl (P : LocallyFreeQuotientOf F k) : IsoUnder P P where
  iso := CategoryTheory.Iso.refl _
  comm := Category.comp_id _

/-- The inverse of an isomorphism of quotients. -/
def IsoUnder.symm {P Q : LocallyFreeQuotientOf F k} (e : IsoUnder P Q) : IsoUnder Q P where
  iso := e.iso.symm
  comm := by rw [← e.comm, Category.assoc, CategoryTheory.Iso.symm_hom,
    CategoryTheory.Iso.hom_inv_id, Category.comp_id]

/-- The composite of isomorphisms of quotients. -/
def IsoUnder.trans {P Q R : LocallyFreeQuotientOf F k} (e : IsoUnder P Q) (e' : IsoUnder Q R) :
    IsoUnder P R where
  iso := e.iso ≪≫ e'.iso
  comm := by rw [CategoryTheory.Iso.trans_hom, ← Category.assoc, e.comm, e'.comm]

/-- An isomorphism of quotients is unique: the quotient maps are epimorphisms. -/
theorem IsoUnder.ext' {P Q : LocallyFreeQuotientOf F k} (e e' : IsoUnder P Q) : e = e' := by
  have : e.iso.hom = e'.iso.hom := (cancel_epi P.π).mp (e.comm.trans e'.comm.symm)
  cases e
  cases e'
  congr
  exact CategoryTheory.Iso.ext this

/-- Isomorphism of quotients under `F`. -/
instance setoid (F : X.Modules) (k : ℕ) : Setoid (LocallyFreeQuotientOf F k) where
  r P Q := Nonempty (IsoUnder P Q)
  iseqv := ⟨fun P ↦ ⟨IsoUnder.refl P⟩, fun ⟨e⟩ ↦ ⟨e.symm⟩, fun ⟨e⟩ ⟨e'⟩ ↦ ⟨e.trans e'⟩⟩

/-- The pullback of a quotient `π : F ⟶ Q` along `f : Y ⟶ X`: the quotient `f^* π` of `f^* F`. -/
def pullback (f : Y ⟶ X) (P : LocallyFreeQuotientOf F k) :
    LocallyFreeQuotientOf ((Scheme.Modules.pullback f).obj F) k where
  obj := (Scheme.Modules.pullback f).obj P.obj
  π := (Scheme.Modules.pullback f).map P.π
  epi_π := inferInstance
  hasRank := sheafHasRank_pullback f P.hasRank

theorem pullback_obj (f : Y ⟶ X) (P : LocallyFreeQuotientOf F k) :
    (P.pullback f).obj = (Scheme.Modules.pullback f).obj P.obj := rfl

theorem pullback_π (f : Y ⟶ X) (P : LocallyFreeQuotientOf F k) :
    (P.pullback f).π = (Scheme.Modules.pullback f).map P.π := rfl

/-- The precomposition of a quotient of `F` with an epimorphism `α : F' ⟶ F`. -/
def precomp (α : F' ⟶ F) [Epi α] (P : LocallyFreeQuotientOf F k) :
    LocallyFreeQuotientOf F' k where
  obj := P.obj
  π := α ≫ P.π
  epi_π := epi_comp _ _
  hasRank := P.hasRank

theorem precomp_obj (α : F' ⟶ F) [Epi α] (P : LocallyFreeQuotientOf F k) :
    (P.precomp α).obj = P.obj := rfl

theorem precomp_π (α : F' ⟶ F) [Epi α] (P : LocallyFreeQuotientOf F k) :
    (P.precomp α).π = α ≫ P.π := rfl

/-- Pullback of an isomorphism of quotients. -/
def IsoUnder.pullback (f : Y ⟶ X) {P Q : LocallyFreeQuotientOf F k} (e : IsoUnder P Q) :
    IsoUnder (P.pullback f) (Q.pullback f) where
  iso := (Scheme.Modules.pullback f).mapIso e.iso
  comm := by
    simp only [LocallyFreeQuotientOf.pullback, Functor.mapIso_hom,
      ← CategoryTheory.Functor.map_comp, e.comm]

/-- Precomposition of an isomorphism of quotients. -/
def IsoUnder.precomp (α : F' ⟶ F) [Epi α] {P Q : LocallyFreeQuotientOf F k} (e : IsoUnder P Q) :
    IsoUnder (P.precomp α) (Q.precomp α) where
  iso := e.iso
  comm := by rw [precomp_π, precomp_π, Category.assoc, e.comm]

/-- Precomposition with a precomposed quotient (an isomorphism with identity underlying map). -/
def precompPrecompIso (β : F'' ⟶ F') (α : F' ⟶ F) [Epi β] [Epi α]
    (P : LocallyFreeQuotientOf F k) :
    IsoUnder ((P.precomp α).precomp β) (P.precomp (β ≫ α)) where
  iso := CategoryTheory.Iso.refl _
  comm := by
    rw [precomp_π, precomp_π, precomp_π, CategoryTheory.Iso.refl_hom, Category.comp_id,
      Category.assoc]

/-- A precomposition with an inverse pair of isomorphisms is the original quotient. -/
def precompHomInvIso (α : F' ≅ F) (P : LocallyFreeQuotientOf F k) :
    IsoUnder ((P.precomp α.hom).precomp α.inv) P where
  iso := CategoryTheory.Iso.refl _
  comm := by
    rw [precomp_π, precomp_π, CategoryTheory.Iso.refl_hom, Category.comp_id,
      CategoryTheory.Iso.inv_hom_id_assoc]

/-- A precomposition with an inverse pair of isomorphisms is the original quotient. -/
def precompInvHomIso (α : F ≅ F') (P : LocallyFreeQuotientOf F k) :
    IsoUnder ((P.precomp α.inv).precomp α.hom) P where
  iso := CategoryTheory.Iso.refl _
  comm := by
    rw [precomp_π, precomp_π, CategoryTheory.Iso.refl_hom, Category.comp_id,
      CategoryTheory.Iso.hom_inv_id_assoc]

end LocallyFreeQuotientOf

open LocallyFreeQuotientOf

/-! ### Quotients of the free sheaf -/

section Free

variable {X : Scheme.{u}} {k n : ℕ}

/-- A quotient of `O_X^n` in the general structure is F8's `LocallyFreeQuotient` (same data). -/
def LocallyFreeQuotientOf.toLocallyFreeQuotient (P : LocallyFreeQuotientOf (freeSheaf X n) k) :
    LocallyFreeQuotient X k n :=
  ⟨P.obj, P.π, P.epi_π, P.hasRank⟩

/-- F8's `LocallyFreeQuotient` as a quotient of `O_X^n` in the general structure (same data). -/
def LocallyFreeQuotientOf.ofLocallyFreeQuotient (P : LocallyFreeQuotient X k n) :
    LocallyFreeQuotientOf (freeSheaf X n) k :=
  ⟨P.obj, P.π, P.epi_π, P.hasRank⟩

end Free

/-! ### The functor on schemes over `S` -/

variable {S : Scheme.{u}} (E : S.Modules) (k : ℕ)

variable {E k}

/-- The pullback of a quotient of `E_T` along a morphism `t : T' ⟶ T` over `S`: the quotient
`E_{T'} ≅ t^* E_T ⟶ t^* Q` of `E_{T'}`. -/
def LocallyFreeQuotientOf.pullbackOver {T T' : Over S} (t : T' ⟶ T)
    (P : LocallyFreeQuotientOf (overPullback E T) k) :
    LocallyFreeQuotientOf (overPullback E T') k :=
  (P.pullback t.left).precomp (overPullbackIso E t).hom

theorem LocallyFreeQuotientOf.pullbackOver_obj {T T' : Over S} (t : T' ⟶ T)
    (P : LocallyFreeQuotientOf (overPullback E T) k) :
    (P.pullbackOver t).obj = (Scheme.Modules.pullback t.left).obj P.obj := rfl

theorem LocallyFreeQuotientOf.pullbackOver_π {T T' : Over S} (t : T' ⟶ T)
    (P : LocallyFreeQuotientOf (overPullback E T) k) :
    (P.pullbackOver t).π =
      (overPullbackIso E t).hom ≫ (Scheme.Modules.pullback t.left).map P.π := rfl

/-- Pullback over `S` of an isomorphism of quotients. -/
def LocallyFreeQuotientOf.IsoUnder.pullbackOver {T T' : Over S} (t : T' ⟶ T)
    {P Q : LocallyFreeQuotientOf (overPullback E T) k} (e : IsoUnder P Q) :
    IsoUnder (P.pullbackOver t) (Q.pullbackOver t) :=
  IsoUnder.precomp (overPullbackIso E t).hom (e.pullback t.left)

/-- Pullback over `S` along the identity. -/
def LocallyFreeQuotientOf.pullbackOverIdIso {T : Over S}
    (P : LocallyFreeQuotientOf (overPullback E T) k) :
    IsoUnder (P.pullbackOver (𝟙 T)) P where
  iso := (pullbackId T.left).app P.obj
  comm := by
    have h := (pullbackId T.left).hom.naturality P.π
    dsimp only [Functor.id_map] at h
    change ((overPullbackIso E (𝟙 T)).hom ≫ (Scheme.Modules.pullback (𝟙 T.left)).map P.π) ≫
      (pullbackId T.left).hom.app P.obj = P.π
    rw [Category.assoc, h, ← Category.assoc, overPullbackIso_id_hom_comp, Category.id_comp]

/-- Pullback over `S` along a composite. -/
def LocallyFreeQuotientOf.pullbackOverCompIso {T T' T'' : Over S} (s : T'' ⟶ T') (t : T' ⟶ T)
    (P : LocallyFreeQuotientOf (overPullback E T) k) :
    IsoUnder (P.pullbackOver (s ≫ t)) ((P.pullbackOver t).pullbackOver s) where
  iso := ((pullbackComp s.left t.left).app P.obj).symm
  comm := by
    have h := (pullbackComp s.left t.left).inv.naturality P.π
    dsimp only [Functor.comp_map] at h
    change ((overPullbackIso E (s ≫ t)).hom ≫
        (Scheme.Modules.pullback (s.left ≫ t.left)).map P.π) ≫
          (pullbackComp s.left t.left).inv.app P.obj =
      (overPullbackIso E s).hom ≫ (Scheme.Modules.pullback s.left).map
        ((overPullbackIso E t).hom ≫ (Scheme.Modules.pullback t.left).map P.π)
    rw [Category.assoc, h, CategoryTheory.Functor.map_comp, overPullbackIso_comp_hom_assoc]

variable (E k)

/-- **The functor `Quot_k(E)`** on schemes over `S`: `T` goes to the isomorphism classes of
epimorphisms `E_T ⟶ Q` with `Q` finite locally free of constant rank `k`, where
`E_T = (T ⟶ S)^* E`, with pullback as maps.

Sources: Nitsure, arXiv:math/0504590v1, §1, Elementary Examples, Exercises (2), pp. 5–6
(`Grass(E, d) = Quot^d_{E/S/S}`); for `E = O^n`, Stacks' `G(n − k, n)` (Tag 089S,
eq. (27.22.0.1)); for `k = 1` and quasi-coherent `E`, Stacks, Section 27.21 (Tag 01OA, after
Definition 27.21.1, Tag 01OB). Encoded subset: an
arbitrary module sheaf `E` on an arbitrary scheme `S`, all `k`; convention: `k` is the rank of the
quotient. No premise. -/
def quotBundleFunctor : (Over S)ᵒᵖ ⥤ Type (u + 1) where
  obj T := Quotient (LocallyFreeQuotientOf.setoid (overPullback E T.unop) k)
  map {T T'} t := TypeCat.ofHom (Quotient.map (LocallyFreeQuotientOf.pullbackOver t.unop)
    (fun _ _ ⟨e⟩ ↦ ⟨e.pullbackOver t.unop⟩))
  map_id T := by
    ext x
    induction x using Quotient.inductionOn with | h P =>
    exact Quotient.sound ⟨LocallyFreeQuotientOf.pullbackOverIdIso P⟩
  map_comp {T T' T''} t t' := by
    ext x
    induction x using Quotient.inductionOn with | h P =>
    exact Quotient.sound ⟨LocallyFreeQuotientOf.pullbackOverCompIso t'.unop t.unop P⟩

theorem quotBundleFunctor_obj (T : (Over S)ᵒᵖ) :
    (quotBundleFunctor E k).obj T =
      Quotient (LocallyFreeQuotientOf.setoid (overPullback E T.unop) k) := rfl

variable {E k}

theorem quotBundleFunctor_map_mk {T T' : (Over S)ᵒᵖ} (t : T ⟶ T')
    (P : LocallyFreeQuotientOf (overPullback E T.unop) k) :
    (quotBundleFunctor E k).map t (Quotient.mk _ P) = Quotient.mk _ (P.pullbackOver t.unop) := rfl

end Grassmannian

end AlgebraicGeometry
