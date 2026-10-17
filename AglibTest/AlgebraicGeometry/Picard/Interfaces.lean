/-
Copyright (c) 2026 Algebraic geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.Grp.Limits
public import Aglib.AlgebraicGeometry.Modules.Invertible.Dual
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Pullback
public import Mathlib.AlgebraicGeometry.Sites.Representability
public import Mathlib.CategoryTheory.Comma.Presheaf.Basic

/-! Interface probes for the Picard functor layer (milestone M0 of `doc/PICARD_PLAN.md`).
Mathlib's plus-plus sheafification applies to the fppf topology induced on `Over S`
with values in `Type (u + 1)` and in `AddCommGrpCat.{u + 1}`; `Functor.RepresentableBy`
accepts `Type (u + 1)`-valued presheaves on `Over S`; the Aglib Picard group of a
scheme in `Scheme.{u}` lives in `Type (u + 1)`; and Aglib's
`Scheme.Modules.quasicoherent_pullback` makes geometric pullback preserve
quasicoherence along every scheme morphism. Mathlib's Zariski-local representability is
stated for `Type u`-valued Zariski sheaves on all schemes; presheaves over `yoneda.obj S`
are presheaves on `CostructuredArrow yoneda (yoneda.obj S)`, the first step of an `Over S`
adapter. -/

@[expose] public section

noncomputable section
open CategoryTheory AlgebraicGeometry

universe u

example (S : Scheme.{u}) : HasSheafify (Scheme.fppfTopology.over S) (Type (u + 1)) :=
  inferInstance

example (S : Scheme.{u}) : HasSheafify (Scheme.fppfTopology.over S) AddCommGrpCat.{u + 1} :=
  inferInstance

example (S : Scheme.{u}) (F : (Over S)ᵒᵖ ⥤ Type (u + 1)) (P : Over S) : Type (u + 1) :=
  F.RepresentableBy P

example (X : Scheme.{u}) : Type (u + 1) := Scheme.Modules.Invertible.PicardGroup X

example {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Y.Modules) [M.IsQuasicoherent] :
    ((Scheme.Modules.pullback f).obj M).IsQuasicoherent :=
  Scheme.Modules.quasicoherent_pullback f M

example (F : Sheaf Scheme.zariskiTopology.{u} (Type u)) {ι : Type u} {X : ι → Scheme.{u}}
    (f : ∀ i, yoneda.obj (X i) ⟶ F.obj) (hf : ∀ i, IsOpenImmersion.presheaf (f i))
    [Presheaf.IsLocallySurjective Scheme.zariskiTopology (Limits.Sigma.desc f)] :
    F.obj.IsRepresentable :=
  Scheme.LocalRepresentability.isRepresentable hf

example (S : Scheme.{u}) :
    Over (yoneda.obj S) ≌ ((CostructuredArrow yoneda (yoneda.obj S))ᵒᵖ ⥤ Type u) :=
  overEquivPresheafCostructuredArrow (yoneda.obj S)
