/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.InternalHom.PresheafSource
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal

/-!
# The tensor–Hom bijection for module presheaves

For module presheaves `P` and `Q` on a scheme `X`, with Mathlib's pointwise tensor product
`P ⊗ Q` of `PresheafOfModulesOfCommRing X.sheaf.obj`, and a module sheaf `N`, morphisms of
module presheaves `P ⊗ Q ⟶ N` correspond bijectively to morphisms `Q ⟶ Hom(P, N)` into the
presheaf-source Hom sheaf `InternalHom.PresheafSource.sheaf X P N`
(`InternalHom.PresheafSource.tensorHomEquiv`). A local section `q` of `Q` is sent to the
Hom-sheaf section `p ↦ h (p ⊗ q)`; conversely `p ⊗ q` is sent to the value at `p` of the
section attached to `q`. The bijection is natural in `Q`
(`InternalHom.PresheafSource.tensorHomEquiv_whiskerLeft_comp`). No sheafification occurs
and no hypothesis is imposed on `P` or `Q`.

The constructions and their equations set `backward.isDefEq.respectTransparency false`
locally. Their terms mix the coefficient rings `X.sheaf.obj ⋙ forget₂ CommRingCat RingCat` (of
the tensor factors), `X.ringCatSheaf.obj` (of module sheaves) and `Γ(X, V)` (of the Hom sheaf),
which agree only after unfolding the semireducible `sheafCompose` and `SheafedSpace.sheaf`.
Restriction maps of the tensor factors are written `PresheafOfModules.map`, the spelling of the
Mathlib lemmas applied to them, and the steps are closed by `exact` rather than `rw`.
-/

@[expose] public section

noncomputable section
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace MonoidalCategory
namespace AlgebraicGeometry.Scheme.Modules.InternalHom.PresheafSource
universe u
variable (X : Scheme.{u}) (P Q : PresheafOfModulesOfCommRing.{u} X.sheaf.obj)
  (N : SheafOfModules.{u} X.ringCatSheaf)

set_option backward.isDefEq.respectTransparency false in
/-- Currying a tensor arrow on sections: a local section `q` of `Q` over `U` gives the
Hom-sheaf section `p ↦ h (p ⊗ q)` on the opens below `U`. -/
def currySection (h : P ⊗ Q ⟶ N.val) (U : X.Opensᵒᵖ) (q : Q.obj U) :
    (sheaf X P N).val.obj U :=
  ⟨{
    app V := AddCommGrpCat.ofHom {
      toFun p := h.app (op V.unop.left) (p ⊗ₜ PresheafOfModules.map Q V.unop.hom.op q)
      map_zero' := by simp
      map_add' p p' := by simp [TensorProduct.add_tmul] }
    naturality {V W} i := by
      ext p
      change h.app (op W.unop.left) (PresheafOfModules.map P i.unop.left.op p ⊗ₜ
          PresheafOfModules.map Q W.unop.hom.op q) =
        N.val.map i.unop.left.op
          (h.app (op V.unop.left) (p ⊗ₜ PresheafOfModules.map Q V.unop.hom.op q))
      refine Eq.trans ?_ (PresheafOfModules.naturality_apply h i.unop.left.op
        (p ⊗ₜ PresheafOfModules.map Q V.unop.hom.op q))
      refine congrArg (h.app (op W.unop.left)) ?_
      change _ = PresheafOfModules.map P i.unop.left.op p ⊗ₜ
        PresheafOfModules.map Q i.unop.left.op (PresheafOfModules.map Q V.unop.hom.op q)
      have hQ : (PresheafOfModules.map Q W.unop.hom.op q : Q.obj (op W.unop.left)) =
          PresheafOfModules.map Q i.unop.left.op (PresheafOfModules.map Q V.unop.hom.op q) :=
        PresheafOfModules.map_comp_apply Q V.unop.hom.op i.unop.left.op q
      exact congrArg (fun y : Q.obj (op W.unop.left) =>
        (PresheafOfModules.map P i.unop.left.op p ⊗ₜ y : (P ⊗ Q).obj (op W.unop.left))) hQ
  }, by
    intro V r p
    change h.app (op V.unop.left) ((r • p) ⊗ₜ PresheafOfModules.map Q V.unop.hom.op q) =
      r • h.app (op V.unop.left) (p ⊗ₜ PresheafOfModules.map Q V.unop.hom.op q)
    have ht := (TensorProduct.smul_tmul' (R := Γ(X, V.unop.left)) r p
      (PresheafOfModules.map Q V.unop.hom.op q : Q.obj (op V.unop.left))).symm
    exact (congrArg (h.app (op V.unop.left)) ht).trans
      ((h.app (op V.unop.left)).hom.map_smul r _)⟩

set_option backward.isDefEq.respectTransparency false in
/-- Currying a tensor arrow as a morphism of module presheaves into the Hom sheaf. -/
def curry (h : P ⊗ Q ⟶ N.val) : Q ⟶ (sheaf X P N).val where
  app U := ModuleCat.ofHom {
    toFun := currySection X P Q N h U
    map_add' q q' := by
      apply Subtype.ext
      change (_ : RawHom X P N U.unop) = _
      ext V p
      change h.app (op V.unop.left) (p ⊗ₜ PresheafOfModules.map Q V.unop.hom.op (q + q')) =
        h.app (op V.unop.left) (p ⊗ₜ PresheafOfModules.map Q V.unop.hom.op q) +
          h.app (op V.unop.left) (p ⊗ₜ PresheafOfModules.map Q V.unop.hom.op q')
      have hq : (PresheafOfModules.map Q V.unop.hom.op (q + q') : Q.obj (op V.unop.left)) =
          PresheafOfModules.map Q V.unop.hom.op q + PresheafOfModules.map Q V.unop.hom.op q' :=
        map_add _ q q'
      have ht := TensorProduct.tmul_add (R := Γ(X, V.unop.left))
        (show P.obj (op V.unop.left) from p)
        (show Q.obj (op V.unop.left) from PresheafOfModules.map Q V.unop.hom.op q)
        (show Q.obj (op V.unop.left) from PresheafOfModules.map Q V.unop.hom.op q')
      exact (congrArg (fun y : Q.obj (op V.unop.left) => h.app (op V.unop.left) (p ⊗ₜ y))
        hq).trans ((congrArg (h.app (op V.unop.left)) ht).trans
          ((h.app (op V.unop.left)).hom.map_add _ _))
    map_smul' r q := by
      apply Subtype.ext
      change (_ : RawHom X P N U.unop) = _
      ext V p
      change h.app (op V.unop.left) (p ⊗ₜ PresheafOfModules.map Q V.unop.hom.op (r • q)) =
        X.presheaf.map V.unop.hom.op r •
          h.app (op V.unop.left) (p ⊗ₜ PresheafOfModules.map Q V.unop.hom.op q)
      have hq := PresheafOfModules.map_smul Q V.unop.hom.op r q
      have ht := TensorProduct.tmul_smul (R := Γ(X, V.unop.left))
        (X.presheaf.map V.unop.hom.op r) (show P.obj (op V.unop.left) from p)
        (PresheafOfModules.map Q V.unop.hom.op q : Q.obj (op V.unop.left))
      exact (congrArg (fun y : Q.obj (op V.unop.left) => h.app (op V.unop.left) (p ⊗ₜ y))
        hq).trans ((congrArg (h.app (op V.unop.left)) ht).trans
          ((h.app (op V.unop.left)).hom.map_smul _ _)) }
  naturality {U V} i := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro q
    apply Subtype.ext
    change (_ : RawHom X P N V.unop) = _
    ext W p
    change h.app (op W.unop.left)
        (p ⊗ₜ PresheafOfModules.map Q W.unop.hom.op (PresheafOfModules.map Q i q)) =
      h.app (op W.unop.left)
        (p ⊗ₜ PresheafOfModules.map Q ((Over.map i.unop).obj W.unop).hom.op q)
    exact congrArg (fun y : Q.obj (op W.unop.left) => h.app (op W.unop.left) (p ⊗ₜ y))
      (PresheafOfModules.map_comp_apply Q i W.unop.hom.op q).symm

set_option backward.isDefEq.respectTransparency false in
/-- Uncurrying a morphism into the Hom sheaf: `p ⊗ q` goes to the value at `p` of the
Hom-sheaf section attached to `q`. -/
def uncurry (k : Q ⟶ (sheaf X P N).val) : P ⊗ Q ⟶ N.val :=
  PresheafOfModulesOfCommRing.homMk (fun U ↦
      ModuleCat.MonoidalCategory.tensorLift
        (fun p q ↦ (k.app U q).val.app (op (Over.mk (𝟙 U.unop))) p)
        (by intro p p' q; exact ((k.app U q).val.app _).hom.map_add _ _)
        (by intro r p q; exact (k.app U q).property (op (Over.mk (𝟙 U.unop))) r p)
        (by intro p q q'; rw [map_add]; rfl)
        (by
          intro r p q
          rw [(k.app U).hom.map_smul]
          change X.presheaf.map (𝟙 U.unop).op r •
            (show N.val.obj U from (k.app U q).val.app (op (Over.mk (𝟙 U.unop))) p) = _
          simp))
      (by
        intro U V i
        apply ModuleCat.MonoidalCategory.tensor_ext
        intro p q
        have hk := PresheafOfModules.naturality_apply k i q
        have hn := NatTrans.naturality_apply (k.app U q).val
          (Over.homMk i.unop : Over.mk i.unop ⟶ Over.mk (𝟙 U.unop)).op p
        change (k.app V (Q.map i q)).val.app (op (Over.mk (𝟙 V.unop)))
          (P.map i p) = N.val.map i ((k.app U q).val.app (op (Over.mk (𝟙 U.unop))) p)
        exact (congrArg (fun s : (sheaf X P N).val.obj V =>
          s.val.app (op (Over.mk (𝟙 V.unop))) (P.map i p)) hk).trans hn)

/-- The value of `uncurry` on a pure tensor. -/
theorem uncurry_app_tmul (k : Q ⟶ (sheaf X P N).val) (U : X.Opensᵒᵖ) (p : P.obj U)
    (q : Q.obj U) :
    (uncurry X P Q N k).app U (p ⊗ₜ q) = (k.app U q).val.app (op (Over.mk (𝟙 U.unop))) p :=
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem uncurry_curry (h : P ⊗ Q ⟶ N.val) : uncurry X P Q N (curry X P Q N h) = h := by
  ext U : 1
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro p q
  have hi := ConcreteCategory.congr_hom (Q.presheaf.map_id U) q
  change PresheafOfModules.map Q (𝟙 U) q = q at hi
  change h.app U (p ⊗ₜ PresheafOfModules.map Q (𝟙 U) q) = h.app U (p ⊗ₜ q)
  exact congrArg (fun y : Q.obj U => h.app U (p ⊗ₜ y)) hi

set_option backward.isDefEq.respectTransparency false in
theorem curry_uncurry (k : Q ⟶ (sheaf X P N).val) : curry X P Q N (uncurry X P Q N k) = k := by
  ext U : 1
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro q
  apply Subtype.ext
  change (_ : RawHom X P N U.unop) = _
  ext V p
  change (k.app (op V.unop.left) (PresheafOfModules.map Q V.unop.hom.op q)).val.app
    (op (Over.mk (𝟙 V.unop.left))) p = (k.app U q).val.app V p
  exact congrArg (fun s : (sheaf X P N).val.obj (op V.unop.left) =>
    s.val.app (op (Over.mk (𝟙 V.unop.left))) p)
    (PresheafOfModules.naturality_apply k V.unop.hom.op q)

/-- The tensor–Hom bijection: morphisms `P ⊗ Q ⟶ N` of module presheaves correspond to
morphisms `Q ⟶ Hom(P, N)` into the presheaf-source Hom sheaf. -/
def tensorHomEquiv : (P ⊗ Q ⟶ N.val) ≃ (Q ⟶ (sheaf X P N).val) where
  toFun := curry X P Q N
  invFun := uncurry X P Q N
  left_inv := uncurry_curry X P Q N
  right_inv := curry_uncurry X P Q N

variable {X P Q N}

set_option backward.isDefEq.respectTransparency false in
/-- Naturality of the tensor–Hom bijection in `Q`: whiskering by `P` on the left
corresponds to precomposition. -/
theorem tensorHomEquiv_whiskerLeft_comp {Q' : PresheafOfModulesOfCommRing.{u} X.sheaf.obj}
    (g : Q' ⟶ Q) (h : P ⊗ Q ⟶ N.val) :
    tensorHomEquiv X P Q' N (P ◁ g ≫ h) = g ≫ tensorHomEquiv X P Q N h := by
  ext U : 1
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro q
  apply Subtype.ext
  change (_ : RawHom X P N U.unop) = _
  ext V p
  change h.app (op V.unop.left)
      (p ⊗ₜ g.app (op V.unop.left) (PresheafOfModules.map Q' V.unop.hom.op q)) =
    h.app (op V.unop.left) (p ⊗ₜ PresheafOfModules.map Q V.unop.hom.op (g.app U q))
  exact congrArg (fun y : Q.obj (op V.unop.left) => h.app (op V.unop.left) (p ⊗ₜ y))
    (PresheafOfModules.naturality_apply g V.unop.hom.op q)

end AlgebraicGeometry.Scheme.Modules.InternalHom.PresheafSource
