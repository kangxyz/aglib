/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.Sheaf.InternalHom.PresheafSource
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal
public import Mathlib.CategoryTheory.HomCongr

/-!
# Actual presheaf tensor–Hom on a commutative ringed site

This constructs currying into the actual presheaf-source Hom sheaf. Only the target
must be a sheaf. Both tensor orientations use the native pointwise tensor, and the
second is obtained from the first by its actual braiding.

The ring and module carriers in this leaf are both `max uC vC r`. Thus the actual
ring-valued tensor unit fits, and the universe of slice natural transformations is
unchanged by Hom. The ring sheaf is already given in this common world; no smaller
ring presentation is silently lifted. The underlying plain Hom construction retains
its independent ring and module universes.

This generalizes the original scheme `Modules/InternalHom/PresheafTensor` construction,
retaining its actual section and pure-tensor maps.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory Opposite MonoidalCategory

universe uC vC r

namespace SheafOfModules.InternalHom.PresheafSource

variable {C : Type uC} [Category.{vC} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose
    (forget₂ CommRingCat.{max uC vC r} RingCat.{max uC vC r})]
  (R : Sheaf J CommRingCat.{max uC vC r})
  (P Q : PresheafOfModulesOfCommRing.{max uC vC r} R.obj)
  (N : SheafOfModules.{max uC vC r}
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))

/-- Restricting a Hom section and evaluating at the identity gives its original arrow component. -/
theorem sheaf_map_app_op_mk_id {U V : C} (i : V ⟶ U)
    (s : (sheaf R P N).val.obj (op U)) (p : P.obj (op V)) :
    ((sheaf R P N).val.map i.op s).val.app (op (Over.mk (𝟙 V))) p =
      s.val.app (op (Over.mk i)) p :=
  ConcreteCategory.congr_hom
    (CategoryTheory.presheafHom_map_app_op_mk_id (F := P.presheaf)
      (G := N.val.presheaf) i s.val) p

/-- Currying a tensor arrow on sections: a local section `q` of `Q` over `U` gives the
Hom-sheaf section `p ↦ h (p ⊗ q)` on the slice over `U`. -/
def currySection (h : P ⊗ Q ⟶ N.val) (U : Cᵒᵖ) (q : Q.obj U) :
    (sheaf R P N).val.obj U :=
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
          PresheafOfModules.map Q i.unop.left.op (PresheafOfModules.map Q V.unop.hom.op q) := by
        rw [← PresheafOfModules.map_comp_apply, ← op_comp, Over.w i.unop]
      exact congrArg (fun y : Q.obj (op W.unop.left) =>
        (PresheafOfModules.map P i.unop.left.op p ⊗ₜ y : (P ⊗ Q).obj (op W.unop.left))) hQ
  }, by
    intro V r p
    change h.app (op V.unop.left) ((r • p) ⊗ₜ PresheafOfModules.map Q V.unop.hom.op q) =
      r • h.app (op V.unop.left) (p ⊗ₜ PresheafOfModules.map Q V.unop.hom.op q)
    have ht := (TensorProduct.smul_tmul' (R := R.obj.obj (op V.unop.left)) r p
      (PresheafOfModules.map Q V.unop.hom.op q : Q.obj (op V.unop.left))).symm
    exact (congrArg (h.app (op V.unop.left)) ht).trans
      ((h.app (op V.unop.left)).hom.map_smul r _)⟩

/-- Currying a tensor arrow as a morphism of module presheaves into the Hom sheaf. -/
def curry (h : P ⊗ Q ⟶ N.val) : Q ⟶ (sheaf R P N).val where
  app U := ModuleCat.ofHom (X := Q.obj U) (Y := (sheaf R P N).val.obj U) {
    toFun := currySection.{uC, vC, r} R P Q N h U
    map_add' q q' := by
      apply Subtype.ext
      change (_ : RawHom R P N U.unop) = _
      ext V p
      change h.app (op V.unop.left) (p ⊗ₜ PresheafOfModules.map Q V.unop.hom.op (q + q')) =
        h.app (op V.unop.left) (p ⊗ₜ PresheafOfModules.map Q V.unop.hom.op q) +
          h.app (op V.unop.left) (p ⊗ₜ PresheafOfModules.map Q V.unop.hom.op q')
      have hq : (PresheafOfModules.map Q V.unop.hom.op (q + q') : Q.obj (op V.unop.left)) =
          PresheafOfModules.map Q V.unop.hom.op q + PresheafOfModules.map Q V.unop.hom.op q' :=
        map_add _ q q'
      have ht := TensorProduct.tmul_add (R := R.obj.obj (op V.unop.left))
        (show P.obj (op V.unop.left) from p)
        (show Q.obj (op V.unop.left) from PresheafOfModules.map Q V.unop.hom.op q)
        (show Q.obj (op V.unop.left) from PresheafOfModules.map Q V.unop.hom.op q')
      exact (congrArg (fun y : Q.obj (op V.unop.left) => h.app (op V.unop.left) (p ⊗ₜ y))
        hq).trans ((congrArg (h.app (op V.unop.left)) ht).trans
          ((h.app (op V.unop.left)).hom.map_add _ _))
    map_smul' r q := by
      apply Subtype.ext
      change (_ : RawHom R P N U.unop) = _
      ext V p
      change h.app (op V.unop.left) (p ⊗ₜ PresheafOfModules.map Q V.unop.hom.op (r • q)) =
        R.obj.map V.unop.hom.op r •
          h.app (op V.unop.left) (p ⊗ₜ PresheafOfModules.map Q V.unop.hom.op q)
      have hq := PresheafOfModules.map_smul Q V.unop.hom.op r q
      have ht := TensorProduct.tmul_smul (R := R.obj.obj (op V.unop.left))
        (R.obj.map V.unop.hom.op r) (show P.obj (op V.unop.left) from p)
        (PresheafOfModules.map Q V.unop.hom.op q : Q.obj (op V.unop.left))
      exact (congrArg (fun y : Q.obj (op V.unop.left) => h.app (op V.unop.left) (p ⊗ₜ y))
        hq).trans ((congrArg (h.app (op V.unop.left)) ht).trans
          ((h.app (op V.unop.left)).hom.map_smul _ _)) }
  naturality {U V} i := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro q
    apply Subtype.ext
    change (_ : RawHom R P N V.unop) = _
    ext W p
    change h.app (op W.unop.left)
        (p ⊗ₜ PresheafOfModules.map Q W.unop.hom.op (PresheafOfModules.map Q i q)) =
      h.app (op W.unop.left)
        (p ⊗ₜ PresheafOfModules.map Q ((Over.map i.unop).obj W.unop).hom.op q)
    exact congrArg (fun y : Q.obj (op W.unop.left) => h.app (op W.unop.left) (p ⊗ₜ y))
      (PresheafOfModules.map_comp_apply Q i W.unop.hom.op q).symm

/-- Uncurrying a morphism into the Hom sheaf: `p ⊗ q` goes to the value at `p` of the
Hom-sheaf section attached to `q`. -/
def uncurry (k : Q ⟶ (sheaf R P N).val) : P ⊗ Q ⟶ N.val :=
  PresheafOfModulesOfCommRing.homMk (fun U ↦
      ModuleCat.MonoidalCategory.tensorLift
        (fun p q ↦ (k.app U q).val.app (op (Over.mk (𝟙 U.unop))) p)
        (by intro p p' q; exact ((k.app U q).val.app _).hom.map_add _ _)
        (by intro r p q; exact (k.app U q).property (op (Over.mk (𝟙 U.unop))) r p)
        (by intro p q q'; rw [map_add]; rfl)
        (by
          intro r p q
          rw [(k.app U).hom.map_smul]
          change R.obj.map (𝟙 U.unop).op r •
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
        exact (congrArg (fun s : (sheaf R P N).val.obj V =>
          s.val.app (op (Over.mk (𝟙 V.unop))) (P.map i p)) hk).trans
            ((sheaf_map_app_op_mk_id.{uC, vC, r} R P N i.unop (k.app U q) (P.map i p)).trans hn))

/-- The value of `uncurry` on a pure tensor. -/
theorem uncurry_app_tmul (k : Q ⟶ (sheaf R P N).val) (U : Cᵒᵖ) (p : P.obj U)
    (q : Q.obj U) :
    (uncurry.{uC, vC, r} R P Q N k).app U (p ⊗ₜ q) =
      (k.app U q).val.app (op (Over.mk (𝟙 U.unop))) p :=
  rfl

theorem uncurry_curry (h : P ⊗ Q ⟶ N.val) :
    uncurry.{uC, vC, r} R P Q N (curry.{uC, vC, r} R P Q N h) = h := by
  ext U : 1
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro p q
  have hi := ConcreteCategory.congr_hom (Q.presheaf.map_id U) q
  change PresheafOfModules.map Q (𝟙 U) q = q at hi
  change h.app U (p ⊗ₜ PresheafOfModules.map Q (𝟙 U) q) = h.app U (p ⊗ₜ q)
  exact congrArg (fun y : Q.obj U => h.app U (p ⊗ₜ y)) hi

theorem curry_uncurry (k : Q ⟶ (sheaf R P N).val) :
    curry.{uC, vC, r} R P Q N (uncurry.{uC, vC, r} R P Q N k) = k := by
  ext U : 1
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro q
  apply Subtype.ext
  change (_ : RawHom R P N U.unop) = _
  ext V p
  change (k.app (op V.unop.left) (PresheafOfModules.map Q V.unop.hom.op q)).val.app
    (op (Over.mk (𝟙 V.unop.left))) p = (k.app U q).val.app V p
  exact (congrArg (fun s : (sheaf R P N).val.obj (op V.unop.left) =>
    s.val.app (op (Over.mk (𝟙 V.unop.left))) p)
    (PresheafOfModules.naturality_apply k V.unop.hom.op q)).trans
      (sheaf_map_app_op_mk_id.{uC, vC, r} R P N V.unop.hom (k.app U q) p)

/-- The tensor–Hom bijection: morphisms `P ⊗ Q ⟶ N` of module presheaves correspond to
morphisms `Q ⟶ Hom(P, N)` into the presheaf-source Hom sheaf. -/
def tensorHomEquiv : (P ⊗ Q ⟶ N.val) ≃ (Q ⟶ (sheaf R P N).val) where
  toFun := curry.{uC, vC, r} R P Q N
  invFun := uncurry.{uC, vC, r} R P Q N
  left_inv := uncurry_curry.{uC, vC, r} R P Q N
  right_inv := curry_uncurry.{uC, vC, r} R P Q N

variable {P Q N}

/-- Naturality of the tensor–Hom bijection in `Q`: whiskering by `P` on the left
corresponds to precomposition. -/
theorem tensorHomEquiv_whiskerLeft_comp {Q' : PresheafOfModulesOfCommRing.{max uC vC r} R.obj}
    (g : Q' ⟶ Q) (h : P ⊗ Q ⟶ N.val) :
    tensorHomEquiv.{uC, vC, r} R P Q' N (P ◁ g ≫ h) = g ≫ tensorHomEquiv.{uC, vC, r} R P Q N h := by
  ext U : 1
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro q
  apply Subtype.ext
  change (_ : RawHom R P N U.unop) = _
  ext V p
  change h.app (op V.unop.left)
      (p ⊗ₜ g.app (op V.unop.left) (PresheafOfModules.map Q' V.unop.hom.op q)) =
    h.app (op V.unop.left) (p ⊗ₜ PresheafOfModules.map Q V.unop.hom.op (g.app U q))
  exact congrArg (fun y : Q.obj (op V.unop.left) => h.app (op V.unop.left) (p ⊗ₜ y))
    (PresheafOfModules.naturality_apply g V.unop.hom.op q)

variable (P Q N)

/-- The opposite tensor orientation, using the actual native presheaf braiding. -/
def tensorHomEquivRight : (Q ⊗ P ⟶ N.val) ≃ (Q ⟶ (sheaf R P N).val) :=
  ((CategoryTheory.BraidedCategory.braiding Q P).homCongr (Iso.refl N.val)).trans
    (tensorHomEquiv.{uC, vC, r} R P Q N)

/-- Currying with the variable tensor factor on the left. -/
abbrev curryRight (h : Q ⊗ P ⟶ N.val) : Q ⟶ (sheaf R P N).val :=
  tensorHomEquivRight.{uC, vC, r} R P Q N h

/-- Uncurrying with the variable tensor factor on the left. -/
abbrev uncurryRight (k : Q ⟶ (sheaf R P N).val) : Q ⊗ P ⟶ N.val :=
  (tensorHomEquivRight.{uC, vC, r} R P Q N).symm k

/-- Right-oriented currying has the original sectionwise formula. -/
theorem curryRight_app (h : Q ⊗ P ⟶ N.val) (U : Cᵒᵖ) (q : Q.obj U)
    (V : (Over U.unop)ᵒᵖ) (p : P.obj (op V.unop.left)) :
    ((curryRight.{uC, vC, r} R P Q N h).app U q).val.app V p =
      h.app (op V.unop.left) (Q.map V.unop.hom.op q ⊗ₜ p) := rfl

/-- Right-oriented uncurrying evaluates the original Hom section on a pure tensor. -/
theorem uncurryRight_app_tmul (k : Q ⟶ (sheaf R P N).val) (U : Cᵒᵖ)
    (q : Q.obj U) (p : P.obj U) :
    (uncurryRight.{uC, vC, r} R P Q N k).app U (q ⊗ₜ p) =
      (k.app U q).val.app (op (Over.mk (𝟙 U.unop))) p := rfl

theorem uncurryRight_curryRight (h : Q ⊗ P ⟶ N.val) :
    uncurryRight.{uC, vC, r} R P Q N (curryRight.{uC, vC, r} R P Q N h) = h :=
  (tensorHomEquivRight.{uC, vC, r} R P Q N).symm_apply_apply h

theorem curryRight_uncurryRight (k : Q ⟶ (sheaf R P N).val) :
    curryRight.{uC, vC, r} R P Q N (uncurryRight.{uC, vC, r} R P Q N k) = k :=
  (tensorHomEquivRight.{uC, vC, r} R P Q N).apply_symm_apply k

variable {P Q N}

/-- Naturality in the variable left tensor factor, for the same actual tensor map. -/
theorem tensorHomEquivRight_whiskerRight_comp
    {Q' : PresheafOfModulesOfCommRing.{max uC vC r} R.obj}
    (g : Q' ⟶ Q) (h : Q ⊗ P ⟶ N.val) :
    tensorHomEquivRight.{uC, vC, r} R P Q' N (g ▷ P ≫ h) =
      g ≫ tensorHomEquivRight.{uC, vC, r} R P Q N h := by
  ext U : 1
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro q
  apply Subtype.ext
  change (_ : RawHom R P N U.unop) = _
  ext V p
  change h.app (op V.unop.left)
      (g.app (op V.unop.left) (Q'.map V.unop.hom.op q) ⊗ₜ p) =
    h.app (op V.unop.left) (Q.map V.unop.hom.op (g.app U q) ⊗ₜ p)
  exact congrArg (fun y : Q.obj (op V.unop.left) =>
    h.app (op V.unop.left) (y ⊗ₜ p))
      (PresheafOfModules.naturality_apply g V.unop.hom.op q)

end SheafOfModules.InternalHom.PresheafSource
