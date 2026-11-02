/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.Sheaf.InternalHom.Basic

/-!
# Coefficient maps for actual ring-linear internal Hom

The maps are literal precomposition and postcomposition on slices. The output
module universe is the one of the actual Hom construction. The same constructors
supply both arbitrary-site maps and their original scheme specializations.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory Opposite

universe uC vC uR uM

namespace SheafOfModules.InternalHom

variable {C : Type uC} [Category.{vC} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{uR} RingCat.{uR})]
  (R : Sheaf J CommRingCat.{uR})

variable (M N : SheafOfModules.{uM} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))

variable {M N} {M' N' : SheafOfModules.{uM} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)}

/-- Map internal homs over `U` by precomposition with `a` and postcomposition with `b`. -/
def overHomMap (U : C) (a : M'.over U ⟶ M.over U) (b : N.over U ⟶ N'.over U) :
    (sheaf R M N).over U ⟶ (sheaf R M' N').over U where
  val.app V := ModuleCat.ofHom {
    toFun s := ⟨Functor.whiskerLeft (Over.map V.unop.hom).op
        ((_root_.PresheafOfModules.toPresheaf _).map a.val) ≫ s.val ≫
      Functor.whiskerLeft (Over.map V.unop.hom).op
        ((_root_.PresheafOfModules.toPresheaf _).map b.val), by
      intro W r m
      change b.val.app (op ((Over.map V.unop.hom).obj W.unop))
          (s.val.app W (a.val.app (op ((Over.map V.unop.hom).obj W.unop)) (r • m))) =
        r • b.val.app (op ((Over.map V.unop.hom).obj W.unop))
          (s.val.app W (a.val.app (op ((Over.map V.unop.hom).obj W.unop)) m))
      rw [(a.val.app _).hom.map_smul, s.property, (b.val.app _).hom.map_smul]⟩
    map_add' s t := by
      apply Subtype.ext
      change (_ : RawHom R M' N' V.unop.left) = _
      ext W m
      let T := op ((Over.map V.unop.hom).obj W.unop)
      change b.val.app T (s.val.app W (a.val.app T m) + t.val.app W (a.val.app T m)) = _
      exact (b.val.app T).hom.map_add _ _
    map_smul' r s := by
      apply Subtype.ext
      change (_ : RawHom R M' N' V.unop.left) = _
      ext W m
      let T := op ((Over.map V.unop.hom).obj W.unop)
      change b.val.app T (R.obj.map W.unop.hom.op r • s.val.app W (a.val.app T m)) =
        R.obj.map W.unop.hom.op r • b.val.app T (s.val.app W (a.val.app T m))
      exact (b.val.app T).hom.map_smul _ _ }
  val.naturality {V W} i := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro s
    apply Subtype.ext
    change (_ : RawHom R M' N' W.unop.left) = _
    ext T m
    change b.val.app (op (Over.mk (T.unop.hom ≫ W.unop.hom)))
        (s.val.app (op (Over.mk (T.unop.hom ≫ i.unop.left)))
          (a.val.app (op (Over.mk (T.unop.hom ≫ W.unop.hom))) m)) =
      b.val.app (op (Over.mk ((T.unop.hom ≫ i.unop.left) ≫ V.unop.hom)))
        (s.val.app (op (Over.mk (T.unop.hom ≫ i.unop.left)))
          (a.val.app (op (Over.mk ((T.unop.hom ≫ i.unop.left) ≫ V.unop.hom))) m))
    have h : (T.unop.hom ≫ i.unop.left) ≫ V.unop.hom = T.unop.hom ≫ W.unop.hom :=
      (Category.assoc _ _ _).trans
        (congrArg (fun g : W.unop.left ⟶ U => T.unop.hom ≫ g) (Over.w i.unop))
    exact congrArg (fun g : T.unop.left ⟶ U =>
      (show N'.val.obj (op T.unop.left) from
        b.val.app (op (Over.mk g))
          (s.val.app (op (Over.mk (T.unop.hom ≫ i.unop.left)))
            (a.val.app (op (Over.mk g)) m)))) h.symm

theorem overIso_hom_inv_apply {U : C} (e : M.over U ≅ M'.over U)
    (V : (Over U)ᵒᵖ) (m : (M.over U).val.obj V) :
    e.inv.val.app V (e.hom.val.app V m) = m := by
  exact congrArg (fun z : M.over U ⟶ M.over U => z.val.app V m) e.hom_inv_id

/-- Transport internal homs along isomorphisms of the source and target over `U`.
The forward map precomposes with `e.inv` and postcomposes with `f.hom`. -/
def overHomIso (U : C) (e : M.over U ≅ M'.over U) (f : N.over U ≅ N'.over U) :
    (sheaf R M N).over U ≅ (sheaf R M' N').over U where
  hom := overHomMap R U e.inv f.hom
  inv := overHomMap R U e.hom f.inv
  hom_inv_id := by
    apply SheafOfModules.hom_ext
    ext V : 1
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro s
    apply Subtype.ext
    change (_ : RawHom R M N V.unop.left) = _
    ext W m
    let T := op ((Over.map V.unop.hom).obj W.unop)
    change f.inv.val.app T (f.hom.val.app T
      (s.val.app W (e.inv.val.app T (e.hom.val.app T m)))) = s.val.app W m
    rw [overIso_hom_inv_apply R e, overIso_hom_inv_apply R f]
  inv_hom_id := by
    apply SheafOfModules.hom_ext
    ext V : 1
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro s
    apply Subtype.ext
    change (_ : RawHom R M' N' V.unop.left) = _
    ext W m
    let T := op ((Over.map V.unop.hom).obj W.unop)
    change f.hom.val.app T (f.inv.val.app T
      (s.val.app W (e.hom.val.app T (e.inv.val.app T m)))) = s.val.app W m
    have he := overIso_hom_inv_apply R e.symm T m
    have hf := overIso_hom_inv_apply R f.symm T (s.val.app W m)
    change e.hom.val.app T (e.inv.val.app T m) = m at he
    change f.hom.val.app T (f.inv.val.app T (s.val.app W m)) = s.val.app W m at hf
    rw [he]
    exact hf

/-- Map internal Hom sheaves by precomposition in the source and postcomposition in the target. -/
def map (a : M' ⟶ M) (b : N ⟶ N') : sheaf R M N ⟶ sheaf R M' N' where
  val.app U := ModuleCat.ofHom {
    toFun s := (sectionHomEquiv R M' N' U.unop).symm
      ((SheafOfModules.overFunctor
          ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) U.unop).map a ≫
        sectionHomEquiv R M N U.unop s ≫
        (SheafOfModules.overFunctor
          ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) U.unop).map b)
    map_add' s t := by
      apply Subtype.ext
      change (_ : RawHom R M' N' U.unop) = _
      ext V m
      exact (b.val.app (op V.unop.left)).hom.map_add _ _
    map_smul' r s := by
      apply Subtype.ext
      change (_ : RawHom R M' N' U.unop) = _
      ext V m
      exact (b.val.app (op V.unop.left)).hom.map_smul _ _ }
  val.naturality {U V} i := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro s
    apply Subtype.ext
    change (_ : RawHom R M' N' V.unop) = _
    ext W m
    rfl
theorem map_apply (a : M' ⟶ M) (b : N ⟶ N') (U : C)
    (s : (sheaf R M N).val.obj (op U)) (V : (Over U)ᵒᵖ)
    (m : M'.val.obj (op V.unop.left)) :
    ((map R a b).val.app (op U) s).val.app V m =
      b.val.app (op V.unop.left) (s.val.app V (a.val.app (op V.unop.left) m)) := rfl
@[simp] theorem map_id : map R (𝟙 M) (𝟙 N) = 𝟙 (sheaf R M N) := by
  apply SheafOfModules.hom_ext
  ext U : 1
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro s
  apply Subtype.ext
  change (_ : RawHom R M N U.unop) = _
  ext V m
  rfl
variable {M'' N'' : SheafOfModules.{uM} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)}
@[reassoc] theorem map_comp (a : M' ⟶ M) (b : N ⟶ N')
    (c : M'' ⟶ M') (d : N' ⟶ N'') :
    map R a b ≫ map R c d = map R (c ≫ a) (b ≫ d) := by
  apply SheafOfModules.hom_ext
  ext U : 1
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro s
  apply Subtype.ext
  change (_ : RawHom R M'' N'' U.unop) = _
  ext V m
  rfl
/-- Transport the internal Hom sheaf along the specified source and target isomorphisms. -/
def iso (e : M ≅ M') (f : N ≅ N') : sheaf R M N ≅ sheaf R M' N' where
  hom := map R e.inv f.hom
  inv := map R e.hom f.inv
  hom_inv_id := by rw [map_comp, e.hom_inv_id, f.hom_inv_id, map_id]
  inv_hom_id := by rw [map_comp, e.inv_hom_id, f.inv_hom_id, map_id]

/-- The coefficient map acts by the original restricted precomposition and postcomposition. -/
theorem sectionHomEquiv_map_coefficients (a : M' ⟶ M) (b : N ⟶ N') (U : C)
    (s : (sheaf R M N).val.obj (op U)) :
    sectionHomEquiv R M' N' U ((map R a b).val.app (op U) s) =
      (SheafOfModules.overFunctor
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) U).map a ≫
          sectionHomEquiv R M N U s ≫
        (SheafOfModules.overFunctor
          ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) U).map b :=
  (sectionHomEquiv R M' N' U).apply_symm_apply _

end SheafOfModules.InternalHom
