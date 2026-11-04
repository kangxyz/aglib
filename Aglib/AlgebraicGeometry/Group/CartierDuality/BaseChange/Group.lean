/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Group.CartierDuality.BaseChange
public import Aglib.AlgebraicGeometry.Group.CartierDuality.UniversalProperty.Group

/-! # The same canonical Cartier dual base-change map as a group isomorphism -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.Scheme.Group.CartierDuality

universe u
open AlgebraicGeometry.Scheme.OverField (FScheme Base)
attribute [local instance] Over.cartesianMonoidalCategory

variable {k : Type u} [Field k] (K : Type u) [Field K]
  (G : Grp (FScheme k)) [IsFinite G.X.hom] [IsCommMonObj G.X]

/-- The original base-change character equivalence preserves the native point products. -/
theorem characterEquivBaseChange_mul (i : Base K ⟶ Base k) (T : FScheme K)
    (p q : T ⟶ ((Over.pullback i).mapGrp.obj (dualGroup G)).X) :
    characterEquivBaseChange G (Over.mk i) T (p * q) =
      characterEquivBaseChange G (Over.mk i) T p *
        characterEquivBaseChange G (Over.mk i) T q := by
  let e := MultiplicativeBaseChange.pullbackSectionsEquiv i (dualGroup G) T
  have he : ((Over.mapPullbackAdj i).homEquiv T (dualGroup G).X).symm (p * q) =
      ((Over.mapPullbackAdj i).homEquiv T (dualGroup G).X).symm p *
        ((Over.mapPullbackAdj i).homEquiv T (dualGroup G).X).symm q := e.map_mul p q
  rw [characterEquivBaseChange_apply, characterEquivBaseChange_apply,
    characterEquivBaseChange_apply]
  dsimp only [Over.mk_hom, Over.mk_left] at he ⊢
  rw [he, characterEquiv_mul, MonObj.comp_mul]

/-- The exact previously constructed comparison preserves products on every original test. -/
theorem dualGroupBaseChangeOverIso_comp_mul (i : Base K ⟶ Base k) (T : FScheme K)
    (p q : T ⟶ ((Over.pullback i).mapGrp.obj (dualGroup G)).X) :
    (p * q) ≫ (dualGroupBaseChangeOverIso K G i).hom =
      (p ≫ (dualGroupBaseChangeOverIso K G i).hom) *
        (q ≫ (dualGroupBaseChangeOverIso K G i).hom) := by
  apply (characterEquiv (k := K) ((Over.pullback i).mapGrp.obj G) T).injective
  rw [dualGroupBaseChangeOverIso_character, characterEquiv_mul,
    dualGroupBaseChangeOverIso_character, dualGroupBaseChangeOverIso_character,
    characterEquivBaseChange_mul]

/-- The exact comparison preserves the original unit on all tests. -/
theorem dualGroupBaseChangeOverIso_comp_one (i : Base K ⟶ Base k) (T : FScheme K) :
    (1 : T ⟶ ((Over.pullback i).mapGrp.obj (dualGroup G)).X) ≫
      (dualGroupBaseChangeOverIso K G i).hom = 1 := by
  let a := (1 : T ⟶ ((Over.pullback i).mapGrp.obj (dualGroup G)).X) ≫
    (dualGroupBaseChangeOverIso K G i).hom
  have hone := congrArg
    (fun p : T ⟶ ((Over.pullback i).mapGrp.obj (dualGroup G)).X =>
      p ≫ (dualGroupBaseChangeOverIso K G i).hom)
    (one_mul (1 : T ⟶ ((Over.pullback i).mapGrp.obj (dualGroup G)).X))
  have h : a = a * a := hone.symm.trans
    (dualGroupBaseChangeOverIso_comp_mul K G i T 1 1)
  have h' := congrArg (fun z => a⁻¹ * z) h
  have ha : 1 = a := by simpa only [inv_mul_cancel, inv_mul_cancel_left] using h'
  exact ha.symm

/-- Character uniqueness and original evaluation bilinearity upgrade the SAME comparison map. -/
theorem dualGroupBaseChangeOverIso_isMonHom (i : Base K ⟶ Base k) :
    IsMonHom (dualGroupBaseChangeOverIso K G i).hom where
  one_hom := by
    have h := dualGroupBaseChangeOverIso_comp_one K G i (𝟙_ (FScheme K))
    simpa only [MonObj.one_eq_one, toUnit_unit, Category.id_comp] using h
  mul_hom := by
    let A := ((Over.pullback i).mapGrp.obj (dualGroup G)).X
    let f := (dualGroupBaseChangeOverIso K G i).hom
    have h := dualGroupBaseChangeOverIso_comp_mul K G i (A ⊗ A) (fst A A) (snd A A)
    rw [← MonObj.mul_eq_mul] at h
    change μ[A] ≫ f = lift (fst A A ≫ f) (snd A A ≫ f) ≫ _ at h
    rw [lift_fst_comp_snd_comp] at h
    exact h

/-- The canonical group isomorphism has the exact original Over comparison as its hom. -/
def dualGroupBaseChangeIso (i : Base K ⟶ Base k) :
    (Over.pullback i).mapGrp.obj (dualGroup G) ≅
      dualGroup (k := K) ((Over.pullback i).mapGrp.obj G) := by
  let : IsMonHom (dualGroupBaseChangeOverIso K G i).hom :=
    dualGroupBaseChangeOverIso_isMonHom K G i
  exact Grp.mkIso' (dualGroupBaseChangeOverIso K G i)

/-- Forgetting the group comparison recovers the SAME actual Over hom. -/
theorem dualGroupBaseChangeIso_hom (i : Base K ⟶ Base k) :
    (dualGroupBaseChangeIso K G i).hom.hom.hom =
      (dualGroupBaseChangeOverIso K G i).hom := rfl

end AlgebraicGeometry.Scheme.Group.CartierDuality
