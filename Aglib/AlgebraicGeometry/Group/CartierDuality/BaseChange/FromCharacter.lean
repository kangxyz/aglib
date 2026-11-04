/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Group.CartierDuality.BaseChange.CharacterSquare
public import Aglib.AlgebraicGeometry.Group.CartierDuality.BaseChange.Group
public import Aglib.AlgebraicGeometry.Group.CartierDuality.UniversalProperty.Functoriality

/-! The original Cartier field square is detected on the original universal character. -/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.OverField

universe u

namespace AlgebraicGeometry.Scheme.Group.CartierDuality

attribute [local instance] Over.cartesianMonoidalCategory

variable {k K : Type u} [Field k] [Field K]
  (b : Base K ⟶ Base k)
  (G : Grp (FScheme k)) [IsFinite G.X.hom] [IsCommMonObj G.X]
  (H : Grp (FScheme K)) [IsFinite H.X.hom] [IsCommMonObj H.X]
  {E : Grp (FScheme k)} {E' : Grp (FScheme K)}
  (u : (Over.pullback b).mapGrp.obj G ⟶ H)
  (v : (Over.pullback b).mapGrp.obj E ⟶ E')
  (c : E ⟶ dualGroup G) (c' : E' ⟶ dualGroup H)

/-- The original comparison of characters on the universal test gives the
whole original field square of Cartier maps. -/
theorem dualGroupBaseChangeIso_hom_eq_of_universal_character
    (hc :
      let T := (Over.pullback b).obj E.X
      let s : (Over.map b).obj T ⟶ E.X := (Over.mapPullbackAdj b).counit.app E.X
      let v₀ : T ⟶ E'.X := v.hom.hom
      (Over.pullback T.hom).mapGrp.map u ≫ characterEquiv H T (v₀ ≫ c'.hom.hom) =
        (BaseChange.groupSchemeBaseChangeComp T.hom b).inv.app G ≫
          characterEquiv G ((Over.map b).obj T) (s ≫ c.hom.hom)) :
    v ≫ c' ≫ dualMap u = (Over.pullback b).mapGrp.map c ≫
      (dualGroupBaseChangeIso K G b).hom := by
  let T := (Over.pullback b).obj E.X
  let s : (Over.map b).obj T ⟶ E.X := (Over.mapPullbackAdj b).counit.app E.X
  let v₀ : T ⟶ E'.X := v.hom.hom
  let p := v₀ ≫ c'.hom.hom
  have hs : ((Over.mapPullbackAdj b).homEquiv T E.X).symm (𝟙 T) = s := by
    apply Over.OverMorphism.ext
    simp only [s, Over.mapPullbackAdj_counit_app, Over.homMk_left]
    rfl
  have hl := characterEquiv_dualMap u T p
  have hr := dualGroupBaseChangeOverIso_character_square G b T E.X (𝟙 T) c.hom.hom
  simp only [hs] at hr
  let f : T ⟶ (dualGroup ((Over.pullback b).mapGrp.obj G)).X :=
    (Over.pullback b).map c.hom.hom ≫ (dualGroupBaseChangeOverIso K G b).hom
  have hId := congrArg (characterEquiv ((Over.pullback b).mapGrp.obj G) T) (Category.id_comp f)
  have h := hl.trans (hc.trans (hr.symm.trans hId))
  apply Grp.hom_ext
  apply (characterEquiv ((Over.pullback b).mapGrp.obj G) T).injective
  change characterEquiv ((Over.pullback b).mapGrp.obj G) T
      (v₀ ≫ c'.hom.hom ≫ (dualMap u).hom.hom) =
    characterEquiv ((Over.pullback b).mapGrp.obj G) T
      ((Over.pullback b).map c.hom.hom ≫ (dualGroupBaseChangeIso K G b).hom.hom.hom)
  rw [dualGroupBaseChangeIso_hom]
  simpa only [p, f, Category.assoc] using h

end AlgebraicGeometry.Scheme.Group.CartierDuality
