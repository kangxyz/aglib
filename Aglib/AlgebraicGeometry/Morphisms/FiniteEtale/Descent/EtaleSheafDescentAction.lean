/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.CategoryTheory.Sites.PresheafRepresentedDescent
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.Descent.FiniteRepresentedRestriction

/-! Construct the actual etale descent action from a local representative of a
set sheaf; the action and its laws are outputs. -/

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits AlgebraicGeometry Opposite
open _root_.AlgebraicGeometry.Scheme.FiniteEtale (toEtale)

namespace AlgebraicGeometry.Scheme.FiniteEtale.SheafDescent

universe u
variable {X S : Scheme.{u}}

/-- The existing lifted section sheaf is the lifted Yoneda presheaf of the
same finite etale object in the small site. -/
def finiteRepresentedYonedaIso (Y : Scheme.FiniteEtale S) :
    uliftYoneda.{u + 1}.obj ((toEtale S).obj Y) ≅ (Scheme.EtaleH1.finiteRepresentedSetSheaf
      Y).obj :=
  NatIso.ofComponents
    (fun U => ((Equiv.ulift.trans
      ((Functor.FullyFaithful.ofFullyFaithful (Scheme.Etale.forget S)).homEquiv
        (X := U.unop) (Y := (toEtale S).obj Y))).trans Equiv.ulift.symm).toIso)
    (fun {U V} g => by
      ext z
      exact congrArg ULift.up ((Scheme.Etale.forget S).map_comp g.unop z.down))

variable (f : S ⟶ X) [Etale f] (F : Scheme.EtaleH1.SetSheaf X) (Y : Scheme.FiniteEtale S)
variable (e : Scheme.EtaleH1.finiteRepresentedSetSheaf Y ≅ (Scheme.EtaleH1.setEtaleRestriction
  f).obj F)

/-- The local represented restriction induces the actual descent monad algebra. -/
def sheafDescentAlgebra : (Scheme.EtaleH1.siteEtalePostcomposeAdj f).toMonad.Algebra :=
  CategoryTheory.PresheafRepresentedDescent.algebra (Scheme.EtaleH1.siteEtalePostcomposeAdj f) F.obj
    (finiteRepresentedYonedaIso Y ≪≫ (sheafToPresheaf _ _).mapIso e)

/-- The action map on the actual schemes, over S. -/
def sheafDescentMap : pullback (Y.obj.hom ≫ f) f ⟶ Y.obj.left :=
  (sheafDescentAlgebra f F Y e).a.left

lemma sheafDescentMap_over :
    sheafDescentMap f F Y e ≫ Y.obj.hom = pullback.snd (Y.obj.hom ≫ f) f :=
  MorphismProperty.Over.w (sheafDescentAlgebra f F Y e).a

/-- The diagonal acts as the identity, as required for genuine descent data. -/
lemma sheafDescentMap_unit :
    pullback.lift (𝟙 Y.obj.left) Y.obj.hom (by simp) ≫ sheafDescentMap f F Y e =
      𝟙 Y.obj.left :=
  congrArg (fun k => k.left) (sheafDescentAlgebra f F Y e).unit

end AlgebraicGeometry.Scheme.FiniteEtale.SheafDescent

/- Migration source: the R5Lab/Aglib mirror; exact module in the migration record.
R5 revision c82abf3a72ce1e1cedf4a4f1fe08bea994ad4df5.
SHA256 e38580e514546b4fc6b10b52d78ebc93e77985ef3304b6def192b37344269dc1.
Definitions, hypotheses and universes are retained modulo native names. -/
