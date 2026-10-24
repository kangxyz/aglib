/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.ProjectionFormula.FiniteLocallyFree
public import Aglib.AlgebraicGeometry.Modules.Tensor.Symmetry

/-!
# The degree-zero projection formula in Kleiman's order, natural in the coefficient

For a morphism of schemes `f : X ⟶ S`, a module sheaf `L` on `X` and a finite locally free
module sheaf `N` on `S`, `pushforwardTensorPullbackIso f L N` is an isomorphism
`f_*(L ⊗ f^*N) ≅ f_*L ⊗ N`, and `pushforwardTensorPullbackNatIso f L` is the same isomorphism
as a natural isomorphism of functors on the full subcategory `FiniteLocallyFree S`. This is the
isomorphism (iii) of Kleiman, *The Picard scheme*, arXiv:math/0504020v1, 3.10, p. 24, for
finite locally free `N`; there it is equivalent to the freeness of the module `Q` (for all
quasi-coherent `N`), here it holds for every morphism `f` and every module sheaf `L`. It is the
degree-zero case of Stacks Project, Tag 01E8 (Cohomology, Lemma 20.54.2).

The construction is the ordinary projection formula `projectionFormulaIso`
(`E ⊗ f_*M ≅ f_*(f^*E ⊗ M)` for finite locally free `E`) conjugated by the tensor symmetries.
It lives in degree zero: no derived functor is involved, and the derived isomorphism
`derivedProjectionFormulaIso` is itself built from the same ordinary natural transformation.
The inverse is the canonical projection map (`pushforwardTensorPullbackIso_inv`).

Consumer: the linear-system step of Kleiman, Thm 3.13 (proof, p. 25), in the locally free
regime (Picard plan row F15), which identifies sections of `L_T ⊗ f_T^*N` with sections of
`f_{T*}L_T ⊗ N`.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

variable {X S : Scheme.{u}} (f : X ⟶ S) (L : X.Modules)

/-- On finite locally free coefficients the projection-formula transformation, natural in the
coefficient, is an isomorphism. -/
instance isIso_whiskerLeft_projectionFormulaNatTrans :
    IsIso (Functor.whiskerLeft (finiteLocallyFreeForget (X := S))
      (projectionFormulaNatTrans f L)) := by
  have (N : FiniteLocallyFree S) : IsIso ((Functor.whiskerLeft
      (finiteLocallyFreeForget (X := S)) (projectionFormulaNatTrans f L)).app N) :=
    isIso_projectionFormulaMap f N.obj L
  exact NatIso.isIso_of_isIso_app _

/-- The degree-zero projection formula `f_*(L ⊗ f^*N) ≅ f_*L ⊗ N`, natural in the finite
locally free coefficient `N` (Kleiman, arXiv:math/0504020v1, 3.10 (iii), p. 24). -/
def pushforwardTensorPullbackNatIso :
    finiteLocallyFreeForget (X := S) ⋙ Scheme.Modules.pullback f ⋙
        moduleTensorLeftFunctor X L ⋙ Scheme.Modules.pushforward f ≅
      finiteLocallyFreeForget (X := S) ⋙
        moduleTensorLeftFunctor S ((Scheme.Modules.pushforward f).obj L) :=
  Functor.isoWhiskerLeft (finiteLocallyFreeForget (X := S) ⋙ Scheme.Modules.pullback f)
      (Functor.isoWhiskerRight (moduleTensorRightLeftIso X L).symm
        (Scheme.Modules.pushforward f)) ≪≫
    (asIso (Functor.whiskerLeft (finiteLocallyFreeForget (X := S))
      (projectionFormulaNatTrans f L))).symm ≪≫
    Functor.isoWhiskerLeft (finiteLocallyFreeForget (X := S))
      (moduleTensorRightLeftIso S ((Scheme.Modules.pushforward f).obj L))

/-- The degree-zero projection formula `f_*(L ⊗ f^*N) ≅ f_*L ⊗ N` for a finite locally free
`N` on the target (Kleiman, arXiv:math/0504020v1, 3.10 (iii), p. 24). -/
def pushforwardTensorPullbackIso (N : S.Modules) [IsFiniteLocallyFree S N] :
    (Scheme.Modules.pushforward f).obj
        ((moduleTensorLeftFunctor X L).obj ((Scheme.Modules.pullback f).obj N)) ≅
      (moduleTensorLeftFunctor S ((Scheme.Modules.pushforward f).obj L)).obj N :=
  (pushforwardTensorPullbackNatIso f L).app (ofFiniteLocallyFree N)

/-- The inverse of `pushforwardTensorPullbackIso` is the canonical projection map
`f_*L ⊗ N → f_*(L ⊗ f^*N)`, written through the original projection-formula arrow and the two
tensor symmetries. -/
theorem pushforwardTensorPullbackIso_inv (N : S.Modules) [IsFiniteLocallyFree S N] :
    (pushforwardTensorPullbackIso f L N).inv =
      (moduleTensorSymmetry S N ((Scheme.Modules.pushforward f).obj L)).inv ≫
        projectionFormulaMap f N L ≫
          (Scheme.Modules.pushforward f).map
            (moduleTensorSymmetry X ((Scheme.Modules.pullback f).obj N) L).hom := by
  simp only [pushforwardTensorPullbackIso, pushforwardTensorPullbackNatIso, Iso.app_inv,
    Iso.trans_inv, Iso.symm_inv, asIso_hom, NatTrans.comp_app, Category.assoc]
  rfl

/-- Naturality of `pushforwardTensorPullbackIso` in the finite locally free coefficient. -/
theorem pushforwardTensorPullbackIso_hom_naturality {N N' : S.Modules} [IsFiniteLocallyFree S N]
    [IsFiniteLocallyFree S N'] (g : N ⟶ N') :
    (Scheme.Modules.pushforward f).map
        ((moduleTensorLeftFunctor X L).map ((Scheme.Modules.pullback f).map g)) ≫
      (pushforwardTensorPullbackIso f L N').hom =
    (pushforwardTensorPullbackIso f L N).hom ≫
      (moduleTensorLeftFunctor S ((Scheme.Modules.pushforward f).obj L)).map g :=
  (pushforwardTensorPullbackNatIso f L).hom.naturality
    (ObjectProperty.homMk g : ofFiniteLocallyFree N ⟶ ofFiniteLocallyFree N')

end AlgebraicGeometry.Scheme.Modules
