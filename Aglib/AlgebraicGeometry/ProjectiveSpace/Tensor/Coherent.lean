/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.ProjectiveSpace.Tensor.Isomorphism
public import Aglib.AlgebraicGeometry.ProjectiveSpace.TwistPresentation.Coherent
public import Aglib.AlgebraicGeometry.Modules.LocallyFree.Tensor.Exact

/-!
# Finite twist sums and coherent tensor twists

The original additive tensor functor preserves finite coproducts. The actual twist tensor
isomorphism therefore identifies tensor twists of finite twist sums. Applying the exact
functor to the proved two-step presentation expresses every twisted coherent module as
an actual cokernel of coherent finite twist sums.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent

universe u

namespace AlgebraicGeometry.ProjectiveSpace

variable (R : Type u) [CommRing R] (ι : Type u)

/-- Tensoring an actual finite twist coproduct gives the native finite coproduct of the
sum twists, via the original finite-coproduct comparison and original multiplication. -/
def twistingTensorCoproductIso {I : Type u} [Finite I] (a : ℤ) (d : I → ℤ) :
    (moduleTensorLeftFunctor (ProjectiveSpace R ι) (twistingSheaf R ι a)).obj
        (∐ fun i => twistingSheaf R ι (d i)) ≅
      ∐ fun i => twistingSheaf R ι (a + d i) :=
  PreservesCoproduct.iso
    (moduleTensorLeftFunctor (ProjectiveSpace R ι) (twistingSheaf R ι a))
    (fun i => twistingSheaf R ι (d i)) ≪≫ Sigma.mapIso (fun i => twistingTensorIso R ι a (d i))

/-- The finite-sum tensor comparison retains the original tensor image of each summand
inclusion and the original multiplication map on that summand. -/
theorem twistingTensorCoproductIso_inclusion {I : Type u} [Finite I]
    (a : ℤ) (d : I → ℤ) (i : I) :
    (moduleTensorLeftFunctor (ProjectiveSpace R ι) (twistingSheaf R ι a)).map
        (Sigma.ι (fun j => twistingSheaf R ι (d j)) i) ≫
        (twistingTensorCoproductIso R ι a d).hom =
      twistingTensorMap R ι a (d i) ≫ Sigma.ι (fun j => twistingSheaf R ι (a + d j)) i := by
  let T := moduleTensorLeftFunctor (ProjectiveSpace R ι) (twistingSheaf R ι a)
  let F : I → (ProjectiveSpace R ι).Modules := fun j => twistingSheaf R ι (d j)
  have hi : T.map (Sigma.ι F i) ≫ (PreservesCoproduct.iso T F).hom =
      Sigma.ι (fun j => T.obj (F j)) i := by
    rw [← cancel_mono (PreservesCoproduct.iso T F).inv]
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
    rw [PreservesCoproduct.inv_hom, ι_comp_sigmaComparison]
  change T.map (Sigma.ι F i) ≫ (PreservesCoproduct.iso T F).hom ≫
    (Sigma.mapIso (fun j => twistingTensorIso R ι a (d j))).hom = _
  rw [← Category.assoc, hi, Sigma.ι_mapIso_hom]
  rfl

variable [IsNoetherianRing R] [Finite ι]

/-- The original tensor twist of a finite twist coproduct is coherent. -/
theorem twistingTensorCoproduct_affineLocallyFiniteType {I : Type u} [Finite I]
    (a : ℤ) (d : I → ℤ) :
    affineLocallyFiniteType (ProjectiveSpace R ι)
      ((moduleTensorLeftFunctor (ProjectiveSpace R ι) (twistingSheaf R ι a)).obj
        (∐ fun i => twistingSheaf R ι (d i))) :=
  (affineLocallyFiniteType (ProjectiveSpace R ι)).prop_of_iso
    (twistingTensorCoproductIso R ι a d).symm
    (twistingCoproduct_affineLocallyFiniteType R ι (fun i => a + d i))

/-- Twisting preserves actual coherent modules, by the original exact tensor functor and
an actual two-step finite-twist presentation. No cohomological vanishing is assumed. -/
theorem twistingTensor_affineLocallyFiniteType (a : ℤ)
    (M : (ProjectiveSpace R ι).Modules)
    (hM : affineLocallyFiniteType (ProjectiveSpace R ι) M) :
    affineLocallyFiniteType (ProjectiveSpace R ι)
      ((moduleTensorLeftFunctor (ProjectiveSpace R ι) (twistingSheaf R ι a)).obj M) := by
  obtain ⟨I, hI, N, J, hJ, L, d, π, hd, hS, hπ⟩ :=
    exists_negativeTwistTwoStepPresentation R ι M hM
  let := hI
  let := hJ
  let : Epi π := hπ
  let T := moduleTensorLeftFunctor (ProjectiveSpace R ι) (twistingSheaf R ι a)
  let : PreservesFiniteColimits T := Functor.preservesFiniteColimits_of_preservesHomology T
  let S := ShortComplex.mk d π hd
  let : Epi (S.map T).g := inferInstanceAs (Epi (T.map π))
  have hST : (S.map T).Exact := hS.map T
  exact (affineLocallyFiniteType (ProjectiveSpace R ι)).prop_of_isColimit hST.gIsCokernel
    (by rintro (_ | _)
        · exact twistingTensorCoproduct_affineLocallyFiniteType R ι a (fun j => -(L j : ℤ))
        · exact twistingTensorCoproduct_affineLocallyFiniteType R ι a (fun i => -(N i : ℤ)))

end AlgebraicGeometry.ProjectiveSpace
