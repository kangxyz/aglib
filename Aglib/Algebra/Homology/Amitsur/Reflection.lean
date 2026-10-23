/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic

/-!
# Faithfully flat reflection for the original module complex

The usual native tensor functor preserves the original module maps.
Native faithfully flat reflection applies degree by degree, with ring,
scalar algebra and module universes independent.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory
open scoped TensorProduct

namespace ModuleCat.Amitsur

universe u v w

variable (R : Type u) [CommRing R] (S : Type v) [CommRing S] [Algebra R S]

/-- The usual underlying scalar-extension tensor functor, in independent universes. -/
def scalarTensorFunctor : ModuleCat.{w} R ⥤ ModuleCat.{max v w} R where
  obj M := ModuleCat.of R (S ⊗[R] M)
  map f := ModuleCat.ofHom (f.hom.lTensor S)
  map_id M := by ext s m; rfl
  map_comp f g := by ext s m; rfl

instance : (scalarTensorFunctor.{u, v, w} R S).Additive where
  map_add {X Y} {f g} := by
    apply ModuleCat.hom_ext
    apply TensorProduct.ext'
    intro s m
    exact TensorProduct.tmul_add _ _ _

/-- Exactness of the same original short complex is equivalent to exactness
after tensoring by the original faithfully flat scalar algebra. -/
theorem shortComplex_exact_iff_scalarTensor [Module.FaithfullyFlat R S]
    (K : ShortComplex (ModuleCat.{w} R)) :
    (K.map (scalarTensorFunctor R S)).Exact ↔ K.Exact := by
  rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact,
    ShortComplex.ShortExact.moduleCat_exact_iff_function_exact]
  exact Module.FaithfullyFlat.lTensor_exact_iff_exact R S K.f.hom K.g.hom

/-- Native faithfully flat tensor exactness reflects the actual original
complex in every degree, without any flatness hypothesis on its modules. -/
theorem exactAt_iff_scalarTensor [Module.FaithfullyFlat R S]
    {ι : Type*} {c : ComplexShape ι} (K : HomologicalComplex (ModuleCat.{w} R) c) (n : ι) :
    (((scalarTensorFunctor R S).mapHomologicalComplex c).obj K).ExactAt n ↔ K.ExactAt n := by
  rw [HomologicalComplex.exactAt_iff, HomologicalComplex.exactAt_iff]
  exact shortComplex_exact_iff_scalarTensor R S (K.sc n)

end ModuleCat.Amitsur
