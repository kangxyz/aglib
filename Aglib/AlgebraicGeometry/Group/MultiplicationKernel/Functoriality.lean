/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Group.Kernel.Functoriality
public import Aglib.AlgebraicGeometry.Group.MultiplicationKernel

/-!
# Functoriality of the original multiplication kernels

The native power square supplies the original kernel map and its identity,
composition and isomorphism laws. No invertibility or finiteness is used.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory MonObj
open Scheme.OverField
open scoped CategoryTheory.MonObj

universe u

namespace AlgebraicGeometry.Scheme.Group.MultiplicationKernel

attribute [local instance] Over.cartesianMonoidalCategory

variable {k : Type u} [Field k] {G H I : Grp (FScheme k)}
  [IsCommMonObj G.X] [IsCommMonObj H.X]

/-- The original group map commutes with original multiplication. -/
theorem multiplicationHom_naturality (f : G ⟶ H) (n : ℕ) :
    f ≫ multiplicationHom H n = multiplicationHom G n ≫ f := by
  apply Grp.hom_ext
  simp only [Grp.comp_hom_hom, multiplicationHom_hom, multiplication,
    MonObj.comp_pow, MonObj.pow_comp, Category.comp_id, Category.id_comp]

/-- Restrict the given group morphism to the two actual multiplication kernels. -/
@[no_expose]
def map (f : G ⟶ H) (n : ℕ) : kernelGroup G n ⟶ kernelGroup H n :=
  Kernel.map (multiplicationHom G n) (multiplicationHom H n) f f
    (multiplicationHom_naturality f n)

/-- The inclusion equation retains the literal map `f`. -/
@[reassoc (attr := simp)]
theorem map_inclusion (f : G ⟶ H) (n : ℕ) :
    map f n ≫ Kernel.inclusion (multiplicationHom H n) =
      Kernel.inclusion (multiplicationHom G n) ≫ f :=
  Kernel.map_inclusion _ _ _ _ _

/-- Identity is retained on the same original multiplication kernel. -/
@[simp]
theorem map_id (n : ℕ) : map (𝟙 G) n = 𝟙 (kernelGroup G n) :=
  Kernel.map_id (multiplicationHom G n)

/-- Composition is retained on the same original multiplication kernels. -/
theorem map_comp [IsCommMonObj I.X] (f : G ⟶ H) (g : H ⟶ I) (n : ℕ) :
    map (f ≫ g) n = map f n ≫ map g n :=
  (Kernel.map_comp _ _ _ _ _ (multiplicationHom_naturality f n)
    _ _ (multiplicationHom_naturality g n)).symm

/-- The original group isomorphism restricts to the original kernels. -/
@[no_expose]
def mapIso (e : G ≅ H) (n : ℕ) : kernelGroup G n ≅ kernelGroup H n :=
  Kernel.mapIso (multiplicationHom G n) (multiplicationHom H n) e e
    (multiplicationHom_naturality e.hom n)

/-- The restricted isomorphism has the same original forward map. -/
theorem mapIso_hom (e : G ≅ H) (n : ℕ) : (mapIso e n).hom = map e.hom n :=
  Kernel.mapIso_hom _ _ _ _ _

end AlgebraicGeometry.Scheme.Group.MultiplicationKernel
