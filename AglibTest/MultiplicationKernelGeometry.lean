/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Group.MultiplicationKernel.Transitions

/-!
# Actual multiplication-kernel interfaces at arbitrary levels

The examples check the original geometric point carrier, comparison to the
native kernel group, finiteness without etaleness, the ordered difference `t-s`,
the genuine Galois action, and the level-zero cover-transition interface.
No multiplication theorem for an arbitrary group scheme is inferred.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.MonObj CategoryTheory.PreGaloisCategory
open AlgebraicGeometry.Scheme.OverField
open AlgebraicGeometry.Scheme.FiniteEtale
open AlgebraicGeometry.Scheme.EtaleFundamentalGroups
open AlgebraicGeometry.Scheme.Group.MultiplicationKernel
open AlgebraicGeometry.Scheme.Group.MultiplicationKernel.MonodromyQuotient
open AlgebraicGeometry.Scheme.Group.MultiplicationKernel.MonodromyQuotient.Transitions

universe u
attribute [local instance] Over.cartesianMonoidalCategory
variable {F : Type u} [Field F] (E : Grp (FScheme F)) [IsCommMonObj E.X]

-- Zero remains a valid multiplication level, on the same literal point carrier.
example : multiplication E 0 = (1 : E.X ⟶ E.X) := rfl

example : geometricPoints E =
    Additive (Over.mk (FieldGalois.geometricPoint F) ⟶ E.X) := rfl

-- The comparison recovers the actual inclusion, rather than a new abstract point marking.
example (n : ℕ) (t : finiteTorsionPoints E n) :
    nativeKernelPointEquiv E n t ≫
      (Scheme.Group.Kernel.inclusion (multiplicationHom E n)).hom.hom = t.val.toMul :=
  nativeKernelPointEquiv_inclusion E n t

-- Etaleness and a positive-level assumption are unnecessary for this finiteness theorem.
example (n : ℕ) [IsFinite (multiplication E n).left] : Finite (finiteTorsionPoints E n) :=
  inferInstance

example (n : ℕ) (σ : Field.absoluteGaloisGroup F) (t : finiteTorsionPoints E n) :
    kernelPointEquiv E n (σ • t) =
      FieldGalois.pointEnd F σ ≫ kernelPointEquiv E n t :=
  kernelPointEquiv_galois E n σ t

section FiniteEtale
variable (n : ℕ) [IsFinite (multiplication E n).left] [Etale (multiplication E n).left]

-- The first lift minus the second lift fixes the sign of the quotient homomorphism.
example (t s : finiteTorsionPoints E n) :
    kernelFiberEquiv E n (pairPoint E n t s ≫ (differenceCoverMap E n).hom) =
      kernelPointEquiv E n (t - s) := difference_pairPoint E n t s

example (g : N E) (t : finiteTorsionPoints E n) :
    rho E n g.val t = quotientMap E n g + t := rho_kernel E n g t

-- This is the additive quotient of the actual arithmetic projection kernel.
example (g h : Additive (N E)) :
    additiveQuotient E n (g + h) = additiveQuotient E n g + additiveQuotient E n h :=
  map_add (additiveQuotient E n) g h

example [TopologicalSpace (finiteTorsionPoints E n)]
    [DiscreteTopology (finiteTorsionPoints E n)] : Continuous (quotientMap E n) :=
  quotientMap_continuous E n

-- The geometric assumptions belong to surjectivity only.
example [CharZero F] [IsProper E.X.hom] [GeometricallyConnected E.X.hom]
    [GaloisCategory (Scheme.FiniteEtale (GeometricKernel.geometricBaseChange F E.X.hom))]
    [PreGaloisCategory.FiberFunctor (fiberToFinite
      (GeometricKernel.geometricPoint F E.X.hom (o E) (Over.w η[E.X])))]
    (h0BTX : GeometricKernel.Stacks0BTX F)
    (h0387 : GeometricCoverConnectedness.Stacks0387 F) :
    Function.Surjective (quotientMap E n) := quotientMap_surjective E n h0BTX h0387

end FiniteEtale

-- Product transitions have no positivity guard on either factor.
example (d : ℕ) [IsFinite (multiplication E d).left] [Etale (multiplication E d).left]
    [IsFinite (multiplication E (d * 0)).left] [Etale (multiplication E (d * 0)).left]
    (g : N E) :
    torsionReduction E d 0 (quotientMap E (d * 0) g) = quotientMap E d g :=
  quotientMap_reduction E d 0 g

example (d n : ℕ) [IsFinite (multiplication E d).left] [Etale (multiplication E d).left]
    [IsFinite (multiplication E n).left] [Etale (multiplication E n).left]
    (hd : 0 < d) (h : d ∣ n) (g : N E) :
    torsionLowering E d n h (quotientMap E n g) = quotientMap E d g :=
  quotientMap_lowering E d n hd h g
