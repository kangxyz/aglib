/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.RepresentedKernel.CoverTerminalPullback

open AlgebraicGeometry.Scheme.EtaleCohomology.RepresentedKernel

/--
info: 'AlgebraicGeometry.Scheme.EtaleCohomology.RepresentedKernel.terminalMarkedKernelRowIso'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms terminalMarkedKernelRowIso

/--
info: 'AlgebraicGeometry.Scheme.EtaleCohomology.RepresentedKernel.terminalMarkedGraphBoundary_transport'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms terminalMarkedGraphBoundary_transport

/--
info: 'AlgebraicGeometry.Scheme.EtaleCohomology.RepresentedKernel.relativeCoverH1Pullback_terminal_of_eq'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms relativeCoverH1Pullback_terminal_of_eq
