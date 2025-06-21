/-
Copyright (c) 2024 Jonathan Washburn. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Jonathan Washburn
-/

/-!
# Navier-Stokes Global Regularity

This module contains the complete formalization of global regularity
for the 3D incompressible Navier-Stokes equations.

## Main Components

- `NavierStokes.Constants`: All numerical constants from Recognition Science
- `NavierStokes.BasicDefinitions`: Velocity fields, vorticity, weak solutions
- `NavierStokes.GeometricDepletion`: Constantin-Fefferman depletion principle
- `NavierStokes.VorticityBound`: Universal scale-invariant bounds
- `NavierStokes.GlobalRegularity`: Main theorem combining all components

## Main Result

The global regularity theorem states that for any smooth divergence-free
initial data, there exists a unique global smooth solution.
-/

import NavierStokes.Constants
import NavierStokes.BasicDefinitions
import NavierStokes.GeometricDepletion
import NavierStokes.VorticityBound
import NavierStokes.GlobalRegularity
