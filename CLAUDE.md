# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Build and Development Commands

### Building
- `make` or `make category-theory`: Build the entire library
- `make -j4`: Build with 4 parallel jobs for faster compilation
- `nix build`: Build using Nix (supports multiple Coq versions 8.14-8.20)
- `nix build .#packages.x86_64-darwin.category-theory_8_20`: Build for specific Coq version

### Make Targets
- `make clean`: Clean build artifacts
- `make fullclean`: Clean all generated files including Makefile.coq
- `make install`: Install the library
- `make todo`: Check for TODOs, admits, undefined, etc. in the codebase
- `make minimize-requires`: Minimize require statements (requires coq-tools)

### Testing/Validation
- `make`: Comprehensive test script that builds against multiple Coq versions in parallel
- The library uses OPAM for dependency management with `coq-equations` as the main dependency

## Architecture Overview

This is a comprehensive formalization of category theory in Coq, structured as a library for both theoretical study and practical application in programming.

### Core Structure
- **Theory/**: Fundamental category theory definitions (categories, functors, natural transformations, adjunctions, etc.)
- **Structure/**: Internal categorical structures (limits, colimits, monoidal structures, cartesian closed categories)
- **Construction/**: Methods for building new categories from existing ones (product, comma, slice categories)
- **Instance/**: Concrete category instances (Set, Coq types, posets, etc.)
- **Functor/**: Various species of functors with specific properties
- **Lib/**: Library foundations with custom setoid definitions and tactics
- **Solver/**: Computational category theory solver for automated proofs

### Key Design Principles
- **Axiom-free**: No axioms used in core theory
- **Type-based**: All definitions in `Type`, avoiding `Prop` except for specific instances
- **Computational setoids**: Uses homsetoids (`crelation`) rather than standard equality
- **Duality-aware**: Dual constructions satisfy "dual of dual = original" by reflexivity
- **Universe polymorphic**: Supports multiple universe levels

### Programming Sub-library
The `Theory/Coq/` directory contains an applied category theory library for Coq programming:
- Provides lawful instances of Functor, Applicative, Monad, etc.
- Laws are proven by mapping to general categorical definitions rather than direct proof
- Leverages the broader category theory library for automatic law verification

### Entry Points
- `Require Import Category.Theory.`: Primary import for basic category theory
- `Require Import Category.Lib.`: Core library foundations
- `Require Import Category.Solver.`: Computational solver for categorical equations

### Notation System
Extensive use of Unicode operators:
- `≈`: Equivalence (primary relation, not equality)
- `≅`: Isomorphism  
- `~>`: Morphisms
- `⟶`: Functors
- `⟹`: Natural transformations
- Various composition operators: `∘` (morphisms), `○` (functors), `∙` (natural transformations)

### Development Tips
- The library expects `coq-equations` plugin for recursive definitions
- Build system generates `Makefile.coq` from `_CoqProject`
- All files are organized under the `Category` namespace (`-R . Category`)
- Use `make todo` to find incomplete proofs or definitions
