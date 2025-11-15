# CLAUDE.md

This codebase is a comprehensive formalization of category theory in Coq/Rocq. It contains 1,603 proof files with 225,209 lines implementing core categorical concepts with zero axioms in the core theory.

## Commands

### Building the Library

```bash
# Build the entire library (default: Rocq 9.1)
make

# Build for specific version (if using Nix)
nix-shell -p coqPackages_9_1.coq --run make

# Build using Nix flake
nix build .#category-theory

# Clean build artifacts
make clean
make fullclean  # removes Makefile.coq as well

# Install library
make install

# Check for admitted proofs or TODOs
make todo
```

### Single File Development

```bash
# Compile a single file
coqc -R . Category Theory/Category.v

# Interactive development (in coqide/vscoq)
# Ensure _CoqProject is loaded with: -R . Category
```

### Proof Development Patterns

The library uses custom tactics in `Lib/Tactics.v`:
- `cat` - standard simplification for category proofs
- `cat_simpl` - more aggressive simplification with program obligations
- `proper` - for proving morphism respectfulness
- `equivalence` - for proving equivalence relations

## Architecture

### Core Abstraction Hierarchy

The library implements category theory through **setoid-based morphisms** where morphisms form equivalence classes rather than using strict equality. This fundamental design choice cascades through the entire architecture:

```
Category (homsets are setoids with ≈ equivalence)
    ↓
Functor (preserves equivalence, not just equality)
    ↓
Natural Transformation (naturality respects ≈)
    ↓
Adjunction/Monad/Kan Extension
```

### Universe Polymorphism Strategy

The library uses three universe parameters `{o h p}` throughout:
- `o` - objects universe level
- `h` - hom-sets universe level
- `p` - proof/proposition universe level
- Constraint: `h <= p` ensures morphism proofs can reference morphisms

This allows categories of categories at any level without universe inconsistencies.

### Duality Architecture

**Key insight**: Duality is built into definitions so `C^op^op = C` by reflexivity.

This requires symmetric laws in core definitions:
- `comp_assoc` AND `comp_assoc_sym` in Category
- `naturality` AND `naturality_sym` in Natural transformations

Benefits:
- Comonads are one line: `Definition Comonad := @Monad (C^op) (M^op)`
- Dual proofs are often automatic
- No code duplication for dual concepts

### Proof Obligation Management

The library uses Coq's Program mechanism extensively:
1. Definitions use `Program Instance` to defer proof obligations
2. `Obligation Tactic := cat_simpl` automates most proofs
3. Remaining obligations proven with specific tactics
4. This separates mathematical content from proof details

### Instance Resolution Strategy

Categories are discovered through:
1. Type classes for concepts (Category, Functor, etc.)
2. `Existing Instance` for conditional instances
3. Notation-driven inference with category hints
4. Explicit category parameters when inference fails

Example: `f ∘[C] g` specifies category C when needed.

## Key Files and Concepts

### Theory Core
- **Theory/Category.v**: Defines categories with setoid hom-sets
- **Theory/Functor.v**: Functors preserve equivalence
- **Theory/Natural/Transformation.v**: Natural transformations
- **Theory/Adjunction.v**: The most important concept - adjunctions
- **Theory/Monad.v**: Monads as endofunctors with structure
- **Theory/Kan/Extension.v**: Universal property of Kan extensions

### Structures (Internal Properties)
- **Structure/Cartesian.v**: Products via universal property
- **Structure/Closed.v**: Exponentials and internal hom
- **Structure/Monoidal.v**: Tensor products with coherence
- **Structure/Limit.v**: Limits and colimits

### Constructions (External Combinators)
- **Construction/Opposite.v**: Op categories with auto-duality
- **Construction/Product.v**: Product categories C × D
- **Construction/Comma.v**: Comma categories (F ↓ G)
- **Construction/Slice.v**: Slice C/c and coslice c/C

### Concrete Instances
- **Instance/Sets.v**: Category of setoids (not strict sets!)
- **Instance/Coq.v**: Category of Coq types and functions
- **Instance/Cat.v**: Category of categories
- **Instance/Fun.v**: Functor categories [C, D]
- **Instance/Lambda/**: Full lambda calculus formalization

### Applied Programming (Theory/Coq/)
Bridges pure theory with practical Coq programming:
- Applicative functors proven via monoidal functors
- Traversable functors with laws
- Monad transformers with coherence conditions

## Critical Design Patterns

### Equivalence Over Equality
Never use `=` for morphisms. Always use `≈`:
```coq
(* WRONG *)
Lemma foo : f ∘ id = f.

(* RIGHT *)
Lemma foo : f ∘ id ≈ f.
```

### Proper Morphisms
All operations must respect equivalence:
```coq
Program Instance Foo_Proper {C : Category} :
  Proper (equiv ==> equiv ==> equiv) (@foo C).
```

### Notation Precedence
- `~>` morphisms (level 90)
- `∘` composition (level 40, left associative)
- `⟶` functors between categories
- `⟹` natural transformations

### Proof Automation
Standard proof pattern:
```coq
Proof.
  intros.
  cat.          (* tries simplification + rewriting *)
  proper.       (* if proving Proper *)
  equivalence.  (* if proving Equivalence *)
Qed.
```

## Common Development Tasks

### Adding a New Category Instance
1. Define objects and morphisms
2. Define equivalence relation on morphisms (setoid)
3. Prove it forms a category (id, compose, laws)
4. Place in Instance/ directory
5. Add to _CoqProject

### Proving Functoriality
1. Define object mapping F_obj
2. Define morphism mapping F_map
3. Prove F_map respects equivalence
4. Prove F preserves id and composition
5. Use `Program Instance` to manage obligations

### Establishing Adjunctions
1. Define functors F : C ⟶ D and G : D ⟶ C
2. Define unit η : Id ⟹ G ○ F
3. Define counit ε : F ○ G ⟹ Id
4. Prove triangle identities
5. Or use hom-set adjunction definition

## References and Learning

When working with specific concepts, reference:
- **nLab**: https://ncatlab.org/nlab/show/[concept_name]
- **README.md**: Contains detailed notation guide (lines 193-247)
- **EXPLORATION_INDEX.md**: Quick navigation to key files
- **EXPLORATION_SUMMARY.md**: Mathematical concept guide

## Versioning

Default version: Rocq 9.1 (flake.nix line 187)
Supported: Coq 8.14-8.20, Rocq 9.0-9.1
Equations dependency required for some parts (versions matched to Coq)

## Testing Individual Theorems

To test a specific construction:
```bash
# Extract just the files needed
coqdep -R . Category Theory/MyConstruction.v | grep -v "^#"

# Compile dependencies first
make Theory/Category.vo Theory/Functor.vo

# Then compile your file
coqc -R . Category Theory/MyConstruction.v
```