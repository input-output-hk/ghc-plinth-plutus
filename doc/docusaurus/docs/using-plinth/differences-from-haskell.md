---
sidebar_position: 15
---

# Differences From Haskell

Plinth is a subset of Haskell.
The Plinth compiler translates GHC Core into Untyped Plutus Core (UPLC), the language that runs on-chain.
UPLC is a small, strict lambda calculus with a fixed set of builtin types and functions.
Every node in the network evaluates the same script and must get bit-identical results, within a fixed execution budget.
These properties cause most differences between Plinth and Haskell: some Haskell features have no UPLC counterpart, and some would break determinism or predictable costs.

This chapter describes the differences, the error message that each unsupported feature triggers, and the reason why the feature is unsupported.

## Strictness

### Function Applications

Unlike in Haskell, function applications in Plinth are strict.
In other words, when evaluating `(\x -> 42) (3 + 4)` the expression `3 + 4` is evaluated first, before evaluating the function body (`42`), even though `x` is not used in the function body.

Using lazy patterns on function parameters does not change this behavior: `(\(~x) -> 42) (3 + 4)` still evaluates `3 + 4` strictly.
At this time, it is not possible to make function applications non-strict in Plinth.

### Bindings

Bindings in Plinth are by default non-strict, but they can be made strict via the bang pattern (`!`), as in `let !x = 3 + 4 in 42`.
Conversely, in modules with the `Strict` language extension on, bindings are by default strict, but they can be made non-strict via the lazy pattern (`~`), as in `let ~x = 3 + 4 in 42`.

> :pushpin: **NOTE**
>
> It is important to note that the UPLC evaluator does not perform lazy evaluation, which means a non-strict binding will be evaluated each time it is used, rather than at most once.

## Supported Haskell Features

The Plinth compiler provides good support for basic Haskell features, including regular algebraic data types, type classes, higher order functions, parametric polymorphism, etc.
However, it doesn't support many of Haskell's more advanced features.
A good rule of thumb for writing Plinth is to stick with simple Haskell (which is also typically good advice for Haskell development in general).

Most functions and methods from [`base`](https://hackage.haskell.org/package/base) are not usable in Plinth.
Use the counterparts from the [`plutus-tx`](https://plutus.cardano.intersectmbo.org/haddock/latest/plutus-tx/) library instead: they are written to compile to efficient UPLC.
This also means most Haskell third-party libraries are not supported, unless the library is developed specifically for Plinth.

## How Unsupported Features Are Reported

The compiler reports an error when the compiled code uses an unsupported feature.
The error has a source location, a `PLINTH` error code, the reason, and often a suggestion:

```
HaskellEq.hs:9:10: error: [PLINTH-00004]
    Plinth Compilation Error:
    Context: Compiling code at HaskellEq.hs:9:10-62:
             GHC.Num.Integer.integerEq
    Error: Unsupported feature: GHC.Classes.Eq.==, use PlutusTx.Eq.Eq
  |
9 | code = $$(PlutusTx.compile [|| \x -> x == (42 :: Integer) ||])
  |          ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
```

The `Context:` lines show the chain of code the compiler was processing, innermost last.
They show GHC Core, the intermediate language the compiler works on, so the code can look different from your source.

The error codes are:

| Code           | Meaning                                                     |
|----------------|-------------------------------------------------------------|
| `PLINTH-00001` | Error from the Plutus Core compiler                         |
| `PLINTH-00002` | Error from the PIR compiler                                 |
| `PLINTH-00003` | Internal error; please report it to the Plutus team         |
| `PLINTH-00004` | Unsupported feature                                         |
| `PLINTH-00005` | Reference to a name without an accessible definition        |
| `PLINTH-00006` | Misused compiler marker                                     |
| `PLINTH-00007` | Internal name lookup error; please report it                |

The plugin option `-fplugin-opt Plinth.Plugin:preserve-source-locations` makes locations more precise: the compiler then tracks the locations of variables, class methods and literals through the compilation, at a small compile-time cost.

The Plinth compiler runs after GHC's type checker, so an IDE that only type-checks the code does not show these errors.
Compile the module to find them.

## Unsupported Features

Each section below names a feature, shows the error it triggers, and explains why Plinth does not support it.

### Machine integers: Int, Word, Word8, ..., Word64

```
Error: Unsupported feature: Int: use Integer instead
```

UPLC has one integer type: `Integer`, with arbitrary precision.
Fixed-width types silently wrap around on overflow, which is dangerous in contract code that moves funds.
Use `Integer`.

### Floating point: Double, Float

```
Error: Unsupported feature: Type GHC.Types.Double is not supported in Plinth; use Integer or PlutusTx.Ratio.Rational instead
```

UPLC has no floating-point builtins.
Floating-point results can differ between platforms and optimization levels, while every node must compute exactly the same result.
Use `Integer`, or `PlutusTx.Ratio.Rational` for exact fractions.

### Characters and String literals

```
Error: Unsupported feature: Literal string (maybe you need to use OverloadedStrings)
Error: Unsupported feature: Literal char
```

Haskell's `String` is a linked list of `Char`, and UPLC has no `Char` type.
Text on-chain is one builtin type: `BuiltinString`.
Enable `OverloadedStrings` and use `BuiltinString`, mainly for trace messages.
Use `BuiltinByteString` for data.

### Data.Text and Data.ByteString

```
Error: Unsupported feature: Type Data.Text.Internal.Text is not supported in Plinth; use BuiltinString instead
Error: Unsupported feature: Type Data.ByteString.Internal.Type.ByteString is not supported in Plinth; use BuiltinByteString instead
```

These types wrap memory buffers managed by the GHC runtime, which does not exist on-chain.
The builtin types `BuiltinString` and `BuiltinByteString` are their on-chain equivalents.

### Type classes from base: Eq, Ord, Show, Enum

```
Error: Unsupported feature: GHC.Classes.Eq.==, use PlutusTx.Eq.Eq
Error: Unsupported feature: GHC.Show.Show.show, use PlutusTx.Show.Show
```

The `base` instances of these classes are compiled for the GHC runtime: they operate on machine integers, produce `String` values, and usually ship without the definitions the Plinth compiler needs (see [Functions without unfoldings](#functions-without-unfoldings)).
The `plutus-tx` library defines on-chain versions of these classes (`PlutusTx.Eq`, `PlutusTx.Ord`, `PlutusTx.Show`, `PlutusTx.Enum`) whose methods compile to builtin operations.
Import `PlutusTx.Prelude` instead of the Haskell `Prelude` to get them.

### Range syntax

```
Error: Unsupported feature: Range syntax, use PlutusTx.Enum.enumFromTo or PlutusTx.Enum.enumFromThenTo
Error: Unsupported feature: Unbounded range syntax: unbounded ranges are not supported
```

`[a .. b]` is sugar for methods of the `base` `Enum` class, which is unsupported (see above).
Use `PlutusTx.Enum.enumFromTo` or `PlutusTx.Enum.enumFromThenTo`, and note that they build the full list, which costs budget proportional to its length.
Unbounded ranges such as `[a ..]` describe infinite lists.
UPLC evaluation is strict and budgeted, so an infinite structure can never be fully evaluated; there is no useful way to compile one.

### error and undefined from Prelude

```
Error: Unsupported feature: GHC.Err.error, use PlutusTx.Prelude.error or PlutusTx.Prelude.traceError
```

`Prelude.error` takes a `String` message and an implicit call stack, and raises a Haskell runtime exception.
None of these exist on-chain: script failure is the UPLC `error` term, and messages are trace strings.
Use `PlutusTx.Prelude.error`, or `PlutusTx.Prelude.traceError` to attach a message.

### IO and FFI

```
Error: Unsupported feature: IO actions are not supported in Plinth
```

A script is a pure function.
Every node re-evaluates it, possibly years later, and must get the same result; there is no runtime system on-chain to perform effects.
Compute effects off-chain and pass the results to the script as arguments.

### Pattern matching on Integer literals

```
Error: Unsupported feature: Cannot pattern match on a value of type 'Integer'.
```

Pattern matching compiles to case analysis on data constructors, and the builtin `Integer` type has no constructors: GHC desugars a literal pattern like `f 42 = ...` into matches on the internal representation of `Integer`, which exposes machine words.
Use equality from `PlutusTx.Prelude` with guards instead:

```haskell
f n | n == 42   = ...
    | otherwise = ...
```

GHC optimizations can also generate such matches from innocent code; the full error message lists the GHC flags that prevent this.

### Recursive newtypes

```
Error: Unsupported feature: Recursive newtypes, use data: MyModule.Stream
```

A newtype compiles to a transparent type alias, so it has no runtime cost.
A recursive alias would unfold forever.
A `data` type compiles to a real datatype, which supports recursion; use `data` for recursive types.

### Mutually recursive data types

```
Error: Error from the PIR compiler:
       Unsupported construct: Mutually recursive datatypes: Forest, Rose ({ MutualData.hs:9:1-9:27 })
```

The intermediate language (PIR) encodes a recursive datatype as a fixed point of a single type.
There is no encoding for a group of types that recurse through each other yet.
Merge the group into a single datatype, or break the cycle by inlining one type into the other.

### Existential types and GADTs

```
Error: Unsupported feature: Existential quantification in data constructor MyModule.Box
Error: Unsupported feature: Following extensions are not supported: GADTs
```

PIR datatypes are plain sums of products: constructors take value arguments whose types only mention the datatype's own type parameters.
A constructor cannot bind its own type variables (existentials) or refine the result type (GADTs), because the datatype encoding has no representation for either.
The `GADTs` extension is rejected as a whole in modules that contain compiled code.

### Type families

```
Error: Unsupported feature: Irreducible type family application: MyModule.F
```

PIR has no type-level computation.
A type family application compiles only when GHC fully reduces it during type checking; an application that remains (for example, an open family with no matching instance) cannot be translated.

### Kind polymorphism (PolyKinds)

```
Error: Unsupported feature: Following extensions are not supported: PolyKinds
```

PIR kinds are `*` and arrow kinds only; there are no kind variables.

### Functions without unfoldings

```
Error: Reference to a name which is not a local, a builtin, or an external INLINABLE function: Variable MyModule.opaque
       No unfolding
```

The compiler translates the GHC Core definition (the "unfolding") of every function the compiled code uses.
GHC only stores unfoldings in interface files under certain conditions, so a function from another module may arrive without one.
Mark the function `INLINABLE` and compile with the flags listed in [GHC Extensions, Flags and Pragmas](./extensions-flags-pragmas.md).
See also the [Troubleshooting](../troubleshooting.md) page.
