# Supported Rust Features

Quick reference for supported Rust features. Note that this list does not include all Verus features, and Verus has many spec/proof features without any standard Rust equivalent—this list only concerns Rust features. See [the guide](https://verus-lang.github.io/verus/guide/modes.html) for more information about Verus' distinction between executable Rust code, specification code, and proof code.

Note that Verus is in active development. If a feature is unsupported, it might be genuinely hard, or it might just be low priority. See the [github issues](https://github.com/verus-lang/verus/issues) or [discussions](https://github.com/verus-lang/verus/discussions) for information on planned features.

Last Updated: 2026-02-18

## Functions and Types

| Feature | Status |
|---------|--------|
| Functions, methods, associated functions | Supported |
| Associated constants | Partially supported |
| Structs | Supported |
| Enums | Supported |
| Const functions | Partially supported |
| Async functions | Not supported |
| Macros | Supported |
| Type aliases | Supported |
| Const items | Partially supported |
| Static items | Partially supported |

## Generics and Declarations

| Feature | Status |
|---------|--------|
| Type parameters | Supported |
| Where clauses | Supported |
| Lifetime parameters | Supported |
| Const generics | Partially Supported |
| Custom discriminants | Supported |
| public / private fields | Partially supported |

## Expressions and Statements

| Feature | Status |
|---------|--------|
| Variables, assignment, mut variables | Supported |
| If, else | Supported |
| patterns, match, if-let, match guards | Supported |
| Block expressions | Supported |
| Items | Not supported |
| loop, while | Supported |
| for | Partially supported |
| ? | Supported |
| Async blocks | Not supported |
| await | Not supported |
| Unsafe blocks | Supported |
| & | Supported |
| &mut, place expressions | Partially supported |
| ==, != | Supported |
| Type cast (as) | Partially supported |
| Compound assignments (+=, etc.) | Supported |
| Array expressions | Partially supported (no fill expressions with `const` arguments) |
| Range expressions | Supported |
| Index expressions | Partially supported |
| Tuple expressions | Supported |
| Struct/enum constructors | Supported |
| Field access | Supported |
| Function and method calls | Supported |
| Closures | Supported |
| Labels, break, continue | Supported |
| Return statements | Supported |

## Arithmetic and Bitwise

| Feature | Status |
|---------|--------|
| Arithmetic for unsigned | Supported |
| Arithmetic for signed | Supported |
| Bitwise operations (&, \|, !, >>, <<) | Supported |
| Arch-dependent types (usize, isize) | Supported |

## Types

| Feature | Status |
|---------|--------|
| Integer types | Supported |
| bool | Supported |
| Strings | Supported |
| Vec | Supported |
| Option / Result | Supported |
| Floating point | Partially supported |
| Slices | Supported |
| Arrays | Supported |
| Pointers | Partially supported |
| References (&) | Supported |
| Mutable references (&mut) | Partially supported |
| Never type | Supported |
| Function pointer types | Not supported |
| Closure types | Supported |
| Trait objects (dyn) | Partially supported |
| impl types | Partially supported |

## Standard Library

| Feature | Status |
|---------|--------|
| Cell, RefCell | Not supported (see vstd alternatives) |
| Iterators | Partially supported |
| Vec, HashMap, HashSet, VecDeque | Supported |
| Smart pointers (Box, Rc, Arc) | Supported |
| Pin | Not supported |
| Hardware intrinsics | Not supported |
| Printing, I/O | Not supported |
| Panic-unwinding | Partially supported |

## Traits

| Feature | Status |
|---------|--------|
| User-defined traits | Supported |
| Default implementations | Supported |
| Trait bounds on trait declarations | Supported |
| Traits with type arguments | Supported |
| Associated types | Supported |
| Generic associated types | Partially supported (only lifetimes are supported) |
| Higher-ranked trait bounds | Supported |
| Marker traits (Copy, Send, Sync) | Supported |
| Standard traits (Clone, Default, Step, From, TryFrom, Into, PartialEq, Eq, PartialOrd, Ord, Neg, Not, Add, Sub, Mul, Div, Rem, BitAnd, BitOr, BitXor, Shl, Shr) | Partially supported |
| Standard traits (Debug, serde::Serialize) | Not supported |
| User-defined destructors (Drop) | Not supported |
| Sized (size_of, align_of) | Supported |
| Deref | Supported |
| DerefMut | Not supported |

## Concurrency

| Feature | Status |
|---------|--------|
| Mutex, RwLock (from standard library) | Not supported |
| Verified lock implementations | Supported |
| Atomics | Supported (vstd equivalent) |
| spawn and join | Supported |
| Interior mutability | Supported |

## Unsafe and Low-level

| Feature | Status |
|---------|--------|
| Raw pointers | Partially supported |
| Transmute | Not supported |
| Unions | Supported |
| UnsafeCell | Supported (vstd equivalent) |

## Project Structure

| Feature | Status |
|---------|--------|
| Multi-crate projects | Partially supported |
| Verified crate + unverified crates | Partially supported |
| Modules | Supported |
| rustdoc | Supported |
