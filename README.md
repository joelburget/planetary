# What is this?

An experimental programming language, built as a foundation for *other* programming languages. We borrow ideas from the blockchain world and semantics from

# The story so far

### First, start with a small core language

We choose [Core Frank](https://arxiv.org/abs/1611.09259) because:

* It's a small language with a formal semantics
* It has a notion of *ambient ability* which allows us to reason about the world our programs operate in
* It doesn't even have a built-in syntax

Because the core is very small, it can be easily implemented for any platform, exposing libraries and features of that platform while interoperating with the Planetary ecosystem.

It's not important to start with the *perfect* base. It is important for the base to be formally specified, extremely simple, and extensible.

### Make everything content-addressable

[IPFS](https://ipfs.io/)
[Unison](https://pchiusano.github.io/2015-04-23/unison-update7.html)

### Make the language extensible

We started with a small core but want to be able to use richer language features

Haskell's language pragma problem
Nix
Reliable builds

### Grow a community of languages

We envision an ecosystem of interoperable languages. A community of language experimentation. Haskell language pragmas or babel, but lighter-weight.

https://youtu.be/_ahvzDzKdB0

## Differences from Core Frank

We don't have an official syntax, however for testing we use a syntax similar to the one from the paper but more limited in some ways.

We add fixed points so we can typecheck inductive data.

We add a foreign value constructor.

Case terms hold the cid they scrutinize. TODO: why? couldn't this be removed?
