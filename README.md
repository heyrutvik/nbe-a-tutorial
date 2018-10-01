# Normalization by Evaluation (NBE)

This repo contains a Scala port of the code that has been demonstrated in a [tutorial](http://davidchristiansen.dk/tutorials/nbe/) written by [David Christiansen](http://davidchristiansen.dk/). 


- [x] [Normalizing Untyped λ-Calculus](https://github.com/heyrutvik/nbe-a-tutorial/tree/master/src/main/scala/nbe/untyped)

- [x] [Typed Normalization by Evaluation](https://github.com/heyrutvik/nbe-a-tutorial/tree/master/src/main/scala/nbe/typed/simply)

- [x] [Type checking the Tartlet](https://github.com/heyrutvik/nbe-a-tutorial/tree/master/src/main/scala/nbe/typed/dependently), It's a tiny dependently-typed language (A Tiny Piece of [Pie](https://github.com/the-little-typer/pie))
    
    - [ ] bidirectional type checking rules for Tartlet
    
    #### Tartlet can be extended with a number of features: (as [listed](http://davidchristiansen.dk/tutorials/nbe/#%28part._.Projects%29) in tutorial)
    
    - [ ] Add a sum type, Either, with constructors left and right.
    
    - [ ] Add lists and vectors (length-indexed lists).
    
    - [ ] Add non-dependent function types and non-dependent pair types to the type checker. This should not require modifications to the evaluator.
    
    - [ ] Add functions that take multiple arguments, but elaborate them to single-argument Curried functions.
    
    - [ ] Add holes and/or named metavariables to allow incremental construction of programs/proofs.
    
    - [ ] Make the evaluation strategy lazy, either call-by-name or better yet call-by-need.
    
    - [ ] Replace U with an infinite number of universes and a cumulativity relation. To do this, type equality checks should be replaced by a subsumption check, where each type constructor has variance rules similar to other systems with subtyping.
