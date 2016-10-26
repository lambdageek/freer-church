= Church-encoded Freer Monad =

This Oleg's [Freer monad](http://okmij.org/ftp/Computation/free-monad.html) but Church-encoded.

- Because it's the Freer monad, `FFC g` is a Monad for any `g` even if it isn't a functor.
- Because it's Church-encoded, it reassociates left-nested binds: `(m >>= f) >>= g` immediately reassociates to `m >>= \x -> f x >>= g`
