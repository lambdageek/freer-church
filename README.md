# Church-encoded Freer Monad #

This Oleg's [Freer monad](http://okmij.org/ftp/Computation/free-monad.html) but Church-encoded.

- Because it's the Freer monad, `FFC g` is a Monad for any `g` even if it isn't a functor.
- Because it's Church-encoded, it reassociates left-nested binds: `(m >>= f) >>= g` immediately reassociates to `m >>= \x -> f x >>= g`


## It's just continuations ##

Start with Oleg's "Freer monad"

```haskell
data Freer g a where
  FPure   :: a -> Freer g a
  FImpure :: g x -> (x -> Freer g a) -> Freer g a
```

Church encode it to get

```haskell
data FFC g a =
  FFC { unFFC :: forall r . (a -> r) -> (forall x . g x -> (x -> r) -> r) -> r }
```

Now flip the two arguments around and note that <code>[Cont](http://hackage.haskell.org/package/transformers-0.5.2.0/docs/Control-Monad-Trans-Cont.html#t:Cont) t b = (b -> t) -> t</code>

```haskell
data FFC g a =
  FFC { unFFC :: forall r . (forall x . g x -> Cont r x) -> Cont r a }
```

So, the Freer monad is just an interpreter for 'g' into the continuation monad.
