-- | Church encoded Freer monad
--
-- Based on Oleg's Freer Monad <http://okmij.org/ftp/Computation/free-monad.html> but Chruch encoded.
{-# language GADTs, RankNTypes #-}
module Control.Monad.Freer.Church (
  -- * Definition
  FFC (..)
  -- * Operations
  , eta
  , fpure
  , fimpure
  , foist
  , retractFFC
    -- * Proofs
    -- $proofs
  ) where

-- | The Church-encoded Freer 'Monad'.  For any @g@ (even if it isn't a 'Functor'!) @FFC g@ is a monad.
--
-- 
-- Think of 'FFC' as if it were like @Freer@
--
-- @
-- data Freer g a where
--   FPure   :: a -> Freer g a
--   FImpure :: g x -> (x -> Freer g a) -> Freer g a
-- @
newtype FFC g a =
  FFC { runFFC :: forall r . (a -> r) -> (forall x . g x -> (x -> r) -> r) -> r }

-- | It's a 'Functor' without a constraint on g
instance Functor (FFC g) where
  fmap f = \mf -> FFC (\pur imp -> runFFC mf (pur . f) imp)
  {-# INLINE fmap #-}

-- | Lift a pure value into the Freer monad
fpure :: a -> FFC g a
fpure = \a -> FFC (\pur _imp -> pur a)
{-# INLINE fpure #-}

-- | Given an operation in @g@ and a continuation returning a monadic
-- computation, sequence the continuation after the operation.
fimpure :: g x -> (x -> FFC g a) -> FFC g a
fimpure gx k = FFC (\pur imp -> imp gx (\x -> runFFC (k x) pur imp))
{-# INLINE fimpure #-}

-- | Embed an operation of 'g' into the monad
--
-- @
-- eta eff === fimpure eff fpure
-- @
eta :: g a -> FFC g a
eta = \eff -> FFC (\pur imp -> imp eff pur)
{-# INLINE eta #-}
-- proof:
--     eta eff
-- === FFC (\pur imp -> imp eff pur)                                                 by defn
-- === FFC (\pur imp -> imp eff (\x -> pur x))                                       by eta expansion
-- === FFC (\pur imp -> imp eff (\x -> runFFC (FFC (\pur' _ -> pur' x)) pur imp))    by defn & eta expansion
-- === FFC (\pur imp -> imp eff (\x -> runFFC (fpure x) pur imp))                    by defn
-- === fimpure eff fpure                                                             by defn

-- | It's an 'Applicative' without a constraint on g
instance Applicative (FFC g) where
  pure = fpure
  {-# INLINE pure #-}
  (<*>) = \mf mx -> FFC (\pur imp -> runFFC mf (\f -> runFFC mx (pur . f) imp) imp)
          -- \mf mx -> runFFC mf (runFFC mx (\x f -> (fpure (f x)))
          --                      (\gx k f -> fimpure gx (\x -> (k x f))))
          --          fimpure
  {-# INLINE (<*>) #-}


-- | And it's a 'Monad' without constraints on 'g'
instance Monad (FFC g) where
  return = fpure
  {-# INLINE return #-}
  (>>=) = \mx f -> FFC (\pur imp -> runFFC mx (\x -> runFFC (f x) pur imp) imp)
                   -- runFFC mx f fimpure
  {-# INLINE (>>=) #-}

-- | Lift a natural transformation in Hask to a natural transformation on the free monads.
foist :: (forall x . f x -> g x) -> FFC f a -> FFC g a
foist phi = \ma -> -- runFFC ma return (fimpure . phi)
              FFC (\pur imp -> runFFC ma pur (imp . phi))
{-# INLINE foist #-}

-- | If @m@ is a monad, we can interpret @FFC m@ in itself
retractFFC :: Monad m => FFC m a -> m a
retractFFC ma = runFFC ma return (>>=)
{-# INLINE retractFFC #-}
-- effects are interpreted as themselves:
--
-- @
-- retractFFC (eff ma) === ma
-- @
--
-- @
--     retractFFC (eff ma)
-- === runFFC (FFC (\pur imp -> imp ma pur) return (>>=))   by defns
-- === (>>=) ma return                                      by beta
-- === ma                                                   by right identity law
-- @
--
-- and its a monad homomorphism
--
-- @
-- retractFFC (return a) === return a
-- @
--
-- @
--     runFFC (FFC (\pur _ -> pur a)) return (>>=)   by defns
-- === return a                                      by beta
-- @
--
-- @
-- retractFFC (m >>= f) === retractFFC m >>= retractFFC . f
-- @
--
-- @
--     retractFFC (FFC (\pur imp -> runFFC m (\x -> runFFC (f x) pur imp) imp))            by defn (>>=)
-- === runFFC (FFC (\pur imp -> runFFC m (\x -> runFFC (f x) pur imp) imp)) return (>>=)   by defn retractFFC
-- === runFFC m (\x -> runFFC (f x) return (>>=)) (>>=)                                    by beta
-- ===
-- === ???
-- ===
-- === runFFC m return (>>=) >>= \x -> runFFC (f x) return (>>=)                           by defn retractFFC
--     retractFFC m >>= \x -> retractFFC (f x)
-- @
--
-- stuck here.

-- $proofs
--
-- == Functor law
--
-- It's a real functor.  (id law left as exercise)
--
-- === Composition
--
-- @fmap f . fmap g === fmap (f . g)@
--
-- @
--     fmap f (fmap g (FFC p))
-- === fmap f (FFC (\\pur imp -> p (pur . g) imp))                         by defn
-- === FFC (\\pur' imp' -> (\\pur imp -> p (pur . g) imp) (pur' . f) imp')  by defn
-- === FFC (\\pur' imp' -> p ((pur' . f) . g) imp')                        by beta
-- === FFC (\\pur' imp' -> p (pur' . (f . g)) imp')                        by assoc-compose
-- === fmap (f . g) (FFC p)                                               by defn
-- @
--
-- == Applicative Laws
--
-- === Identity
-- @
-- pure id \<*\> v === v
-- @
--
-- @
--     pure id \<*\> (FFC vp)
-- === (FFC (\\pur _ -> pur id)) \<*\> (FFC vp)                                    by defn pure
-- === FFC (\\pur' imp' -> (\\pur _ -> pur id) (\\f -> vp (pur' . f) imp') imp')   by defn (\<*\>)
-- === FFC (\\pur' imp' -> (\\f -> vp (pur' . f) imp') id)                        by beta
-- === FFC (\\pur' imp' -> vp (pur' . id) imp')                                  by beta
-- === FFC (\\pur' imp' -> vp pur' imp')                                         by compose-id
-- === FFC vp                                                                   by eta
-- @
--
-- === Homomorphism
--
-- @
-- pure f \<*\> pure x === pure (f x)
-- @
--
-- @
--     pure f <*> pure x
-- === FFC (\\pur _ -> pur f) <*> FFC (\\pur' _-> pur' x)                                                by defn
-- === FFC (\\pur'' imp'' -> (\\pur _ -> pur f) (\\h -> (\\pur' _ -> pur' x) (pur'' . h) imp'') imp'')   by defn
-- === FFC (\\pur'' imp'' -> (\\h -> (\\pur' -> pur' x) (pur'' . h) imp'') f)                           by beta
-- === FFC (\\pur'' imp'' -> (\\pur' _ -> pur' x) (pur'' . f) imp'')                                   by beta
-- === FFC (\\pur'' imp'' -> (pur'' . f) x)                                                           by beta
-- === FFC (\\pur'' _ -> pur'' (f x))                                                                 by defn-compose
-- === pure (f x)                                                                                    by defn
-- @
--
-- === Interchange
--
-- @
-- u \<*\> pure y === pure (\\k -> k y) \<*\> u
-- @
--
-- @
--     FFC ru \<*\> FFC (\\pur _ -> pur y)                                                   by defn
-- === FFC (\\pur' imp' -> ru (\\u -> (\\pur _ -> pur y) (pur' . u) imp') imp')              by defn
-- === FFC (\\pur' imp' -> ru (\\u -> (pur' . u) y) imp')                                   by beta
-- === FFC (\\pur' imp' -> ru (\\u -> pur' (u y)) imp')                                     by beta
-- === FFC (\\pur' imp' -> ru (\\u -> pur' ((\\k -> k y) u)) imp')                           by beta
-- === FFC (\\pur' imp' -> ru (\\u -> (pur' . (\\k -> k y)) u) imp')                         by defn-compose
-- === FFC (\\pur' imp' -> ru (pur' . (\\k -> k y)) imp')                                   by eta
-- === FFC (\\pur' imp' -> (\\f -> ru (pur' . f) imp') (\\k -> k y))                         by beta
-- === FFC (\\pur' imp' -> (\\pur _ -> pur (\\k -> k y)) (\\f -> ru (pur' . f) imp') imp')    by defn
-- === FFC (\\pur _ -> pur (\\k -> k y)) \<*\> FFC ru
-- @
--
-- === Composition
--
-- @
-- pure compose \<*\> u \<*\> v \<*\> w === u \<*\> (v \<*\> w)
-- @
--
-- Please send a Pull Request.  (Proof seems straightforward, but tedious)
--
--
-- == Monad Laws
-- 
-- === Left Identity
--
-- @
-- return a >>= f === f a
-- @
--
-- @
--     FFC (\\pur' _ -> pur' a) >>= f
-- === FFC (\\pur imp -> (\\pur' _ -> pur' a) (\\x -> runFFC (f x) pur imp) imp)   by defn
-- === FFC (\\pur imp -> (\\x -> runFFC (f x) pur imp) a)                         by beta
-- === FFC (\\pur imp -> runFFC (f a) pur imp)                                   by beta
-- === FFC (runFFC (f a))                                                       by eta
-- === f a                                                                      by eta
-- @
--
--
-- === Right Identity
-- 
-- @
-- (FFC mp) >>= return === (FFC mp)
-- @
-- 
-- @
--     FFC mp >>= (\\x -> FFC (\\pur' _ -> pur' x))                                            by defn
-- === FFC (\\pur imp -> mp (\\a -> runFFC ((\\x -> FFC (\\pur' _ -> pur' x)) a) pur imp) imp)   by defn
-- === FFC (\\pur imp -> mp (\\a -> runFFC (FFC (\\pur' _ -> pur' a)) pur imp) imp)             by beta
-- === FFC (\\pur imp -> mp (\\a -> pur a) imp)                                                by beta
-- === FFC (\\pur imp -> mp pur imp)                                                          by eta
-- === FFC mp                                                                                by eta
-- @
--
--
-- === Associativity
--
-- @
-- (FFC mp >>= f) >>= g === (FFC mp) >>= (\\x -> f x >>= g)
-- @
--
-- @
--     FFC (\\pur imp -> runFFC (FFC mp >>= f) (\\a -> runFFC (g a) pur imp) imp)                                                 by defn (>>=) outer
-- === FFC (\\pur imp -> runFFC (FFC (\\pur' imp' -> mp (\\b -> runFFC (f b) pur' imp') imp')) (\\a -> runFFC (g a) pur imp) imp)   by defn (>>= inner)
-- === FFC (\\pur imp -> mp (\\b -> runFFC (f b) (\\a -> runFFC (g a) pur imp)) imp)                                               by beta
-- === FFC (\\pur imp -> mp (\\b -> runFFC (FFC (\\pur' imp' -> runFFC (f b) (\\a -> runFFC (g a) pur' imp') imp')) pur imp) imp)   by beta
-- === FFC (\\pur imp -> mp (\\b -> runFFC (f b >>= g) pur imp) imp)                                                              by defn
-- === FFC (\\pur imp -> mp (\\b -> runFFC ((\\z -> f z >>= g) b) pur imp) imp)                                                    by beta
-- === FFC mp >>= (\\z -> f z >>= g)                                                                                             by defn
-- @
