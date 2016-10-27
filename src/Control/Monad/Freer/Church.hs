-- | Church encoded Freer monad
--
-- Based on Oleg's Freer Monad <http://okmij.org/ftp/Computation/free-monad.html> but Chruch encoded.
{-# language GADTs, RankNTypes #-}
module Control.Monad.Freer.Church (
  -- * Derivation
  -- $derivation
  
  -- * Definition
  FFC (..)
  , FFCT (..)
  -- * Operations
  , eta
  , eta'
  , fpure
  , fpure'
  , fimpure
  , fimpure'
  , foist
  , foistT
  , retractFFC
  , retractFFCT
    -- * Proofs
    -- $proofs
  ) where

import Control.Monad.Trans.Cont
import Control.Monad.Trans.Class

-- $derivation
--
-- Start with Oleg's "Freer monad"
--
-- @
-- data Freer g a where
--   FPure   :: a -> Freer g a
--   FImpure :: g x -> (x -> Freer g a) -> Freer g a
-- @
--
-- Church encode it to get
--
-- @
-- data FFC g a =
--   FFC { unFFC :: forall r . (a -> r) -> (forall x . g x -> (x -> r) -> r) -> r }
-- @
--
-- Now flip the two arguments around and note that @'Cont' t b = (b -> t) -> t@
--
-- @
-- data FFC g a =
--   FFC { unFFC :: forall r . (forall x . g x -> Cont r x) -> Cont r a }
-- @
--
-- So, the Freer monad is just an interpreter for 'g' into the continuation monad.

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
  FFC { unFFC :: forall r . (forall x . g x -> Cont r x) -> Cont r a }

-- | Freer monad transformer.
--
-- Unfolding the definition of 'ContT' this type is precisely <https://hackage.haskell.org/package/free/docs/Control-Monad-Trans-Free-Church.html#t:FT FT>
--
newtype FFCT g m a =
  FFCT { unFFCT :: forall r . (forall x . g x -> ContT r m x) -> ContT r m a}

runFFC :: FFC g a -> (a -> r) -> (forall x . g x -> (x -> r) -> r) -> r
runFFC ma pur imp = runCont (unFFC ma (cont . imp)) pur

runFFCT :: Monad m => FFCT g m a -> (a -> m r) -> (forall x . g x -> (x -> m r) -> m r) -> m r
runFFCT tma mpur mimp = runContT (unFFCT tma (ContT . mimp)) mpur

-- | It's a 'Functor' without a constraint on g
instance Functor (FFC g) where
  fmap f = \ma -> FFC (\imp -> fmap f (unFFC ma imp))
  {-# INLINE fmap #-}

instance Functor (FFCT g m) where
  fmap f = \tma -> FFCT (\mimp -> fmap f (unFFCT tma mimp))

-- | Lift a pure value into the Freer monad
fpure :: a -> FFC g a
fpure = \a -> FFC (\imp -> pure a)
{-# INLINE fpure #-}

-- | Lift a pure value into a Freer monad transformer
fpure' :: a -> FFCT g m a
fpure' = \a -> FFCT (\mimp -> pure a)
{-# INLINE fpure' #-}

-- | Given an operation in @g@ and a continuation returning a monadic
-- computation, sequence the continuation after the operation.
fimpure :: g x -> (x -> FFC g a) -> FFC g a
fimpure = \gx k -> FFC (\imp -> (imp gx) >>= \x -> unFFC (k x) imp)
{-# INLINE fimpure #-}

-- | Sequence an operation in @g@ to be followed by the continuation.
fimpure' :: g x -> (x -> FFCT g m a) -> FFCT g m a
fimpure' = \ gx k -> FFCT (\mimp -> (mimp gx) >>= \x -> unFFCT (k x) mimp)

-- | Embed an operation of 'g' into the monad
--
-- @
-- eta eff === fimpure eff fpure
-- @
eta :: g a -> FFC g a
eta = \eff -> FFC (\imp -> imp eff)
{-# INLINE eta #-}
-- proof:
--     eta eff
-- === FFC (\pur imp -> imp eff pur)                                                 by defn
-- === FFC (\pur imp -> imp eff (\x -> pur x))                                       by eta expansion
-- === FFC (\pur imp -> imp eff (\x -> unFFC (FFC (\pur' _ -> pur' x)) pur imp))    by defn & eta expansion
-- === FFC (\pur imp -> imp eff (\x -> unFFC (fpure x) pur imp))                    by defn
-- === fimpure eff fpure                                                             by defn

-- | Embed an operation of 'g' into the monad transformer
eta' :: g a -> FFCT g m a
eta' = \eff -> FFCT (\mimp -> mimp eff)
{-# INLINE eta' #-}

-- | It's an 'Applicative' without a constraint on g
instance Applicative (FFC g) where
  pure = fpure
  {-# INLINE pure #-}
  (<*>) = \mf mx -> FFC (\imp -> unFFC mf imp <*> unFFC mx imp)
          -- \mf mx -> unFFC mf (unFFC mx (\x f -> (fpure (f x)))
          --                      (\gx k f -> fimpure gx (\x -> (k x f))))
          --          fimpure
  {-# INLINE (<*>) #-}

instance Applicative (FFCT g m) where
  pure = fpure'
  (<*>) = \mf mx -> FFCT (\mimp -> unFFCT mf mimp <*> unFFCT mx mimp)


-- | And it's a 'Monad' without constraints on 'g'
instance Monad (FFC g) where
  return = fpure
  {-# INLINE return #-}
  (>>=) = \mx f -> FFC (\imp -> unFFC mx imp >>= \x -> unFFC (f x) imp)
                   -- unFFC mx f fimpure
  {-# INLINE (>>=) #-}

instance Monad (FFCT g m) where
  return = fpure'
  (>>=) = \mx f -> FFCT (\mimp -> unFFCT mx mimp >>= \x -> unFFCT (f x) mimp)

instance MonadTrans (FFCT g) where
  lift m = FFCT (\mimp -> lift m)

-- | Lift a natural transformation in Hask to a natural transformation on the free monads.
foist :: (forall x . f x -> g x) -> FFC f a -> FFC g a
foist phi = \ma -> -- unFFC ma return (fimpure . phi)
              FFC (\imp -> unFFC ma (imp . phi))
{-# INLINE foist #-}

-- | Lift a natural transformation in Hask to a natural transformation on the free monads.
foistT :: (forall x . f x -> g x) -> FFCT f m a -> FFCT g m a
foistT phi = \ma -> FFCT (\mimp -> unFFCT ma (mimp . phi))

-- | If @m@ is a monad, we can interpret @FFC m@ in itself
retractFFC :: Monad m => FFC m a -> m a
retractFFC ma = runCont (unFFC ma (\mx -> cont (\f -> mx >>= f))) return
{-# INLINE retractFFC #-}
-- effects are interpreted as themselves:
--
-- @
-- retractFFC (eff ma) === ma
-- @
--
-- @
--     retractFFC (eff ma)
-- === unFFC (FFC (\pur imp -> imp ma pur) return (>>=))   by defns
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
--     unFFC (FFC (\pur _ -> pur a)) return (>>=)   by defns
-- === return a                                      by beta
-- @
--
-- @
-- retractFFC (m >>= f) === retractFFC m >>= retractFFC . f
-- @
--
-- @
--     retractFFC (FFC (\pur imp -> unFFC m (\x -> unFFC (f x) pur imp) imp))            by defn (>>=)
-- === unFFC (FFC (\pur imp -> unFFC m (\x -> unFFC (f x) pur imp) imp)) return (>>=)   by defn retractFFC
-- === unFFC m (\x -> unFFC (f x) return (>>=)) (>>=)                                    by beta
-- ===
-- === ???
-- ===
-- === unFFC m return (>>=) >>= \x -> unFFC (f x) return (>>=)                           by defn retractFFC
--     retractFFC m >>= \x -> retractFFC (f x)
-- @
--
-- stuck here.

-- | Interpret the freer monad transformer in itself.
retractFFCT :: (MonadTrans t, Monad (t m), Monad m) => FFCT (t m) m a -> t m a
retractFFCT ma = join . lift $ runContT (unFFCT ma (\tmx -> ContT (\kmtm -> return $ tmx >>= (join . lift . kmtm)))) (return . return)
  where
    join :: Monad m => m (m a) -> m a
    join mmx = mmx >>= id

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
-- === FFC (\\pur imp -> (\\pur' _ -> pur' a) (\\x -> unFFC (f x) pur imp) imp)   by defn
-- === FFC (\\pur imp -> (\\x -> unFFC (f x) pur imp) a)                         by beta
-- === FFC (\\pur imp -> unFFC (f a) pur imp)                                   by beta
-- === FFC (unFFC (f a))                                                       by eta
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
-- === FFC (\\pur imp -> mp (\\a -> unFFC ((\\x -> FFC (\\pur' _ -> pur' x)) a) pur imp) imp)   by defn
-- === FFC (\\pur imp -> mp (\\a -> unFFC (FFC (\\pur' _ -> pur' a)) pur imp) imp)             by beta
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
--     FFC (\\pur imp -> unFFC (FFC mp >>= f) (\\a -> unFFC (g a) pur imp) imp)                                                 by defn (>>=) outer
-- === FFC (\\pur imp -> unFFC (FFC (\\pur' imp' -> mp (\\b -> unFFC (f b) pur' imp') imp')) (\\a -> unFFC (g a) pur imp) imp)   by defn (>>= inner)
-- === FFC (\\pur imp -> mp (\\b -> unFFC (f b) (\\a -> unFFC (g a) pur imp)) imp)                                               by beta
-- === FFC (\\pur imp -> mp (\\b -> unFFC (FFC (\\pur' imp' -> unFFC (f b) (\\a -> unFFC (g a) pur' imp') imp')) pur imp) imp)   by beta
-- === FFC (\\pur imp -> mp (\\b -> unFFC (f b >>= g) pur imp) imp)                                                              by defn
-- === FFC (\\pur imp -> mp (\\b -> unFFC ((\\z -> f z >>= g) b) pur imp) imp)                                                    by beta
-- === FFC mp >>= (\\z -> f z >>= g)                                                                                             by defn
-- @
