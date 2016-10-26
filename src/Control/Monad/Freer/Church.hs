-- | Church encoded Freer monad
--
-- Based on Oleg's Freer Monad (http://okmij.org/ftp/Computation/free-monad.html) but Chruch encoded.
--
-- $proofs
{-# language GADTs, RankNTypes #-}
module Control.Monad.Freer.Church where

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
  fmap f = \mf -> runFFC mf (\a -> FFC (\pur _imp -> pur (f a)))
                  (\gx k -> FFC (\pur imp -> imp gx (\x -> runFFC (k x) pur imp)))
  {-# INLINE fmap #-}

-- | Embed the effect of 'g' into the monad
--
eta :: g a -> FFC g a
eta = \eff -> FFC (\pur imp -> imp eff pur)
{-# INLINE eta #-}

-- | It's an 'Applicative' without a constraint on g
instance Applicative (FFC g) where
  pure = \a -> FFC (\pur _imp -> pur a)
  {-# INLINE pure #-}
  (<*>) = \mf mx -> runFFC mf (runFFC mx (\x f -> (pure (f x)))
                                (\gx k f -> FFC (\pur imp -> imp gx (\x -> runFFC (k x f) pur imp))))
                    (\gx k -> FFC (\pur imp -> imp gx (\x -> runFFC (k x) pur imp)))
  {-# INLINE (<*>) #-}


-- | And it's a 'Monad' without constraints on 'g'
instance Monad (FFC g) where
  return = pure
  {-# INLINE return #-}
  (>>=) = \mx f -> runFFC mx f (\gx k -> FFC (\pur imp -> imp gx (\x -> runFFC (k x) pur imp)))
  {-# INLINE (>>=) #-}

foist :: (forall x . f x -> g x) -> FFC f a -> FFC g a
foist phi = \ma -> runFFC ma return (\fx k -> eta (phi fx) >>= k)
{-# INLINE foist #-}

retractFFC :: Monad m => FFC m a -> m a
retractFFC ma = runFFC ma return (>>=)
{-# INLINE retractFFC #-}

-- $proofs
--
-- == Functor law ==
--
-- It's a real functor.  (id law left as exercise)
--
-- fmap f (fmap g (FFC p))
-- = fmap f (FFC (\pur imp -> p (pur . g) imp))     by defn
-- = FFC (\pur' imp' -> (\pur imp -> p (pur . g) imp) (pur' . f) imp')  by defn
-- = FFC (\pur' imp' -> p ((pur' . f) . g) imp')  by beta
-- = FFC (\pur' imp' -> p (pur' . (f . g)) imp')  by assoc-compose
-- = fmap (f . g) (FFC p)                         by defn
--
-- == Applicative laws, too==
--
-- pure id <*> v = v                            -- Identity
--
-- pure id <*> (FFC vp)
-- = (FFC (\pur _ -> pur id)) <*> (FFC vp)   by defn pure
-- = FFC (\pur' imp' -> (\pur _ -> pur id) (\f -> vp (pur' . f) imp') imp')   by defn (<*>)
-- = FFC (\pur' imp' -> (\f -> vp (pur' . f) imp') id)   by beta
-- = FFC (\pur' imp' -> vp (pur' . id) imp')             by beta
-- = FFC (\pur' imp' -> vp pur' imp')                    by compose-id
-- = FFC vp                                              by eta
--
-- pure f <*> pure x = pure (f x)               -- Homomorphism
--
-- pure f <*> pure x
-- FFC (\pur _ -> pur f) <*> FFC (\pur' _-> pur' x)    by defn
-- FFC (\pur'' imp'' -> (\pur _ -> pur f) (\h -> (\pur' _ -> pur' x) (pur'' . h) imp'') imp'')  by defn
-- FFC (\pur'' imp'' -> (\h -> (\pur' -> pur' x) (pur'' . h) imp'') f)     by beta
-- FFC (\pur'' imp'' -> (\pur' _ -> pur' x) (pur'' . f) imp'')             by beta
-- FFC (\pur'' imp'' -> (pur'' . f) x)                                     by beta
-- FFC (\pur'' _ -> pur'' (f x))                                           by defn-compose
-- pure (f x)                                                              by defn
--
-- u <*> pure y = pure (\k -> k y) <*> u              -- Interchange
--
-- FFC ru <*> FFC (\pur _ -> pur y)           -- by defn
-- FFC (\pur' imp' -> ru (\u -> (\pur _ -> pur y) (pur' . u) imp') imp')   -- by defn
-- FFC (\pur' imp' -> ru (\u -> (pur' . u) y) imp')     -- by beta
-- FFC (\pur' imp' -> ru (\u -> pur' (u y)) imp')       -- by beta
-- FFC (\pur' imp' -> ru (\u -> pur' ((\k -> k y) u)) imp')   -- by beta
-- FFC (\pur' imp' -> ru (\u -> (pur' . (\k -> k y)) u) imp') -- by defn-compose
-- FFC (\pur' imp' -> ru (pur' . (\k -> k y)) imp')             -- by eta
-- FFC (\pur' imp' -> (\f -> ru (pur' . f) imp') (\k -> k y))   -- by beta
-- FFC (\pur' imp' -> (\pur _ -> pur (\k -> k y)) (\f -> ru (pur' . f) imp') imp') -- by defn
-- FFC (\pur _ -> pur (\k -> k y)) <*> FFC ru
--
-- pure compose <*> u <*> v <*> w = u <*> (v <*> w) -- Composition
-- omg tedious
--
--
-- == Monad laws ==
-- 
-- return a >>= f = f a
--
-- FFC (\pur' _ -> pur' a) >>= f
-- FFC (\pur imp -> (\pur' _ -> pur' a) (\x -> runFFC (f x) pur imp) imp)   by defn
-- FFC (\pur imp -> (\x -> runFFC (f x) pur imp) a)   by beta
-- FFC (\pur imp -> runFFC (f a) pur imp)    by beta
-- FFC (runFFC (f a))   by eta
-- f a  by eta
--
--
-- (FFC mp) >>= return = (FFC mp)
-- 
-- FFC mp >>= (\x -> FFC (\pur' _ -> pur' x))   by defn
-- FFC (\pur imp -> mp (\a -> runFFC ((\x -> FFC (\pur' _ -> pur' x)) a) pur imp) imp)  by defn
-- FFC (\pur imp -> mp (\a -> runFFC (FFC (\pur' _ -> pur' a)) pur imp) imp)  by beta
-- FFC (\pur imp -> mp (\a -> pur a) imp)    by beta
-- FFC (\pur imp -> mp pur imp)              by eta
-- FFC mp                                    by eta
--
--
-- (FFC mp >>= f) >>= g = (FFC mp) >>= (\x -> f x >>= g)
--
-- FFC (\pur imp -> runFFC (FFC mp >>= f) (\a -> runFFC (g a) pur imp) imp)  -- by defn (>>=) outer
-- FFC (\pur imp -> runFFC (FFC (\pur' imp' -> mp (\b -> runFFC (f b) pur' imp') imp')) (\a -> runFFC (g a) pur imp) imp)  -- by defn (>>= inner)
-- FFC (\pur imp -> mp (\b -> runFFC (f b) (\a -> runFFC (g a) pur imp)) imp)  -- by beta
-- FFC (\pur imp -> mp (\b -> runFFC (FFC (\pur' imp' -> runFFC (f b) (\a -> runFFC (g a) pur' imp') imp')) pur imp) imp)    by beta
-- FFC (\pur imp -> mp (\b -> runFFC (f b >>= g) pur imp) imp)               by defn
-- FFC (\pur imp -> mp (\b -> runFFC ((\z -> f z >>= g) b) pur imp) imp)      by beta
-- FFC mp >>= (\z -> f z >>= g)      by defn


