{-# language GADTs, RankNTypes #-}

import Control.Monad.Free.Church (F (..))
import Control.Monad.Freer.Church

import Control.Monad (unless) 

import Data.Functor.Identity

-- | The empty type constructor with no values.
data Empty a

-- | Ex falso quodlibet.
vacuous :: Empty a -> b
vacuous emp = emp `seq` vacuous emp

instance Functor Empty where
  fmap _f emp = vacuous emp

-- | The freer monad of the empty 'Functor' is the 'Identity' monad
interpEmpty :: FFC Empty a -> Identity a
interpEmpty (FFC ra) = ra return (\emp k -> k (vacuous emp))

f :: Monad m => Int -> m Int
f 0 = return 1
f 1 = return 1
f n = do
  i <- f (n - 1)
  j <- f (n - 2)
  return (i + j)

data Const b a = Const b

instance Functor (Const b) where
  fmap _f (Const b) = Const b

interpConst :: FFC (Const b) a -> Either b a
interpConst (FFC p) = p Right (\(Const b) _k -> Left b) 

raiseConst :: b -> FFC (Const b) a
raiseConst b = eta (Const b)

data Cont a = Cont { runCont :: forall r . (a -> r) -> r }

retCont :: a -> Cont a
retCont a = Cont (\k -> k a)

interpretIdentity :: FFC Identity a -> Cont a
interpretIdentity (FFC p) = p retCont (\(Identity x) k -> k x)

contCont :: (forall r . (a -> r) -> r) -> FFC Identity a
contCont k = eta (k Identity)

data Teletype a where
  ReadTTY :: Teletype Char
  WriteTTY :: Char -> Teletype ()

data TeleF next where
  ReadF :: (Char -> next) -> TeleF next
  WriteF :: Char -> next -> TeleF next

instance Functor TeleF where
  fmap f (ReadF k) = ReadF (f . k)
  fmap f (WriteF c k) = WriteF c (f k)

teleTo :: FFC Teletype a -> F TeleF a
teleTo (FFC p) = F (\ar telek -> p ar (\tty k -> case tty of
                                                   ReadTTY -> telek (ReadF k)
                                                   WriteTTY c -> telek (WriteF c (k ()))))

teleFrom :: F TeleF a -> FFC Teletype a
teleFrom (F q) = FFC (\pur imp -> q pur (\telek -> case telek of
                                            ReadF k -> imp ReadTTY k
                                            WriteF c k -> imp (WriteTTY c) (\() -> k)))

ttyIO :: FFC Teletype a -> IO a
ttyIO (FFC p) = p return (\tty k -> case tty of
                                      ReadTTY -> do
                                        c <- getChar
                                        k c
                                      WriteTTY c -> do
                                        putChar c
                                        k ())

newtype TapeIn = TapeIn String
  deriving (Show, Eq)
newtype TapeOut = TapeOut [Char]
  deriving (Show, Eq)

ttyTape :: FFC Teletype a -> TapeIn -> (Maybe (a, TapeOut), TapeIn)
ttyTape (FFC p) = p pur imp
  where
    pur :: a -> TapeIn -> (Maybe (a, TapeOut), TapeIn)
    pur = \x tape -> (Just (x, TapeOut []), tape)
    {-# INLINE pur #-}
    imp :: Teletype x -> (x -> TapeIn -> (Maybe (a, TapeOut), TapeIn)) -> TapeIn -> (Maybe (a, TapeOut), TapeIn)
    imp = \tty k tape -> case tty of
                       ReadTTY -> case tape of
                                    TapeIn [] -> (Nothing, TapeIn [])
                                    TapeIn (c:cs) -> k c (TapeIn cs)
                       WriteTTY c -> case k () tape of
                                       (Nothing, tapeIn) -> (Nothing, tapeIn)
                                       (Just (ans, TapeOut cs), tapeIn) -> (Just (ans, TapeOut (c:cs)), tapeIn)
    {-# INLINE imp #-}
{-# INLINE ttyTape #-}

readTTY :: FFC Teletype Char
readTTY = eta ReadTTY

writeTTY :: Char -> FFC Teletype ()
writeTTY = eta . WriteTTY

echo :: Int -> FFC Teletype ()
echo 0 = return ()
echo n = do
  c <- readTTY
  writeTTY c
  echo (n - 1)
  
echo' :: Int -> FFC Teletype ()
echo' n = teleFrom (teleTo (echo n))

assertEq :: (Show a, Eq a) => a -> a -> IO ()
assertEq got want =
  unless (got == want) $ fail ("Expected: " ++ show want ++ "\nGot: " ++ show got)

main = do
  assertEq (interpEmpty (f 10)) 89
  assertEq (ttyTape (echo' 2) (TapeIn "abcd")) (Just ((), TapeOut "ab"), TapeIn "cd")
