{-# language GADTs, RankNTypes, GeneralizedNewtypeDeriving #-}

import Control.Monad.Free.Church (F (..), retract, hoistF)
import Control.Monad.Freer.Church

import Control.Applicative (Alternative (..))
import Control.Monad (MonadPlus(..), unless, replicateM_)
import Control.Monad.Trans.State
import Control.Monad.Trans.Except
import Control.Monad.Trans.Class (lift)

import Data.Functor.Identity
import Data.Function (on)

-- | The empty type constructor with no values.
data Empty a

-- | Ex falso quodlibet.
vacuous :: Empty a -> b
vacuous emp = emp `seq` vacuous emp

instance Functor Empty where
  fmap _f emp = vacuous emp

-- | The freer monad of the empty 'Functor' is the 'Identity' monad
interpEmpty :: FFC Empty a -> Identity a
interpEmpty = retractFFC . foist phi
  where
    phi :: Empty x -> Identity x
    phi emp = vacuous emp

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
interpConst = retractFFC . foist phi
  where
    phi :: Const b x -> Either b x
    phi (Const b) = Left b

raiseConst :: b -> FFC (Const b) a
raiseConst b = eta (Const b)

data Cont a = Cont { runCont :: forall r . (a -> r) -> r }

instance Functor Cont where
  fmap f (Cont c) = Cont (\k -> c (k . f))

instance Applicative Cont where
  pure = retCont
  mf <*> mx = mf >>= \f -> mx >>= (return . f)

instance Monad Cont where
  return = retCont
  (Cont cx) >>= f = Cont (\k -> cx (\x -> runCont (f x) k))

retCont :: a -> Cont a
retCont a = Cont (\k -> k a)

interpretIdentity :: FFC Identity a -> Cont a
interpretIdentity = retractFFC . foist phi
  where
    phi :: Identity x -> Cont x
    phi (Identity x) = retCont x

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
teleTo = retractFFC . foist phi
            -- F (\ar telek -> p ar (\tty k -> case tty of
            --                                  ReadTTY -> telek (ReadF k)
            --                                  WriteTTY c -> telek (WriteF c (k ()))))
  where
    phi :: Teletype x -> F TeleF x
    phi ReadTTY = F (\ar telek -> telek (ReadF ar))
    phi (WriteTTY c) = F (\ar telek -> telek (WriteF c (ar ())))


teleFrom :: F TeleF a -> FFC Teletype a
teleFrom = retract . hoistF phi
              -- FFC (\pur imp -> q pur (\telek -> case telek of
              --                                    ReadF k -> imp ReadTTY k
              --                                    WriteF c k -> imp (WriteTTY c) (\() -> k)))
  where
    phi :: TeleF x -> FFC Teletype x
    phi (ReadF k) = fimpure ReadTTY (fpure . k)
    phi (WriteF c k) = fimpure (WriteTTY c) (\() -> pure k)


ttyIO :: FFC Teletype a -> IO a
ttyIO = retractFFC . foist phi
                -- p return (\tty -> case tty of
                --                      ReadTTY -> \k -> getChar >>= k
                --                      WriteTTY c -> \k -> putChar c >> k ())
  where
    phi :: Teletype x -> IO x
    phi ReadTTY = getChar
    phi (WriteTTY c) = putChar c

newtype TapeIn = TapeIn String
  deriving (Show, Eq)
newtype TapeOut = TapeOut ShowS

mkTapeOut :: String -> TapeOut
mkTapeOut = TapeOut . showString

playOutTape :: TapeOut -> String
playOutTape (TapeOut s) = s ""

instance Eq TapeOut where
  (==) = (==) `on` playOutTape

instance Show TapeOut where
  showsPrec _ = showString . playOutTape

newtype Tapes a = Tapes { unTapes :: ExceptT () (State (TapeIn, TapeOut)) a }
  deriving (Functor, Applicative, Alternative, Monad, MonadPlus)

runTapes :: Tapes a -> TapeIn -> (Maybe a, TapeIn, TapeOut)
runTapes (Tapes m) tapeIn = case runState (runExceptT m) (tapeIn, TapeOut id) of
                              (Left (), (tapeIn, tapeOut)) -> (Nothing, tapeIn, tapeOut)
                              (Right a, (tapeIn, tapeOut)) -> (Just a, tapeIn, tapeOut)

getTape :: Tapes Char
getTape = Tapes $ do
  (tapeIn, tapeOut) <- lift get
  case tapeIn of
    TapeIn [] -> mzero
    TapeIn (c:cs) -> do
      lift $ put (TapeIn cs, tapeOut)
      return c

putTape :: Char -> Tapes ()
putTape c = Tapes $ lift $ modify (\(tapeIn, TapeOut cs) -> (tapeIn, TapeOut (cs . showChar c)))


ttyTape :: FFC Teletype a -> Tapes a
ttyTape = retractFFC . foist phi -- (FFC p) = p pur imp
  where
    phi :: Teletype x -> Tapes x
    phi ReadTTY = getTape
    phi (WriteTTY c) = putTape c
  -- where
  --   pur :: a -> TapeIn -> (Maybe (a, TapeOut), TapeIn)
  --   pur = \x tape -> (Just (x, TapeOut []), tape)
  --   imp :: Teletype x -> (x -> TapeIn -> (Maybe (a, TapeOut), TapeIn)) -> TapeIn -> (Maybe (a, TapeOut), TapeIn)
  --   imp = \tty -> case tty of
  --                      ReadTTY -> \ k tape -> case tape of
  --                                   TapeIn [] -> (Nothing, TapeIn [])
  --                                   TapeIn (c:cs) -> k c (TapeIn cs)
  --                      WriteTTY c -> \k tape -> case k () tape of
  --                                      (Nothing, tapeIn) -> (Nothing, tapeIn)
  --                                      (Just (ans, TapeOut cs), tapeIn) -> (Just (ans, TapeOut (c:cs)), tapeIn)
{-# INLINE ttyTape #-}

readTTY :: FFC Teletype Char
readTTY = eta ReadTTY

writeTTY :: Char -> FFC Teletype ()
writeTTY = eta . WriteTTY

echo :: Int -> FFC Teletype ()
echo n = replicateM_ n $ do
  c <- readTTY
  writeTTY c

  
echo' :: Int -> FFC Teletype ()
echo' = teleFrom . teleTo . echo

assertEq :: (Show a, Eq a) => a -> a -> IO ()
assertEq got want =
  unless (got == want) $ fail ("Expected: " ++ show want ++ "\nGot: " ++ show got)

echoTape = ttyTape . echo
echoTape' = ttyTape . echo'

main = do
  assertEq (interpEmpty (f 10)) 89
  assertEq (runTapes (echoTape 2) (TapeIn "abcd")) (Just (), TapeIn "cd", mkTapeOut "ab")
  assertEq (runTapes (echoTape' 2) (TapeIn "abcd")) (Just (), TapeIn "cd", mkTapeOut "ab")
-- ttyIO (echo 10)

