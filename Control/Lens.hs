module Control.Lens (Lens, Refractor, Traversal,
                     lens, iso,
                     get, set, modify,
                     fstL, sndL, swapL, unitL, bitL) where

import Prelude hiding (id)

import Control.Applicative
import Control.Arrow
import Control.Category
import Control.Category.Unicode
import Data.Bits (Bits (..))
import Data.Bool (bool)
import Data.Functor.Identity
import Data.Tuple (swap)

type Refractor c d α β a b = ∀ p f . (d f, c p) ⇒ p a (f b) → p α (f β)

type Lens α β a b = Refractor ((~) (→)) Functor α β a b

type Traversal α β a b = Refractor ((~) (→)) Applicative α β a b

lens :: (α → a) → (b → α → β) → Lens α β a b
lens get set ret = liftA2 fmap (flip set) (ret ∘ get)

iso :: (α → a) → (b → β) → Lens α β a b
iso f g = (fmap g ∘) ∘ (∘ f)

get :: ((a → Const a b) → α → Const a β) → α → a
get l = getConst ∘ l Const

set :: ((a → Identity b) → α → Identity β) → b → α → β
set l = modify l ∘ pure

modify :: ((a → Identity b) → α → Identity β) → (a → b) → α → β
modify l f = runIdentity ∘ l (Identity ∘ f)

fstL :: Lens (a, c) (b, c) a b
fstL = swapL ∘ sndL

sndL :: Lens (a, b) (a, c) b c
sndL f = id *** f >>> uncurry (fmap ∘ (,))

swapL :: Lens (a, b) (c, d) (b, a) (d, c)
swapL = iso swap swap

unitL :: Lens α α () ()
unitL = lens (pure ()) (\ () -> id)

bitL :: Bits a => Int -> Lens a a Bool Bool
bitL = liftA2 lens (flip testBit) (flip (flip ∘ bool clearBit setBit))