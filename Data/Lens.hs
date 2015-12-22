module Data.Lens (Lens,
                  lens, iso,
                  get, set, modify,
                  fstL, sndL, swapL, unitL) where

import Prelude hiding (id)

import Control.Applicative
import Control.Arrow
import Control.Category
import Control.Category.Unicode
import Data.Functor.Identity
import Data.Tuple (swap)

type Refractor c d α β a b = ∀ p f . (d f, c p) ⇒ p a (f b) → p α (f β)

type Lens α β a b = Refractor ((~) (→)) Functor α β a b

type Traversal α β a b = Refractor ((~) (→)) Applicative α β a b

lens :: (α → a) → (b → α → β) → Lens α β a b
lens get set ret = liftA2 fmap (flip set) (ret ∘ get)

iso :: (α → a) → (b → β) → Lens α β a b
iso f g = (fmap g ∘) ∘ (∘ f)

get :: Lens α β a b → α → a
get l = getConst ∘ l Const

set :: Lens α β a b → b → α → β
set l = modify l ∘ pure

modify :: Lens α β a b → (a → b) → α → β
modify l f = runIdentity ∘ l (Identity ∘ f)

fstL :: Lens (a, c) (b, c) a b
fstL = swapL ∘ sndL

sndL :: Lens (a, b) (a, c) b c
sndL f = id *** f >>> uncurry (fmap ∘ (,))

swapL :: Lens (a, b) (c, d) (b, a) (d, c)
swapL = iso swap swap

unitL :: Lens α α () ()
unitL = lens (pure ()) (\ () -> id)
