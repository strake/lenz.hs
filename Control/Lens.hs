module Control.Lens (Lens, Traversal, Iso,
                     lens, iso,
                     get, set, modify, mapping,
                     fstL, sndL, swapL, unitL, bitL) where

import Prelude hiding (id)

import Control.Applicative
import Control.Category
import Control.Category.Unicode
import Data.Bits (Bits (..))
import Data.Bool (bool)
import Data.Functor.Identity
import Data.Profunctor
import Data.Tuple (swap)

type Lens α β a b = ∀ f . Functor f => (a -> f b) -> (α -> f β)

type Traversal α β a b = ∀ f . Applicative f => (a -> f b) -> (α -> f β)

type Iso α β a b = ∀ p f . (Profunctor p, Functor f) ⇒ p a (f b) -> p α (f β)

lens :: (α → a) → (b → α → β) → Lens α β a b
lens get set ret = liftA2 fmap (flip set) (ret ∘ get)

iso :: (α → a) → (b → β) → Iso α β a b
iso f g = dimap f (fmap g)

get :: ((a → Const a b) → α → Const a β) → α → a
get l = getConst ∘ l Const

set :: ((a → Identity b) → α → Identity β) → b → α → β
set l = modify l ∘ pure

modify :: ((a → Identity b) → α → Identity β) → (a → b) → α → β
modify l f = runIdentity ∘ l (Identity ∘ f)

mapping :: (Functor f, Functor g) => AnIso α β a b -> Iso (f α) (g β) (f a) (g b)
mapping = (`withIso` \ f g -> iso (fmap f) (fmap g))

withIso :: AnIso α β a b -> ((α -> a) -> (b -> β) -> c) -> c
withIso x = case x (Xchg id Identity) of Xchg φ χ -> \ f -> f φ (runIdentity ∘ χ)

type AnIso α β a b = Xchg a b a (Identity b) -> Xchg a b α (Identity β)

data Xchg a b α β = Xchg (α -> a) (b -> β) deriving (Functor)

instance Profunctor (Xchg a b) where dimap f g (Xchg φ χ) = Xchg (φ ∘ f) (g ∘ χ)

fstL :: Lens (a, c) (b, c) a b
fstL = swapL ∘ sndL

sndL :: Lens (a, b) (a, c) b c
sndL f = id *** f >>> uncurry (fmap ∘ (,))

swapL :: Iso (a, b) (c, d) (b, a) (d, c)
swapL = iso swap swap

unitL :: Lens α α () ()
unitL = lens (pure ()) (\ () -> id)

bitL :: Bits a => Int -> Lens a a Bool Bool
bitL = liftA2 lens (flip testBit) (flip (flip ∘ bool clearBit setBit))
