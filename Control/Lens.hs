module Control.Lens (Lens, Traversal, Iso,
                     lens, iso, invert,
                     get, set, modify, mapping,
                     toListOf, foldrOf, foldlOf, mapAccumLOf, mapAccumROf,
                     fstL, sndL, swapL, unitL, bitL, constL) where

import Prelude hiding (id)

import Control.Applicative
import Control.Applicative.Backwards (Backwards (..))
import Control.Category
import Control.Category.Unicode
import Control.Monad.Trans.State (State, state, runState)
import Data.Bits (Bits (..))
import Data.Bool (bool)
import Data.Functor.Identity
import Data.Monoid (Dual (..), Endo (..))
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
get l = gets l id

gets :: ((a -> Const c b) -> α -> Const c β) -> (a -> c) -> α -> c
gets l f = getConst ∘ l (Const ∘ f)

set :: ((a → Identity b) → α → Identity β) → b → α → β
set l = modify l ∘ pure

modify :: ((a → Identity b) → α → Identity β) → (a → b) → α → β
modify l f = runIdentity ∘ l (Identity ∘ f)

mapping :: (Functor f, Functor g) => AnIso α β a b -> Iso (f α) (g β) (f a) (g b)
mapping = (`withIso` \ f g -> iso (fmap f) (fmap g))

withIso :: AnIso α β a b -> ((α -> a) -> (b -> β) -> c) -> c
withIso x = case x (Xchg id Identity) of Xchg φ χ -> \ f -> f φ (runIdentity ∘ χ)

invert :: AnIso α β a b -> Iso b a β α
invert = flip withIso $ flip iso

type AnIso α β a b = Xchg a b a (Identity b) -> Xchg a b α (Identity β)

data Xchg a b α β = Xchg (α -> a) (b -> β) deriving (Functor)

instance Profunctor (Xchg a b) where dimap f g (Xchg φ χ) = Xchg (φ ∘ f) (g ∘ χ)

-- foldOf :: Monoid a => Getting a α β a b -> α -> a
-- foldOf = get

-- foldMapOf :: Getting c α β a b -> (a -> c) -> α -> c
-- foldMapOf = gets

toListOf :: Getting (Endo [a]) α β a b -> α -> [a]
toListOf l = foldrOf l (:) []

foldrOf :: Getting (Endo c) α β a b -> (a -> c -> c) -> c -> α -> c
foldrOf l f z₀ = flip appEndo z₀ ∘ gets l (Endo ∘ f)

foldlOf :: Getting (Dual (Endo c)) α β a b -> (c -> a -> c) -> c -> α -> c
foldlOf l f z₀ = flip appEndo z₀ ∘ getDual ∘ gets l (Dual ∘ Endo ∘ flip f)

-- foldMapAccumOf :: Monoid c => ((a -> (c, b)) -> α -> (c, β)) -> (a -> (c, b)) -> α -> (c, β)
-- foldMapAccumOf = id

mapAccumROf :: ((a -> State c b) -> α -> State c β) -> (a -> c -> (c, b)) -> c -> α -> (c, β)
mapAccumROf l f z₀ = swap ∘ flip runState z₀ ∘ l (state ∘ (swap ∘) ∘ f)

mapAccumLOf :: ((a -> Backwards (State c) b) -> α -> Backwards (State c) β) -> (c -> a -> (c, b)) -> c -> α -> (c, β)
mapAccumLOf l f z₀ = swap ∘ flip runState z₀ ∘ forwards ∘ l (Backwards ∘ state ∘ (swap ∘) ∘ flip f)

type Getting r α β a b = (a -> Const r b) -> α -> Const r β

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

constL :: Iso (Const a α) (Const b β) a b
constL = iso getConst Const
