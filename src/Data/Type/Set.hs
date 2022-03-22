{-# LANGUAGE GADTs, DataKinds, KindSignatures, TypeOperators, TypeFamilies,
             MultiParamTypeClasses, FlexibleInstances, PolyKinds,
             FlexibleContexts, UndecidableInstances, ConstraintKinds,
             ScopedTypeVariables, TypeInType, TypeApplications #-}

module Data.Type.Set (Set(..), Union, Unionable, union, quicksort, append,
                      Sort, Sortable, (:++), Split, split, Cmp, Filter, Flag(..),
                      Nub, Nubable, nub, AsSet, asSet, IsSet, Subset, subset,
                      Delete(..), Proxy(..), remove, Remove, (:\),
                      Elem(..), Member(..), MemberP, NonMember) where

import GHC.TypeLits
import Data.Type.Bool
import Data.Type.Equality

import Rearrange.Typeclass
import Rearrange.Rearrangeable

data Proxy (p :: k) = Proxy

-- Value-level 'Set' representation,  essentially a list
--type Set :: [k] -> Type
data Set (n :: [k]) where
    {--| Construct an empty set -}
    Empty :: Set '[]
    {--| Extend a set with an element -}
    Ext :: e -> Set s -> Set (e ': s)

instance Rearrangeable Set where
  rConsToHead (Ext x _) = Ext x
  rTail (Ext _ xs) = xs
  rEmpty = Empty
instance RearrangeableStar Set where
  rCons = Ext
  rHead (Ext x _) = x

instance Show (Set '[]) where
    show Empty = "{}"

instance (Show e, Show' (Set s)) => Show (Set (e ': s)) where
    show (Ext e s) = "{" ++ show e ++ (show' s) ++ "}"

class Show' t where
    show' :: t -> String
instance Show' (Set '[]) where
    show' Empty = ""
instance (Show' (Set s), Show e) => Show' (Set (e ': s)) where
    show' (Ext e s) = ", " ++ show e ++ (show' s)

instance Eq (Set '[]) where
  (==) _ _ = True
instance (Eq e, Eq (Set s)) => Eq (Set (e ': s)) where
    (Ext e m) == (Ext e' m') = e == e' && m == m'

instance Ord (Set '[]) where
  compare _ _ = EQ
instance (Ord a, Ord (Set s)) => Ord (Set (a ': s)) where
  compare (Ext a as) (Ext a' as') = case compare a a' of
    EQ ->
      compare as as'

    other ->
      other

{-| At the type level, normalise the list form to the set form -}
type AsSet s = Nub (Sort s)

{-| At the value level, noramlise the list form to the set form -}
asSet :: (RDel Set s (Sort s), Nubable (Sort s))
  => Set s -> Set (AsSet s)
asSet = nub . quicksort

{-| Predicate to check if in the set form -}
type IsSet s = (s ~ Nub (Sort s))

{-| Useful properties to be able to refer to someties -}
type SetProperties (f :: [k]) =
  ( Union f ('[] :: [k]) ~ f,
    Split f ('[] :: [k]) f,
    Union ('[] :: [k]) f ~ f,
    Split ('[] :: [k]) f f,
    Union f f ~ f,
    Split f f f,
    Unionable f ('[] :: [k]),
    Unionable ('[] :: [k]) f
  )
{-- Union --}

{-| Union of sets -}
type Union s t = Nub (Sort (s :++ t))
type Unionable s t = (Sortable (s :++ t),
  Nubable (Sort (s :++ t)))

union :: forall s t.
  Unionable s t
  => Set s -> Set t -> Set (Union s t)
union s t = nub $ quicksort (append s t)

{-| List append (essentially set disjoint union) -}
type family (:++) (x :: [k]) (y :: [k]) :: [k] where
            '[]       :++ xs = xs
            (x ': xs) :++ ys = x ': (xs :++ ys)

infixr 5 :++

append :: Set s -> Set t -> Set (s :++ t)
append Empty x = x
append (Ext e xs) ys = Ext e (append xs ys)

{-| Delete elements from a set -}
type family (m :: [k]) :\ (x :: k) :: [k] where
     '[]       :\ x = '[]
     (x ': xs) :\ x = xs :\ x
     (y ': xs) :\ x = y ': (xs :\ x)

class Remove s t where
  remove :: Set s -> Proxy t -> Set (s :\ t)

instance Remove '[] t where
  remove Empty Proxy = Empty

instance {-# OVERLAPS #-} Remove xs x => Remove (x ': xs) x where
  remove (Ext _ xs) x@Proxy = remove xs x

instance {-# OVERLAPPABLE #-} (((y : xs) :\ x) ~ (y : (xs :\ x)), Remove xs x)
      => Remove (y ': xs) x where
  remove (Ext y xs) (x@Proxy) = Ext y (remove xs x)

type Split s t st = (RDel Set st s, RDel Set st t)

{-| Splitting a union a set, given the sets we want to split it into -}
split :: Split s t st =>
  Set st -> (Set s, Set t)
split inp = (fst $ rDel inp, fst $ rDel inp)

{-| Remove duplicates from a sorted list -}
type family Nub t where
    Nub '[]           = '[]
    Nub '[e]          = '[e]
    Nub (e ': e ': s) = Nub (e ': s)
    Nub (e ': f ': s) = e ': Nub (f ': s)

{-| Value-level counterpart to the type-level 'Nub'
    Note: the value-level case for equal types is not define here,
          but should be given per-application, e.g., custom 'merging' behaviour may be required -}

class Nubable t where
    nub :: Set t -> Set (Nub t)

instance Nubable '[] where
    nub Empty = Empty

instance Nubable '[e] where
    nub (Ext x Empty) = Ext x Empty

instance Nubable (e ': s) => Nubable (e ': e ': s) where
    nub (Ext _ (Ext e s)) = nub (Ext e s)

instance {-# OVERLAPS #-} (Nub (e ': f ': s) ~ (e ': Nub (f ': s)),
              Nubable (f ': s)) => Nubable (e ': f ': s) where
    nub (Ext e (Ext f s)) = Ext e (nub (Ext f s))

type Subset s t = RDel Set t s

{-| Construct a subsetset 's' from a superset 't' -}
subset :: Subset s t => Set t -> Set s
subset = fst . rDel

{-| Type-level quick sort for normalising the representation of sets -}
type family Sort (xs :: [k]) :: [k] where
            Sort '[]       = '[]
            Sort (x ': xs) = ((Sort (Filter FMin x xs)) :++ '[x]) :++ (Sort (Filter FMax x xs))

data Flag = FMin | FMax

type family Filter (f :: Flag) (p :: k) (xs :: [k]) :: [k] where
            Filter f p '[]       = '[]
            Filter FMin p (x ': xs) = If (Cmp x p == LT) (x ': (Filter FMin p xs)) (Filter FMin p xs)
            Filter FMax p (x ': xs) = If (Cmp x p == GT || Cmp x p == EQ) (x ': (Filter FMax p xs)) (Filter FMax p xs)

type family DeleteFromList (e :: elem) (list :: [elem]) where
    DeleteFromList elem '[] = '[]
    DeleteFromList elem (x ': xs) = If (Cmp elem x == EQ)
                                       xs
                                       (x ': DeleteFromList elem xs)

type family Delete elem set where
    Delete elem (Set xs) = Set (DeleteFromList elem xs)

type Sortable xs = RDel Set xs (Sort xs)

{-| Value-level quick sort that respects the type-level ordering -}
quicksort :: Sortable xs => Set xs -> Set (Sort xs)
quicksort = fst . rDel

{-| Open-family for the ordering operation in the sort -}

type family Cmp (a :: k) (b :: k) :: Ordering

{-| Access the value at a type present in a set. -}
class Elem a s where
  project :: Proxy a -> Set s -> a

instance {-# OVERLAPS #-} Elem a (a ': s) where
  project _ (Ext x _)  = x

instance {-# OVERLAPPABLE #-} Elem a s => Elem a (b ': s) where
  project p (Ext _ xs) = project p xs

-- | Value level type list membership predicate: does the type 'a' show up in
--   the type list 's'?
class Member a s where
  member :: Proxy a -> Set s -> Bool

instance Member a '[] where
  member _ Empty = False

instance {-# OVERLAPS #-} Member a (a ': s) where
  member _ (Ext x _)  = True

instance {-# OVERLAPPABLE #-} Member a s => Member a (b ': s) where
  member p (Ext _ xs) = member p xs

-- | Type level type list membership predicate: does the type 'a' show up in the
--   type list 's'?
--type MemberP :: k -> [k] -> Bool
type family MemberP a s :: Bool where
            MemberP a '[]      = False
            MemberP a (a ': s) = True
            MemberP a (b ': s) = MemberP a s

type NonMember a s = MemberP a s ~ False
