
module Utils (makeMap, recsearch, (?|)) where

import qualified Data.Map.Lazy as Map

insertPairIntoMap :: Ord k => Map.Map k v -> (k, v) -> Map.Map k v
insertPairIntoMap map (key, value) = Map.insert key value map

makeMap :: Ord k => [(k, v)] -> Map.Map k v
makeMap xs = foldl insertPairIntoMap Map.empty xs

recsearch :: (item -> Maybe item) -> [item] -> Maybe item
recsearch _ [] = Nothing
recsearch f (x:xs) = case f x of
                       j@(Just something) -> j
                       Nothing            -> recsearch f xs

-- x ?| y
-- Evaluates to y if x is Nothing, x otherwise.
(?|) :: Maybe t -> Maybe t -> Maybe t
(?|) Nothing y = y
(?|) x _ = x
