
module Utils where

import qualified Data.Map.Lazy as Map

-- Combines map and fold into one operation, when the map needs the
-- fold to calculate its result. Kinda like a zip, but the elements of
-- one of the lists are generated on the fly rather than all at once.
mapfold :: (foldt -> mapfrom -> (foldt, mapto)) -> foldt -> [mapfrom] -> (foldt, [mapto])
mapfold f z xs = mapfold' f z [] xs

-- helper for mapfold
mapfold' :: (foldt -> mapfrom -> (foldt, mapto)) -> foldt -> [mapto] -> [mapfrom] -> (foldt, [mapto])

mapfold' _ folded mapped [] = (folded, reverse mapped)
mapfold' f folded mapped (x:xs) = mapfold' f newFolded (mappedItem:mapped) xs
                                  where (newFolded, mappedItem) = (f folded x)

insertPairIntoMap :: Ord k => Map.Map k v -> (k, v) -> Map.Map k v
insertPairIntoMap map (key, value) = Map.insert key value map

makeMap :: Ord k => [(k, v)] -> Map.Map k v
makeMap xs = foldl insertPairIntoMap Map.empty xs
