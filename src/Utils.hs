
module Utils where

-- Combines map and fold into one operation, when the map needs the
-- fold to calculate its result.
mapfold :: (foldt -> mapfrom -> (foldt, mapto)) -> foldt -> [mapfrom] -> (foldt, [mapto])
mapfold f z xs = mapfold' f z [] xs

-- helper for mapfold
mapfold' :: (foldt -> mapfrom -> (foldt, mapto)) -> foldt -> [mapto] -> [mapfrom] -> (foldt, [mapto])

mapfold' _ folded mapped [] = (folded, reverse mapped)
mapfold' f folded mapped (x:xs) = mapfold' f newFolded (mappedItem:mapped) xs
                                  where (newFolded, mappedItem) = (f folded x)
