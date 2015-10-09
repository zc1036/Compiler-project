
data BinOpType = Add
               | Subtract
               | Multiply
               | Divide
               deriving (Show)

data UnOpType = Negate
               deriving (Show)

data Expr = BinaryExpr BinOpType Expr Expr
          | UnaryExpr UnOpType Expr
          | IntegerLiteral Int
          deriving (Show)

left (BinaryExpr _ left _) = left
right (BinaryExpr _ _ right) = right

data Statement = Statement Expr
               deriving (Show)

data StatementList = StatementList [Statement]
                   deriving (Show)


data Stopper a = Stopper a Int
               | Stopped
                 deriving (Show)

stopperVal (Stopper a _) = a
stopperCount (Stopper _ c) = c

instance Monad Stopper where
  return x = Stopper x 0

  (Stopper a 3) >>= b = Stopped

  (Stopper a num) >>= b = Stopper x y
    where s = b a
          x = stopperVal s
          y = (stopperCount s) + 1
