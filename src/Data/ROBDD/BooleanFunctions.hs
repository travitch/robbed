-- | These are additional primitive boolean functions not present in any
-- standard libraries.
module Data.ROBDD.BooleanFunctions ( boolXor
                                   , boolImpl
                                   , boolBiimp
                                   , boolNotAnd
                                   , boolNotOr
                                   ) where

boolXor :: Bool -> Bool -> Bool
True `boolXor` True = False
False `boolXor` False = False
_ `boolXor` _ = True

boolImpl :: Bool -> Bool -> Bool
True `boolImpl` True = True
True `boolImpl` False = False
False `boolImpl` True = True
False `boolImpl` False = True

boolBiimp :: Bool -> Bool -> Bool
True `boolBiimp` True = True
False `boolBiimp` False = True
_ `boolBiimp` _ = False

boolNotAnd :: Bool -> Bool -> Bool
True `boolNotAnd` True = False
_ `boolNotAnd` _ = True

boolNotOr :: Bool -> Bool -> Bool
False `boolNotOr` False = True
_ `boolNotOr` _ = False
