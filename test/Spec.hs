{-# LANGUAGE OverloadedStrings #-}

module Main where

import Test.Tasty
import Test.Tasty.HUnit

import qualified Data.Text.Lazy as L
import qualified Data.Text.Lazy.IO as L
import qualified Data.Map as Map

import Syntax
import Type
import Parser
import Infer
import Env
import Eval
import Pretty ()

main :: IO ()
main = defaultMain tests

tests :: TestTree
tests = testGroup "Poly"
  [ parserTests
  , typeInferenceTests
  , evalTests
  , errorTests
  , integrationTests
  ]

-------------------------------------------------------------------------------
-- Helpers
-------------------------------------------------------------------------------

-- | Parse, infer, and return the normalized scheme
inferFromText :: L.Text -> Either TypeError Scheme
inferFromText src = case parseExpr src of
  Left err -> error (show err)
  Right ex -> inferExpr Env.empty ex

-- | Parse a module and infer all top-level definitions
inferModuleFromText :: L.Text -> Either TypeError Env
inferModuleFromText src = case parseModule "<test>" src of
  Left err -> error (show err)
  Right decls -> inferTop Env.empty decls

-- | Shorthand for building type schemes
mono :: Type -> Scheme
mono = Forall []

forall1 :: (Type -> Type) -> Scheme
forall1 f = Forall [TV "a"] (f (TVar (TV "a")))

forall2 :: (Type -> Type -> Type) -> Scheme
forall2 f = Forall [TV "a", TV "b"] (f (TVar (TV "a")) (TVar (TV "b")))

forall3 :: (Type -> Type -> Type -> Type) -> Scheme
forall3 f = Forall [TV "a", TV "b", TV "c"]
  (f (TVar (TV "a")) (TVar (TV "b")) (TVar (TV "c")))

infixr 9 ~>
(~>) :: Type -> Type -> Type
(~>) = TArr

-------------------------------------------------------------------------------
-- Parser Tests
-------------------------------------------------------------------------------

parserTests :: TestTree
parserTests = testGroup "Parser"
  [ testCase "integer literal" $ do
      let Right e = parseExpr "42"
      e @?= Lit (LInt 42)

  , testCase "boolean literal True" $ do
      let Right e = parseExpr "True"
      e @?= Lit (LBool True)

  , testCase "boolean literal False" $ do
      let Right e = parseExpr "False"
      e @?= Lit (LBool False)

  , testCase "variable" $ do
      let Right e = parseExpr "x"
      e @?= Var "x"

  , testCase "lambda" $ do
      let Right e = parseExpr "\\x -> x"
      e @?= Lam "x" (Var "x")

  , testCase "multi-arg lambda" $ do
      let Right e = parseExpr "\\x y -> x"
      e @?= Lam "x" (Lam "y" (Var "x"))

  , testCase "application" $ do
      let Right e = parseExpr "f x"
      e @?= App (Var "f") (Var "x")

  , testCase "application is left-associative" $ do
      let Right e = parseExpr "f x y"
      e @?= App (App (Var "f") (Var "x")) (Var "y")

  , testCase "let expression" $ do
      let Right e = parseExpr "let x = 1 in x"
      e @?= Let "x" (Lit (LInt 1)) (Var "x")

  , testCase "if-then-else" $ do
      let Right e = parseExpr "if True then 1 else 2"
      e @?= If (Lit (LBool True)) (Lit (LInt 1)) (Lit (LInt 2))

  , testCase "arithmetic operators" $ do
      let Right e = parseExpr "1 + 2"
      e @?= Op Add (Lit (LInt 1)) (Lit (LInt 2))

  , testCase "operator precedence: * binds tighter than +" $ do
      let Right e = parseExpr "1 + 2 * 3"
      e @?= Op Add (Lit (LInt 1)) (Op Mul (Lit (LInt 2)) (Lit (LInt 3)))

  , testCase "equality operator" $ do
      let Right e = parseExpr "x == 0"
      e @?= Op Eql (Var "x") (Lit (LInt 0))

  , testCase "fix expression" $ do
      let Right e = parseExpr "fix f"
      e @?= Fix (Var "f")

  , testCase "parenthesized expression" $ do
      let Right e = parseExpr "(1 + 2) * 3"
      e @?= Op Mul (Op Add (Lit (LInt 1)) (Lit (LInt 2))) (Lit (LInt 3))

  , testCase "top-level let declaration" $ do
      let Right m = parseModule "<test>" "let f x = x;"
      m @?= [("f", Lam "x" (Var "x"))]

  , testCase "top-level let rec declaration" $ do
      let Right m = parseModule "<test>" "let rec f x = f x;"
      m @?= [("f", Fix (Lam "f" (Lam "x" (App (Var "f") (Var "x")))))]

  , testCase "multiple declarations" $ do
      let Right m = parseModule "<test>" "let x = 1;\nlet y = 2;"
      length m @?= 2

  , testCase "parse failure returns Left" $ do
      let result = parseExpr "let = ="
      case result of
        Left _  -> return ()
        Right _ -> assertFailure "expected parse error"
  ]

-------------------------------------------------------------------------------
-- Type Inference Tests
-------------------------------------------------------------------------------

typeInferenceTests :: TestTree
typeInferenceTests = testGroup "Type Inference"
  [ testGroup "Literals"
    [ testCase "integer literal has type Int" $ do
        let Right ty = inferFromText "42"
        ty @?= mono typeInt

    , testCase "boolean literal has type Bool" $ do
        let Right ty = inferFromText "True"
        ty @?= mono typeBool
    ]

  , testGroup "Lambda & Application"
    [ testCase "identity function: forall a. a -> a" $ do
        let Right ty = inferFromText "\\x -> x"
        ty @?= forall1 (\a -> a ~> a)

    , testCase "const function: forall a b. a -> b -> a" $ do
        let Right ty = inferFromText "\\x y -> x"
        ty @?= forall2 (\a b -> a ~> b ~> a)

    , testCase "apply identity to int" $ do
        let Right ty = inferFromText "(\\x -> x) 1"
        ty @?= mono typeInt
    ]

  , testGroup "Arithmetic"
    [ testCase "addition: Int" $ do
        let Right ty = inferFromText "1 + 2"
        ty @?= mono typeInt

    , testCase "subtraction: Int" $ do
        let Right ty = inferFromText "3 - 1"
        ty @?= mono typeInt

    , testCase "multiplication: Int" $ do
        let Right ty = inferFromText "2 * 3"
        ty @?= mono typeInt

    , testCase "equality: Bool" $ do
        let Right ty = inferFromText "1 == 2"
        ty @?= mono typeBool

    , testCase "arithmetic lambda: Int -> Int -> Int" $ do
        let Right ty = inferFromText "\\x y -> x + y"
        ty @?= mono (typeInt ~> typeInt ~> typeInt)
    ]

  , testGroup "If-then-else"
    [ testCase "if-then-else with ints" $ do
        let Right ty = inferFromText "if True then 1 else 2"
        ty @?= mono typeInt

    , testCase "if-then-else with bools" $ do
        let Right ty = inferFromText "if True then False else True"
        ty @?= mono typeBool
    ]

  , testGroup "Let polymorphism"
    [ testCase "let id = \\x -> x in id 1" $ do
        let Right ty = inferFromText "let id = \\x -> x in id 1"
        ty @?= mono typeInt

    , testCase "let id = \\x -> x in id True" $ do
        let Right ty = inferFromText "let id = \\x -> x in id True"
        ty @?= mono typeBool

    , testCase "let polymorphism: id used at two types" $ do
        -- id is used as (Int -> Int) and (Bool -> Bool)
        let Right ty = inferFromText
              "let id = \\x -> x in let a = id 1 in id True"
        ty @?= mono typeBool

    , testCase "nested let polymorphism" $ do
        let Right ty = inferFromText
              "let const = \\x y -> x in let f = const 1 in f True"
        ty @?= mono typeInt
    ]

  , testGroup "Top-level inference (inferTop)"
    [ testCase "identity function" $ do
        let Right env = inferModuleFromText "let id x = x;"
        let Just ty = Env.lookup "id" env
        ty @?= forall1 (\a -> a ~> a)

    , testCase "const function" $ do
        let Right env = inferModuleFromText "let const x y = x;"
        let Just ty = Env.lookup "const" env
        ty @?= forall2 (\a b -> a ~> b ~> a)

    , testCase "compose function" $ do
        let Right env = inferModuleFromText "let compose f g = \\x -> f (g x);"
        let Just ty = Env.lookup "compose" env
        ty @?= forall3 (\a b c -> (a ~> b) ~> (c ~> a) ~> c ~> b)

    , testCase "successor function" $ do
        let Right env = inferModuleFromText "let succ x = x + 1;"
        let Just ty = Env.lookup "succ" env
        ty @?= mono (typeInt ~> typeInt)

    , testCase "recursive factorial" $ do
        let Right env = inferModuleFromText
              "let rec fact n = if (n == 0) then 1 else (n * (fact (n - 1)));"
        let Just ty = Env.lookup "fact" env
        ty @?= mono (typeInt ~> typeInt)

    , testCase "recursive fibonacci" $ do
        let Right env = inferModuleFromText $ L.unlines
              [ "let rec fib n ="
              , "  if (n == 0) then 0"
              , "  else if (n == 1) then 1"
              , "  else ((fib (n - 1)) + (fib (n - 2)));"
              ]
        let Just ty = Env.lookup "fib" env
        ty @?= mono (typeInt ~> typeInt)

    , testCase "multiple definitions share environment" $ do
        let Right env = inferModuleFromText $ L.unlines
              [ "let id x = x;"
              , "let foo = id 1;"
              ]
        let Just ty = Env.lookup "foo" env
        ty @?= mono typeInt

    , testCase "SKI combinators" $ do
        let Right env = inferModuleFromText $ L.unlines
              [ "let I x = x;"
              , "let K x y = x;"
              , "let S f g x = f x (g x);"
              ]
        let Just ti = Env.lookup "I" env
        ti @?= forall1 (\a -> a ~> a)

        let Just tk = Env.lookup "K" env
        tk @?= forall2 (\a b -> a ~> b ~> a)
    ]

  , testGroup "Fix operator"
    [ testCase "fix-based factorial" $ do
        let Right ty = inferFromText
              "fix (\\fact -> \\n -> if (n == 0) then 1 else (n * (fact (n - 1))))"
        ty @?= mono (typeInt ~> typeInt)
    ]
  ]

-------------------------------------------------------------------------------
-- Evaluation Tests
-------------------------------------------------------------------------------

evalTests :: TestTree
evalTests = testGroup "Evaluation"
  [ testCase "integer literal" $ do
      let Right e = parseExpr "42"
      let (val, _) = runEval emptyTmenv "it" e
      show val @?= "42"

  , testCase "boolean literal" $ do
      let Right e = parseExpr "True"
      let (val, _) = runEval emptyTmenv "it" e
      show val @?= "True"

  , testCase "addition" $ do
      let Right e = parseExpr "1 + 2"
      let (val, _) = runEval emptyTmenv "it" e
      show val @?= "3"

  , testCase "subtraction" $ do
      let Right e = parseExpr "10 - 3"
      let (val, _) = runEval emptyTmenv "it" e
      show val @?= "7"

  , testCase "multiplication" $ do
      let Right e = parseExpr "3 * 4"
      let (val, _) = runEval emptyTmenv "it" e
      show val @?= "12"

  , testCase "equality true" $ do
      let Right e = parseExpr "1 == 1"
      let (val, _) = runEval emptyTmenv "it" e
      show val @?= "True"

  , testCase "equality false" $ do
      let Right e = parseExpr "1 == 2"
      let (val, _) = runEval emptyTmenv "it" e
      show val @?= "False"

  , testCase "identity application" $ do
      let Right e = parseExpr "(\\x -> x) 42"
      let (val, _) = runEval emptyTmenv "it" e
      show val @?= "42"

  , testCase "const application" $ do
      let Right e = parseExpr "(\\x y -> x) 1 2"
      let (val, _) = runEval emptyTmenv "it" e
      show val @?= "1"

  , testCase "let binding" $ do
      let Right e = parseExpr "let x = 10 in x + 1"
      let (val, _) = runEval emptyTmenv "it" e
      show val @?= "11"

  , testCase "nested let" $ do
      let Right e = parseExpr "let x = 1 in let y = 2 in x + y"
      let (val, _) = runEval emptyTmenv "it" e
      show val @?= "3"

  , testCase "if-then-else true branch" $ do
      let Right e = parseExpr "if True then 1 else 2"
      let (val, _) = runEval emptyTmenv "it" e
      show val @?= "1"

  , testCase "if-then-else false branch" $ do
      let Right e = parseExpr "if False then 1 else 2"
      let (val, _) = runEval emptyTmenv "it" e
      show val @?= "2"

  , testCase "complex arithmetic" $ do
      let Right e = parseExpr "(2 + 3) * (10 - 6)"
      let (val, _) = runEval emptyTmenv "it" e
      show val @?= "20"

  , testCase "factorial via module" $ do
      let Right decls = parseModule "<test>"
            "let rec fact n = if (n == 0) then 1 else (n * (fact (n - 1)));"
      let env = foldl evalDef emptyTmenv decls
      let Right call = parseExpr "fact 5"
      let (val, _) = runEval env "it" call
      show val @?= "120"

  , testCase "fibonacci via module" $ do
      let Right decls = parseModule "<test>" $ L.unlines
            [ "let rec fib n ="
            , "  if (n == 0) then 0"
            , "  else if (n == 1) then 1"
            , "  else ((fib (n - 1)) + (fib (n - 2)));"
            ]
      let env = foldl evalDef emptyTmenv decls
      let Right call = parseExpr "fib 10"
      let (val, _) = runEval env "it" call
      show val @?= "55"
  ]

evalDef :: TermEnv -> (String, Expr) -> TermEnv
evalDef env (nm, ex) = snd (runEval env nm ex)

-------------------------------------------------------------------------------
-- Error Tests
-------------------------------------------------------------------------------

errorTests :: TestTree
errorTests = testGroup "Type Errors"
  [ testCase "unbound variable" $ do
      let result = inferFromText "x"
      case result of
        Left (UnboundVariable _) -> return ()
        Left err  -> assertFailure $ "expected UnboundVariable, got: " ++ show err
        Right _   -> assertFailure "expected type error"

  , testCase "type mismatch in if branches" $ do
      let result = inferFromText "if True then 1 else False"
      case result of
        Left _ -> return ()
        Right _ -> assertFailure "expected type error"

  , testCase "non-boolean condition" $ do
      let result = inferFromText "if 1 then 2 else 3"
      case result of
        Left _ -> return ()
        Right _ -> assertFailure "expected type error"

  , testCase "infinite type (occurs check)" $ do
      let result = inferFromText "\\x -> x x"
      case result of
        Left (InfiniteType _ _) -> return ()
        Left err  -> assertFailure $ "expected InfiniteType, got: " ++ show err
        Right _   -> assertFailure "expected type error"

  , testCase "adding bool to int" $ do
      let result = inferFromText "True + 1"
      case result of
        Left _ -> return ()
        Right _ -> assertFailure "expected type error"
  ]

-------------------------------------------------------------------------------
-- Integration Tests
-------------------------------------------------------------------------------

integrationTests :: TestTree
integrationTests = testGroup "Integration (test.ml subset)"
  [ testCase "Church booleans and SKI" $ do
      let Right env = inferModuleFromText $ L.unlines
            [ "let T x y = x;"
            , "let F x y = y;"
            , "let I x = x;"
            , "let K x y = x;"
            , "let S f g x = f x (g x);"
            ]
      -- T and K should have the same type: forall a b. a -> b -> a
      let Just tT = Env.lookup "T" env
      let Just tK = Env.lookup "K" env
      tT @?= tK

  , testCase "arithmetic functions" $ do
      let Right env = inferModuleFromText $ L.unlines
            [ "let nsucc x = x + 1;"
            , "let npred x = x - 1;"
            ]
      let Just ts = Env.lookup "nsucc" env
      ts @?= mono (typeInt ~> typeInt)
      let Just tp = Env.lookup "npred" env
      tp @?= mono (typeInt ~> typeInt)

  , testCase "boolean functions" $ do
      let Right env = inferModuleFromText $ L.unlines
            [ "let notbool x = if x then False else True;"
            , "let eqzero x = if (x == 0) then True else False;"
            ]
      let Just tn = Env.lookup "notbool" env
      tn @?= mono (typeBool ~> typeBool)
      let Just te = Env.lookup "eqzero" env
      te @?= mono (typeInt ~> typeBool)

  , testCase "higher-order functions" $ do
      let Right env = inferModuleFromText "let twice f x = f (f x);"
      let Just ty = Env.lookup "twice" env
      ty @?= forall1 (\a -> (a ~> a) ~> a ~> a)

  , testCase "let polymorphism usage" $ do
      let Right env = inferModuleFromText $ L.unlines
            [ "let I x = x;"
            , "let poly = I (I I) (I 3);"
            ]
      let Just ty = Env.lookup "poly" env
      ty @?= mono typeInt

  , testCase "self application via let" $ do
      let Right env = inferModuleFromText "let self = (\\x -> x) (\\x -> x);"
      let Just ty = Env.lookup "self" env
      ty @?= forall1 (\a -> a ~> a)

  , testCase "recursive until function" $ do
      let Right env = inferModuleFromText $ L.unlines
            [ "let rec until p f x ="
            , "  if (p x)"
            , "  then x"
            , "  else (until p f (f x));"
            ]
      let Just ty = Env.lookup "until" env
      ty @?= forall1 (\a -> (a ~> typeBool) ~> (a ~> a) ~> a ~> a)

  , testCase "full test.ml parses and type-checks" $ do
      src <- L.readFile "test.ml"
      case parseModule "test.ml" src of
        Left err -> assertFailure $ "parse error: " ++ show err
        Right decls -> case inferTop Env.empty decls of
          Left err -> assertFailure $ "type error: " ++ show err
          Right env -> do
            -- Spot-check a few definitions
            let Just factTy = Env.lookup "fact" env
            factTy @?= mono (typeInt ~> typeInt)
            let Just fibTy = Env.lookup "fib" env
            fibTy @?= mono (typeInt ~> typeInt)
  ]
