module Eval where

import Syntax

import Control.Monad.Identity
import qualified Data.Map as Map

data Value
  = VInt Integer
  | VBool Bool
  | VClosure String Expr TermEnv

type TermEnv = Map.Map String Value
type Interpreter t = Identity t

emptyTmenv :: TermEnv
emptyTmenv = Map.empty

instance Show Value where
  show (VInt n) = show n
  show (VBool n) = show n
  show VClosure{} = "<<closure>>"

eval :: TermEnv -> Expr -> Interpreter Value
eval env expr = case expr of
  Lit (LInt k)  -> return $ VInt k
  Lit (LBool k) -> return $ VBool k

  Var x ->
    case Map.lookup x env of
      Just v  -> return v
      Nothing -> error $ "unbound variable: " ++ x

  Op op a b -> do
    a' <- eval env a
    b' <- eval env b
    case (a', b') of
      (VInt av, VInt bv) -> return $ (binop op) av bv
      _ -> error "type error in binary operation"

  Lam x body ->
    return (VClosure x body env)

  App fun arg -> do
    funVal <- eval env fun
    case funVal of
      VClosure x body clo -> do
        argv <- eval env arg
        let nenv = Map.insert x argv clo
        eval nenv body
      _ -> error "type error in application"

  Let x e body -> do
    e' <- eval env e
    let nenv = Map.insert x e' env
    eval nenv body

  If cond tr fl -> do
    condVal <- eval env cond
    case condVal of
      VBool br ->
        if br then eval env tr
        else eval env fl
      _ -> error "type error in conditional"

  Fix e -> do
    eval env (App e (Fix e))

binop :: Binop -> Integer -> Integer -> Value
binop Add a b = VInt $ a + b
binop Mul a b = VInt $ a * b
binop Sub a b = VInt $ a - b
binop Eql a b = VBool $ a == b

runEval :: TermEnv -> String -> Expr -> (Value, TermEnv)
runEval env nm ex =
  let res = runIdentity (eval env ex) in
  (res, Map.insert nm res env)
