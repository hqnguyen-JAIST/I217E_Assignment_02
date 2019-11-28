-- name: Nguyen Quoc Huy
-- id: 1910410
-- acknowledgements: 

import TRS
import Parser
import System.Environment

-- Pretty printers

showRule :: Rule -> String
showRule (s, t) = show s ++ " = " ++ show t ++ " ."

showTRS :: TRS -> String
showTRS rules = unlines [ showRule rule | rule <- rules ]


-- Implementation

-- | Use two evaluation flags (Evaluated and NotEvaluated) to evaluate that whether a term is evaluated or not
data EvaluateQuery = Evaluated | NotEvaluated
  deriving (Eq, Show)

-- | The termz that contain the evaluation flag
data LazyTerm = LazyVar String EvaluateQuery | LazyCon String EvaluateQuery | LazyApp LazyTerm LazyTerm EvaluateQuery
    deriving (Eq, Show)

-- | Substitution maps variable name (string) to a lazy term
type Substitution = [(String, LazyTerm)]

-- | Convert term to lazy term
termToLazyTerm :: Term -> LazyTerm
termToLazyTerm (Var x) = LazyVar x NotEvaluated
termToLazyTerm (Con c) = LazyCon c NotEvaluated
termToLazyTerm (App l r) = LazyApp (termToLazyTerm l) (termToLazyTerm r) NotEvaluated

-- | Convert lazy term to term
lazyTermToTerm :: LazyTerm -> Term
lazyTermToTerm (LazyVar x _) = Var x
lazyTermToTerm (LazyCon c _) = Con c
lazyTermToTerm (LazyApp l r _) = App (lazyTermToTerm l) (lazyTermToTerm r)

-- | Find substitution that match one term to another (lazy) term
match :: Substitution -> Term -> LazyTerm -> Maybe Substitution
match sigma (App (Con f) us) (LazyApp (LazyCon g _) vs _)
  | f == g = match sigma us vs
match sigma (Con f) (LazyCon g _)
  | f == g = Just sigma
match sigma (Var x) ws =
  case lookup x sigma of
    Just wsP | wsP == ws -> Just sigma
    Nothing              -> Just ((x, ws) : sigma)
match sigma (App sl sr) (LazyApp tl tr _) = 
  case match sigma sl tl of
    Just sigmaPrime -> match sigmaPrime sr tr
    Nothing         -> Nothing
match _ _ _ = Nothing

-- | Apply a substitution on a term, return a lazy term
substitute :: Term -> Substitution -> Maybe LazyTerm
substitute (Var x) sigma 
  | Just t <- lookup x sigma = Just t
substitute (Con c) sigma = Just (LazyCon c Evaluated)
substitute (App l r) sigma 
  | Just lP <- substitute l sigma, 
    Just rP <- substitute r sigma = Just (LazyApp lP rP NotEvaluated)
substitute _ _ = Nothing

-- | Find one rule in a set of rules and apply that rule on the given lazy term
matchOneRule :: LazyTerm -> TRS -> Maybe LazyTerm
matchOneRule s [] = Nothing
matchOneRule s ((u, v) : rs) =
  case match [] u s of
    Just sigma -> substitute v sigma
    Nothing    -> matchOneRule s rs

-- | Transform lazy term until it is in normal form
evaluate :: LazyTerm -> TRS -> Maybe LazyTerm
evaluate (LazyApp u v Evaluated) rs = Just (LazyApp u v Evaluated)
evaluate (LazyApp u v NotEvaluated) rs = 
  (\(utt, vtt) rsss ->
    case matchOneRule (LazyApp utt vtt NotEvaluated) rsss of
      Just t  -> evaluate t rsss
      Nothing -> Just (LazyApp utt vtt Evaluated)
  ) ((\ut vt rss -> 
    case (evaluate vt rss, evaluate ut rss) of
      (Just vP, Just uP) -> (uP, vP)
      (Just vP, Nothing) -> (ut, vP)
      (Nothing, Just uP) -> (uP, vt)
      (Nothing, Nothing) -> (ut, vt)
  ) u v rs) rs 
evaluate (LazyCon f Evaluated) rs = Just (LazyCon f Evaluated)
evaluate (LazyCon f NotEvaluated) rs =
  case matchOneRule (LazyCon f NotEvaluated) rs of
    Just t  -> evaluate t rs
    Nothing -> Just (LazyCon f Evaluated)
evaluate (LazyVar x Evaluated) rs = Just (LazyVar x Evaluated)
evaluate (LazyVar x NotEvaluated) rs =
  case matchOneRule (LazyVar x NotEvaluated) rs of
    Just t  -> evaluate t rs
    Nothing -> Just (LazyVar x Evaluated)

-- | This function is for debugging: do ONE transformation step
next :: LazyTerm -> TRS -> Maybe LazyTerm
next (LazyApp u v Evaluated) rs = Nothing
next (LazyApp u v NotEvaluated) rs = 
  case next v rs of
    Just vP -> Just (LazyApp u vP NotEvaluated)
    Nothing ->
      case next u rs of
        Just uP -> Just (LazyApp uP v NotEvaluated)
        Nothing -> matchOneRule (LazyApp u v NotEvaluated) rs 
next (LazyCon f Evaluated) rs = Nothing
next (LazyCon f NotEvaluated) rs = matchOneRule (LazyCon f NotEvaluated) rs
next (LazyVar x Evaluated) rs = Nothing
next (LazyVar x NotEvaluated) rs = matchOneRule (LazyVar x NotEvaluated) rs

-- | This function is for debugging: print all transformation steps
getNext :: LazyTerm -> Int -> TRS -> IO ()
getNext t k rs = do
  print k
  print (lazyTermToTerm t)
  case next t rs of
    Just s  -> getNext s (k+1) rs
    Nothing -> print "Finish"

-- | This function is for debugging: check debug mode
getMode [] = Nothing
getMode (arg : _) =
  case arg of
    "DEBUG" -> Just arg
    _       -> Nothing

main = do
  file : otherArgs <- getArgs
  m <- readTRSFile file
  case m of
    Left e    -> print e
    Right trs -> do
      putStrLn (showTRS trs)
      case lookup (Con "main") trs of
        Just s  -> 
          case getMode otherArgs of
            Just "DEBUG" -> getNext (termToLazyTerm s) 0 trs
            Nothing      ->
              case evaluate (termToLazyTerm s) trs of 
                Just result -> print (lazyTermToTerm result)
                Nothing     -> print "Cannot trasnform to normal form"
        Nothing -> print "Cannot find main function"

