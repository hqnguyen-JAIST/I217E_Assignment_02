import TRS
import Parser
import System.Environment

-- Pretty printers

showRule :: Rule -> String
showRule (s, t) = show s ++ " = " ++ show t ++ " ."

showTRS :: TRS -> String
showTRS rules = unlines [ showRule rule | rule <- rules ]


-- Implementation
data EvaluateQuery = Evaluated | NotEvaluated
    deriving (Eq, Show)
data LazyTerm = LazyVar String EvaluateQuery | LazyCon String EvaluateQuery | LazyApp LazyTerm LazyTerm EvaluateQuery
    deriving (Eq, Show)
type Substitution = [(String, LazyTerm)]

termToLazyTerm :: Term -> LazyTerm
termToLazyTerm (Var x) = LazyVar x NotEvaluated
termToLazyTerm (Con c) = LazyCon c NotEvaluated
termToLazyTerm (App l r) = LazyApp (termToLazyTerm l) (termToLazyTerm r) NotEvaluated

lazyTermToTerm :: LazyTerm -> Term
lazyTermToTerm (LazyVar x _) = Var x
lazyTermToTerm (LazyCon c _) = Con c
lazyTermToTerm (LazyApp l r _) = App (lazyTermToTerm l) (lazyTermToTerm r)

match :: Substitution -> Term -> LazyTerm -> Maybe Substitution
match sigma (App (Con f) us) (LazyApp (LazyCon g _) vs _)
    | f == g = match sigma us vs
match sigma (Con f) (LazyCon g _)
    | f == g = Just []
match sigma (Var x) ws =
    case lookup x sigma of
        Just wsP | wsP == ws -> Just sigma
        Nothing              -> Just ((x, ws) : sigma)
match sigma (App sl sr) (LazyApp tl tr _) = 
    case match sigma sl tl of
        Just sigmaPrime -> match sigmaPrime sr tr
        Nothing         -> Nothing
match _ _ _ = Nothing

substitute :: Term -> Substitution -> Maybe LazyTerm
substitute (Var x) sigma 
    | Just t <- lookup x sigma = Just t
substitute (Con c) sigma = Just (LazyCon c Evaluated)
substitute (App l r) sigma 
    | Just lP <- substitute l sigma, 
      Just rP <- substitute r sigma = Just (LazyApp lP rP NotEvaluated)
substitute _ _ = Nothing

matchOneRule :: LazyTerm -> TRS -> Maybe LazyTerm
matchOneRule s [] = Nothing
matchOneRule s ((u, v) : rs) =
    case match [] u s of
        Just sigma -> substitute v sigma
        Nothing    -> matchOneRule s rs

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

main = do
    file : _ <- getArgs
    m <- readTRSFile file
    case m of
        Left e    -> print e
        Right trs -> do
            case lookup (Con "main") trs of
                Just s -> case evaluate (termToLazyTerm s) trs of 
                    Just result -> print (lazyTermToTerm result)

-- putStrLn (showTRS trs)
-- putStrLn (show (nf1 trs (Con "main")))
-- putStrLn (show (nf2 trs (MCon "main")))
-- putStrLn (show (nf3 trs (Hole, MCon "main")))

