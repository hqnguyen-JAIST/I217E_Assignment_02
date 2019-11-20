import TRS
import Parser
import System.Environment

-- Pretty printers

showRule :: Rule -> String
showRule (s, t) = show s ++ " = " ++ show t ++ " ."

showTRS :: TRS -> String
showTRS rules = unlines [ showRule rule | rule <- rules ]


-- Implementation
type Substitution = [(String, Term)]

match :: Substitution -> Term -> Term -> Maybe Substitution
match sigma (App (Con f) us) (App (Con g) vs)
    | f == g = match sigma us vs
match sigma (Con f) (Con g)
    | f == g = Just []
match sigma (Var x) ws =
    case lookup x sigma of
        Just wsP | wsP == ws -> Just sigma
        Nothing              -> Just ((x, ws) : sigma)
match sigma (App sl sr) (App tl tr) = 
    case match sigma sl tl of
        Just sigmaPrime -> match sigmaPrime sr tr
        Nothing         -> Nothing
match _ _ _ = Nothing

substitute :: Term -> Substitution -> Maybe Term
substitute (Var x) sigma 
    | Just t <- lookup x sigma = Just t
substitute (Con c) sigma = Just (Con c)
substitute (App l r) sigma 
    | Just lP <- substitute l sigma, 
      Just rP <- substitute r sigma = Just (App lP rP)
substitute _ _ = Nothing

matchOneRule :: Term -> TRS -> Maybe Term
matchOneRule s [] = Nothing
matchOneRule s ((u, v) : rs) =
    case match [] u s of
        Just sigma -> substitute v sigma
        Nothing    -> matchOneRule s rs

evaluate :: Term -> TRS -> Maybe Term
evaluate (App u v) rs = 
    (\(App utt vtt) rsss ->
        case matchOneRule (App utt vtt) rsss of 
            Just t  -> evaluate t rsss
            Nothing -> Just (App utt vtt)
    ) ((\(App ut vt) rss -> 
        case (evaluate vt rss, evaluate ut rss) of
            (Just vP, Just uP) -> (App uP vP)
            (Just vP, Nothing) -> (App ut vP)
            (Nothing, Just uP) -> (App uP vt)
            (Nothing, Nothing) -> (App ut vt)
    ) (App u v) rs) rs 
evaluate (Con f) rs =
    case matchOneRule (Con f) rs of
        Just t  -> evaluate t rs
        Nothing -> Just (Con f)
evaluate (Var x) rs =
    case matchOneRule (Var x) rs of
        Just t  -> evaluate t rs
        Nothing -> Just (Var x)

main = do
    file : _ <- getArgs
    m <- readTRSFile file
    case m of
        Left e    -> print e
        Right trs -> do
            case lookup (Con "main") trs of
                Just s -> case evaluate s trs of 
                    Just result -> print result
-- putStrLn (showTRS trs)
-- putStrLn (show (nf1 trs (Con "main")))
-- putStrLn (show (nf2 trs (MCon "main")))
-- putStrLn (show (nf3 trs (Hole, MCon "main")))

