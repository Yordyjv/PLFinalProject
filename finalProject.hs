import Data.Char
import Language.Haskell.TH (safe)
import Control.Monad.RWS (MonadState(put))
--Worked with Kevin Portillo

type FunList = Either AExpr BExpr 
type FName = String  --Function names 

type Vars = String -- Variables

data AExpr = Var Vars | Const Integer -- Arithmetic expressions
    | Add AExpr AExpr | Sub AExpr AExpr
    | Mul AExpr AExpr | Div AExpr AExpr
    | Mod AExpr 
    | FCallA AExpr --returns the evaluated function 
    deriving Show
data BExpr = TT | FF -- Boolean expressions
    | And BExpr BExpr | Or BExpr BExpr | Not BExpr
    | Eql AExpr AExpr -- equality of arithmetic expressions
    | Lt AExpr AExpr -- true if the first is less than the second
    | Lte AExpr AExpr -- true if it’s less than or equal to
    | Gre BExpr BExpr | Gr BExpr BExpr --NEW
    | FCallB BExpr --returns the evaluated function 
    deriving Show

data Instr = Assign Vars AExpr -- assignment
    | IfThenElse BExpr Instr Instr -- conditional
    | While BExpr Instr -- looping construct
    | Do [Instr] -- a block of several instructions
    | Nop -- the "do nothing" instruction
    | FAssign FunDef
    | Return AExpr -- the final value to return
    | FCall FName [Value]
    deriving Show


data Keywords = IfK | ThenK | ElseK | WhileK | NopK | ReturnK 
    | ClassK | MainK | IntegerK | BooleanK | NewK | 
    FunK | PublicK | PrivateK
    deriving Show
data UOps = NotOp deriving Show 
data BOps = AddOp | SubOp | MulOp | DivOp
    | AndOp | OrOp | EqlOp | LtOp | LteOp
    | ModOp | GreOp | GrOp
    deriving Show

data Token = VSym String | CSym Integer | BSym Bool
    | NSym String --Starts with uppercase letter, followed by 0 or more letters/digits
    | LPar | RPar | LBra | RBra | Semi | Comma
    | UOp UOps | BOp BOps | AssignOp
    | Keyword Keywords
    | Err String
    | LSqu | RSqu
    | PA AExpr | PB BExpr | PI Instr | Block [Instr] | Input Value | Param VName
    | Params [VName] | Inputs[Value]
    | FunDefT FunDef
    deriving Show


--FUNCTIONS, CLASSES 

type VName = String 
type Value = Integer 
type VEnv = [(VName, Value)] --fields

type FEnv = [FunDef] -- fundefs

type Env = (VEnv, FEnv) --class enviorments

--type ClassName = String 
--type Object = [(ClassName, Class)] 


data FunDef = FunDef { fname :: FName 
                        , params :: VEnv
                        , body :: [Instr]  }
                        deriving Show

-- Fun def has params and body. 
-- Params have a value and a name, VEnv
--
--FunDef is function definition. Value is values to be put in original params

--evalFunDef :: FunDef -> [Value] -> Either AExpr BExpr
--evalFunDef = 





-- update (x,v) e sets the value of x to v and keeps other variables in e the same
updateV :: (Vars, Integer) -> VEnv -> VEnv
updateV (x, v) [] = [(x, v)] 
updateV (x, v) ((e, val):env)
    | x /= e    = (e, val) : updateV (x, v) env
    | otherwise = (x, v) : env





evala :: Env -> AExpr -> Integer
evala (venv,fenv) (Var x) = case lookup x venv of
                     Just val -> val
                     Nothing  -> error $ "Variable not found: " ++ x
evala env (Const b) = b
evala env (Add e1 e2) = evala env e1 + evala env e2
evala env (Sub e1 e2) = evala env e1 - evala env e2
evala env (Mul e1 e2) = evala env e1 * evala env e2
evala env (Div e1 e2) = evala env e1 `div` evala env e2

evalb :: Env -> BExpr -> Bool
evalb env TT = True
evalb env FF = False
evalb env (And p1 p2) = evalb env p1 && evalb env p2
evalb env (Or p1 p2) = evalb env p1 || evalb env p2
evalb env (Not p1) = not (evalb env p1)
evalb env (Eql p1 p2)
    | evala env p1 == evala env p2 = evalb env TT
    | otherwise = evalb env FF
evalb env (Lt p1 p2)
    | evala env p1 < evala env p2 = evalb env TT
    | otherwise = evalb env FF
evalb env (Lte p1 p2)
    | evala env p1 <= evala env p2 = evalb env TT
    | otherwise = evalb env FF

exec :: Instr -> Env -> Env
exec (Assign v a) env = (updateV (v, evala env a) (fst env), snd env)
exec (FAssign fundef) (venv,fenv) = (venv, fundef:fenv)
exec (IfThenElse condI thenI elseI) env =
    if evalb env condI
        then exec thenI env
        else exec elseI env
exec (While condI doI) env =
    if evalb env condI
        then exec (While condI doI) (exec doI env)
        else env
exec (Do instrs) env = foldl (\e i -> exec i e) env instrs
exec Nop env = env
exec (FCall n vs) env = callFun n (setParms n vs env)
exec (Return a) env = (updateV ("", evala env a) (fst env), snd env)

setParms :: FName -> [Value] -> Env -> Env
setParms fn vs env@(venv, fenv) = case lookup fn [(fname f, f) | f <- fenv] of
    Just fundef -> 
        let varnames = map fst (params fundef)
            newparams = zip varnames vs
            newFundef = fundef { params = newparams }
            newFenv = map (\f -> if fname f == fn then newFundef else f) fenv
        in (venv, newFenv)
    Nothing -> env

callFun :: FName -> Env -> Env
callFun fn env@(venv, fenv) = case lookup fn [(fname f, f) | f <- fenv] of
    Just fundef ->  let {params' = params fundef; body' = body fundef} in execList body' (params', fenv)
    Nothing -> env


--lokup the function in fenv of env
--then map [values] to [var(strs)] output [(vars,values)]


execList :: [Instr] -> Env -> Env
execList instrs env = foldl (\e i -> exec i e) env instrs




--Example
sum100 :: [Instr] -- a program to add together all the numbers up to 100
sum100 = [
    Assign "X" (Const 0), -- initialize the sum at X=0
    Assign "C" (Const 1), -- initialize the counter at C=1
    While (Lt (Var "C") (Const 101)) -- while C < 101, do:
        (Do [Assign "X" (Add (Var "X") (Var "C")), -- X := X + C;
            Assign "C" (Add (Var "C") (Const 1))]), -- C := C + 1
    Return (Var "X")]

sum100output = run sum100


lexer :: String -> [Token]
lexer "" = []
--Punctuation
lexer ('(':xs)      = LPar : lexer xs                --Left parenthesis case 
lexer (')':xs)      = RPar : lexer xs                --Right parenthesis case
lexer ('{':xs)      = LBra : lexer xs                --Left bracket case 
lexer ('}':xs)      = RBra : lexer xs                --Right bracket case
lexer ('[':xs)      = LSqu : lexer xs 
lexer (']':xs)      = RSqu : lexer xs 
lexer(',':xs)= Comma : lexer xs
lexer (';':xs)      = Semi : lexer xs
--Constants
lexer ('T':'r':'u':'e':xs)          = BSym True : lexer xs      --Boolean constant True
lexer ('F':'a':'l':'s':'e':xs)      = BSym False : lexer xs     --Boolean constant False
--Keywords
lexer ('w':'h':'i':'l':'e':xs)      = Keyword WhileK : lexer xs
lexer ('i':'f':xs)                  = Keyword IfK : lexer xs
lexer ('t':'h':'e':'n':xs)          = Keyword ThenK : lexer xs
lexer ('e':'l':'s':'e':xs)          = Keyword ElseK : lexer xs
lexer ('n':'o':'p':xs)              = Keyword NopK : lexer xs
lexer ('r':'e':'t':'u':'r':'n':xs)  = Keyword ReturnK : lexer xs
--Classes & functions  
lexer ('C':'l':'a':'s':'s':xs)      = Keyword ClassK : lexer xs --class
lexer ('m':'a':'i':'n':xs)          = Keyword MainK : lexer xs  --main
lexer ('p':'u':'b':'l':'i':'c':xs)      = Keyword PublicK : lexer xs    --public function
lexer ('p':'r':'i':'v':'a':'t':'e':xs)      = Keyword PrivateK : lexer xs --private function
lexer ('i':'n':'t':xs)                     =Keyword IntegerK : lexer xs --int return type
lexer ('b':'o':'o':'l':'e':'a':'n':xs) = Keyword BooleanK : lexer xs --boolean return type 
--Variables
--Operators
lexer ('+':xs)          = BOp AddOp : lexer xs
lexer ('-':xs)          = BOp SubOp : lexer xs
lexer ('*':xs)          = BOp MulOp : lexer xs
lexer ('/':'\\':xs)         = BOp AndOp : lexer xs
lexer ('/':xs)          = BOp DivOp : lexer xs
lexer ('\\' : '/':xs)       = BOp OrOp : lexer xs
lexer ('!':xs)              = UOp NotOp : lexer xs
lexer ('=':'=':xs)          = BOp EqlOp : lexer xs
lexer ('<':'=':xs)          = BOp LteOp : lexer xs
lexer ('<':xs)              = BOp LtOp : lexer xs
lexer (':':'=':xs)          = AssignOp : lexer xs
--space
lexer (x:xs) | isSpace x = lexer xs --space
lexer (x:xs) | isDigit x = let (ys,zs) = span isDigit xs    in CSym (read (x:ys)) : lexer zs --number
lexer (x:xs) | isLower x = let (ys,zs) = span isAlphaNum xs in VSym (x:ys) : lexer zs       --variable name
lexer (x:xs) | isUpper x = let (ys,zs) = span isAlphaNum xs in NSym (x:ys) : lexer zs       --function names 
lexer xs                 = [Err xs]

parse :: [Token] -> Either [Instr] String
parse tokens = case sr [] tokens of
    (Block instructions : []) -> Left instructions
    (Err e : _) -> Right ("Lexical Error: " ++ e)
    _ -> Right "Parse Error: Invalid program structure"

sr :: [Token] -> [Token] -> [Token]
--reduce phase
    --Variable (PA)
sr (VSym v : ts) i = sr (PA (Var v) : ts) i     --Variable AEXpr
    --Constants (PA or PB) 
sr (CSym c : ts) i = sr (PA (Const c) : ts) i   --Constant AExpr
sr (BSym True : ts) i = sr (PB (TT) : ts) i     --Constant True
sr (BSym False : ts) i = sr (PB (FF) : ts) i    --Constant False
    --Unary Operations (PA, PB or PI)
sr (UOp u : ts) i = sr (UOp (NotOp) : ts) i  --UOp
    --Binary Operations 
sr s@(PB e1 : BOp o : PB e2 : ts) (BOp o2 : i) | rank o > rank o2 = sr (BOp o2 : s) i -- Binary Op BExpr
sr s@(PA e1 : BOp o : PA e2 : ts) (BOp o2 : i) | rank o > rank o2 = sr (BOp o2 : s) i -- Binary Op AExpr
    --Boolean Operators 
sr (PB e2 : BOp AndOp : PB e1 : ts) i = sr (PB (And e1 e2) : ts) i
sr (PB e2 : BOp OrOp : PB e1 : ts) i = sr (PB (Or e1 e2) : ts) i
sr (PA e2 : BOp EqlOp : PA e1 : ts) i = sr (PB (Eql e1 e2) : ts) i
sr (PA e2 : BOp LteOp : PA e1 : ts) i = sr (PB (Lte e1 e2) : ts) i
sr (PA e2 : BOp LtOp : PA e1 : ts) i = sr (PB (Lt e1 e2) : ts) i
    --Mathematical Operators 
sr (PA e2 : BOp AddOp : PA e1 : ts) i = sr (PA (Add e1 e2) : ts) i
sr (PA e2 : BOp SubOp : PA e1 : ts) i = sr (PA (Sub e1 e2) : ts) i
sr (PA e2 : BOp MulOp : PA e1 : ts) i = sr (PA (Mul e1 e2) : ts) i  
sr (PA e2 : BOp DivOp : PA e1 : ts) i = sr (PA (Div e1 e2) : ts) i   
    --Assign
sr (PA e : AssignOp : PA (Var v) : ts) q = sr (PI (Assign v e) : ts) q  

    --IfThenElse
sr (PI i2 : Keyword ElseK : PI i1 : Keyword ThenK : PB b : Keyword IfK : ts ) q
    = sr (PI (IfThenElse b i1 i2 ) : ts ) q                             
    --Nop
sr (Keyword NopK : ts) q = sr (PI (Nop) : ts) q

-----------------

sr (RSqu : Inputs es : NSym n : ts) q = sr (PI (FCall n (reverse es)) : ts) q

sr (LSqu: s) q = sr (Inputs [] : s) q 
sr(Comma : PA (Const c) : Inputs es: s) q = sr (Inputs (c:es):s) q
sr(RSqu: PA (Const c) : Inputs es:s ) q = sr (RSqu : Inputs (c:es): s) q --HERE



sr (LPar : NSym n:  s) q = sr (Params []: LPar : NSym n : s) q 
sr (Comma: PA (Var v): Params vs:s ) q = sr (Params (v:vs) : s) q
sr (RPar : PA (Var v): Params vs : s) q = sr (RPar:Params (v:vs):s) q


--Block
sr (LBra : PI i : ts)            q = sr (Block [i] : LBra : ts) q --Left bracket, start block with next instruction
sr (RBra : Semi:  PI i : ts) q = sr (Block [i] : ts) q -- RBra then Semi then instruction, means the bloc
sr (Block is : Semi : PI i : ts) q = sr (Block (i:is) : ts) q
sr (Block is : LBra : ts)        q = sr (PI (Do is) : ts)   q

sr (PI i : PB b : Keyword WhileK : ts) q = sr (PI (While b i) : ts) q
sr (PA e :Keyword ReturnK : ts) q = sr (PI (Return e) : ts) q
-- Function call
sr (PI (Do is) : RPar: Params ps : LPar : NSym n : ts) q = let defaultV = -999 :: Value in
    sr (PI (FAssign (FunDef n (zip ps (repeat defaultV)) (reverse is))) : ts) q
-- Function definition

--Syntax
sr (RPar : PI e : LPar : s) q = sr (PI e : s) q --parenthesis
sr (RPar : PA e : LPar : s) q = sr (PA e : s) q --parenthesis
sr (RPar : PB e : LPar : s) q = sr (PB e : s) q --parenthesis

sr (Semi : PI e: s) q = sr (PI e : s) q

--shift 
sr s (i:q) = sr (i:s) q 
--exit 
sr (Err e : s) _ = [Err e]
sr [Block i] [] = [Block i]
sr s [] = blocker s (Block [] : [])


blocker :: [Token] -> [Token] -> [Token]
blocker [] x = x
blocker (x:xs) (Block(i):[]) = case x of 
    RBra -> blocker xs (Block(i):[])
    PI x -> blocker xs (Block(x:i):[])
    unexpected -> [Err$ "Block Error" ++ show unexpected ++ " in " ++ show (x:xs)]

 

run :: [Instr] -> Integer
run p = case lookup "" (fst (execList p ([],[]))) of
    Just x -> x
    Nothing -> error "No value returned."


rank :: BOps -> Int
rank AddOp = 1
rank SubOp = 1
rank MulOp = 3
rank DivOp = 3
rank AndOp = 3
rank OrOp = 2

main :: IO ()
main = repl

repl :: IO ()
repl = do
    putStrLn "Enter file name:"
    fileName <- getLine
    contents <- readFile fileName
    case contents of 
        "quit" -> return () 
        s -> case parse (lexer contents) of 
            Left expr -> putStrLn ("Evaluates to: " ++ show (run expr))
            Right err -> putStrLn err
        
        

{-
adding structures to imp
various fields 
different types, some of those fields are functions 


replace parseline with parsefundef in parselines 
parselines returns Fname 

Use records 
FEnv = (Fname, ([Vars], AExpr))
instead: 
data FunDef = FunDef { fname :: FName 
                        , cars :: [Vars]
                        , body :: AExpr  }


lookupfun :: FName -> FunDef -> Maybe FunDef 
lookupFun fn [] = Nothing
lookupFun fn (fd : fdr) = if fname fd == fn then Just fc else lookupFun fn fds

replace lookup with lookupFun in eval 
Fust fundef -> 
        new env = zip (vars, fundef) 
        in eval (newEnv, fenv) (body fundef) 


parsefunDef :: [Token] -> FunDef 
now outputs fundef fn (left)

(parselines ->)
parseFunDefs
-}



{-
Changing from AEzpr to a list of instructions 
    in the function call don't return the evaluation
    create a function that executes the body of the function with the list of parameters 
ex: 
    execFun :: [Instr] -> FunDef-> Value 
    then in eval: 
        in execFun (boody fundef) (newEnc, fenv) execFun ()



lexer: 
lex function definition into Tokens 

parser:
parse function definition into record 

data TOken = ... | AccessT | InputVars [Vars] | FunDefT FunDef
data AccessT = PrivateK | PublicK 
sr (LPar : Nsym : AccessToken : s ) q = (InputVars [] : AccessT : s) q
sr (Comma : VSym x : InputVars xs : s) q = sr (InputVars (x:xs) : s) q
sr (RPar : VSym x : InputVars xs : s) q = sr (InputVars (x:xs) : s) q
sr (LBra : InputVars xs: s) q = ... 
sr(Rbra : Do is : (Lbra?) : InputVars xs : NSym f : AccessT : s) q = sr (FunDefT (FunDef {fname = f, vars = (reverse xs), body = reverse (is)}) : s) q

eval: 
evaluate record-  call a helper to evaluate the function definition, get a return value from the function 
-}


instructions :: [Instr]
instructions = 
    [ FAssign $ FunDef { fname = "bruh"
                       , params = [("x",  0)] -- Default value 0
                       , body = [ Assign "x" (Mul (Var "x") (Var "x"))
                                , Return (Var "x")
                                ]
                       }
    , FCall "bruh" [5]
    ]

testLexFun :: String
testLexFun = "Bruh(x){ x:=(x*2); return x; } Bruh[5];"

test = parse (lexer testLexFun)


{-
parse [NSym "Bruh",LPar,VSym "x",RPar,LBra,VSym "x",AssignOp,VSym "x",BOp MulOp,CSym 2,Semi,Keyword ReturnK,VSym "x",Semi,RBra,NSym "Bruh",LSqu,CSym 5,RSqu,Semi]



"Lexical Error: Block ErrorPA (Const 5) in [PA (Const 5),Params [],
NSym \"Bruh\",LPar,RBra,Semi,PI (Return (Var \"x\")),Semi,
PA (Const 2),BOp MulOp,PI (Assign \"x\" (Var \"x\")),Block [],
RPar,Params [\"x\"],NSym \"Bruh\",LPar]"

--Inputs 5 ( Bruh } ; Return x ; 2 * =: x 



-}