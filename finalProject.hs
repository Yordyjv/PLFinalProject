import Data.Char
import Language.Haskell.TH (safe)
import Control.Monad.RWS (MonadState(put))
import Data.Maybe (fromMaybe)
import System.Directory
import System.FilePath
--Worked with Kevin Portillo
--Funtions are always Camel Case
--fucntion defintions start with fname (params sep by commas)
--functions calls are fname [input vars split by commas]

--FUNCTIONS, CLASSES 

type VName = String 
type Value = Integer 
type VEnv = [(VName, Value)] --fields

type FEnv = [FunDef] -- fundefs

type Env = (VEnv, FEnv) --class enviorments



data FunDef = FunDef { fname :: FName 
                        , params :: VEnv
                        , body :: [Instr]  }
                        deriving Show


data Arg = VarArg VName | ValArg Value | FunArg (FName, [Arg]) | AExprArgs AExpr
    deriving Show


-----
data Keywords = IfK | ThenK | ElseK | WhileK | NopK | ReturnK 
    | ClassK | MainK | IntegerK | BooleanK | NewK | 
    FunK | PublicK | PrivateK
    deriving Show
data UOps = NotOp deriving Show 
data BOps = AddOp | SubOp | MulOp | DivOp
    | AndOp | OrOp | EqlOp | LtOp | LteOp
    | ModOp | GreOp | GrOp
    deriving Show
-- lexing stuff ^^


type FName = String  --Function names 
type Vars = String -- Variables

data AExpr = Var Vars | Const Integer -- Arithmetic expressions
    | Add AExpr AExpr | Sub AExpr AExpr
    | Mul AExpr AExpr | Div AExpr AExpr
    | Mod AExpr 
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
    | AssignF Vars Instr -- assingment of variables where instr is strictly a pi (FCall fn args)
    | IfThenElse BExpr Instr Instr -- conditional
    | While BExpr Instr -- looping construct
    | Do [Instr] -- a block of several instructions
    | Nop -- the "do nothing" instruction
    | FAssign FunDef
    | Return AExpr -- the final value to return
    | FCall FName [Arg] 
    deriving Show

data Token = VSym String | CSym Integer | BSym Bool
    | NSym String --Starts with uppercase letter, followed by 0 or more letters/digits
    | LPar | RPar | LBra | RBra | Semi | Comma
    | UOp UOps | BOp BOps | AssignOp
    | Keyword Keywords
    | Err String
    | LSqu | RSqu
    | PA AExpr | PB BExpr | PI Instr | Block [Instr] 
    | Params [VName] | Inputs [Arg] --inputs that are straight constants
    | FunDefT FunDef
    deriving Show


--for full OOP functionallity we would ddefine  the following
{-
a record ttpe for methods. which would have a visiablity type attched
a type visiablity with public or private
--class with a name, venv, and methods
we then would want a CENV
and and ENV to be (Venv, Fenv, Cenv)
-}

-- Fun def has params and body. 
-- Params have a value and a name, VEnv
--
--FunDef is function definition. Value is values to be put in original params







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
exec (AssignF v (FCall fn args)) env = 
    let newEnv = callFun fn (setParms fn args env) in
    (updateV (v, lookupV "" newEnv) (fst env), snd env)
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

lookupV :: Vars -> Env -> Integer
lookupV v (venv, _) = fromMaybe 0 (lookup v venv)

execList :: [Instr] -> Env -> Env
execList instrs env = foldl (\e i -> exec i e) env instrs


setParms :: FName -> [Arg] -> Env -> Env
setParms fn args env@(venv, fenv) = case lookup fn [(fname f, f) | f <- fenv] of
    Just fundef -> 
        let varnames = map fst (params fundef)
            resolvedVs = map (resolveArg env) args
            newparams = zip varnames resolvedVs
            newFundef = fundef { params = newparams }
            newFenv = map (\f -> if fname f == fn then newFundef else f) fenv
        in (venv, newFenv)
    Nothing -> env

resolveArg :: Env -> Arg -> Value
resolveArg env (VarArg v) = fromMaybe (error $ "Undefined variable: " ++ v) (lookup v (fst env))
resolveArg _ (ValArg val) = val
resolveArg env (AExprArgs expr) = evala env expr
resolveArg env (FunArg (f, args)) = case exec (FCall f args) env of
    (venv, _) -> fromMaybe (error "No return value") (lookup "" venv)

--calls and runs functions at the top level
callFun :: FName -> Env -> Env
callFun fn env@(venv, fenv) = case lookup fn [(fname f, f) | f <- fenv] of
    Just fundef ->  let {params' = params fundef; body' = body fundef} in execList body' (params', fenv)
    Nothing -> env



--lokup the function in fenv of env
--then map [values] to [var(strs)] output [(vars,values)]




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
--comments
lexer ('-':'-':xs) = lexer (dropWhile (/='\n') xs)

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
    --Assign -- helppp
sr (PA e : AssignOp : PA (Var v) : ts) q = sr ( PI (Assign v e) : ts) q 
--Assign Case where we have a x= Foo(2) this can inantly be evaluated given that foo is defined before x's assingmen
sr (PI (FCall fn args) : AssignOp : PA (Var v) : ts) q = sr ( PI (AssignF v ((FCall fn args))) : ts) q 
-- assign case where we have bruh(y){ x=foo(y); return x;} canoot be instantly evald until y is evaled. store as aexpr and in evalA have a case for that


    --IfThenElse
sr (PI i2 : Keyword ElseK :Semi :PI i1 : Keyword ThenK : PB b : Keyword IfK : ts ) q
    = sr (PI (IfThenElse b i1 i2 ) : ts ) q                             
    --Nop
sr (Keyword NopK : ts) q = sr (PI (Nop) : ts) q
-----------------
sr (RSqu : Inputs es : NSym n : ts) q = sr (PI (FCall n (reverse es)) : ts) q
--get the input varibales or constants for the function
sr (LSqu: s) q = sr (Inputs [] : s) q 
sr(Comma : PA (Const c) : Inputs es: s) q = sr (Inputs (ValArg c:es):s) q
sr(Comma : PA (Var v) : Inputs es: s) q = sr (Inputs (VarArg v:es):s) q
sr(Comma : PA a: Inputs es: s) q = sr (Inputs (AExprArgs a:es):s) q
sr(Comma : PI (FCall f args) : Inputs es: s) q = sr (Inputs (FunArg (f, args):es):s) q
sr(RSqu: PA (Const c) : Inputs es:s ) q = sr (RSqu : Inputs (ValArg c:es): s) q
sr(RSqu: PA (Var v) : Inputs es:s ) q = sr (RSqu : Inputs (VarArg v:es): s) q
sr(RSqu : PA a: Inputs es: s) q = sr (Inputs (AExprArgs a:es):s) q
sr(RSqu: PI (FCall f args) : Inputs es:s ) q = sr (RSqu : Inputs (FunArg (f, args):es): s) q
---END INPUT HANDLING -- START PARAM HANDLING -- could add type keywords here to allow for boolean params
sr (LPar : NSym n:  s) q = sr (Params []: LPar : NSym n : s) q 
sr (Comma: PA (Var v): Params vs:s ) q = sr (Params (v:vs) : s) q
sr (RPar : PA (Var v): Params vs : s) q = sr (RPar:Params (v:vs):s) q

--Block
sr (LBra : PI i : ts)            q = sr (Block [i] : LBra : ts) q --Left bracket, start block with next instruction
sr (RBra : Semi:  PI i : ts) q = sr (Block [i] : ts) q -- RBra then Semi then instruction, means the bloc
sr (Block is : Semi : PI i : ts) q = sr (Block (i:is) : ts) q
sr (Block is : LBra : ts)        q = sr (PI (Do is) : ts)   q
--- while and return
sr (PI i : PB b : Keyword WhileK : ts) q = sr (PI (While b i) : ts) q
sr (PA e :Keyword ReturnK : ts) q = sr (PI (Return e) : ts) q
-- Function defintion
sr (PI (Do is) : RPar: Params ps : LPar : NSym n : ts) q = let defaultV = -999 :: Value in
    sr (PI (FAssign (FunDef n (reverse (zip ps (repeat defaultV))) (is))) : ts) q
--Syntax
sr (RPar : PI e : LPar : s) q = sr (PI e : s) q --parenthesis
sr (RPar : PA e : LPar : s) q = sr (PA e : s) q --parenthesis
sr (RPar : PB e : LPar : s) q = sr (PB e : s) q --parenthesis

--shift 
sr s (i:q) = sr (i:s) q 
--exit 
sr (Err e : s) _ = [Err e]
sr [Block i] [] = [Block i]
sr (Semi: PI i : s) q = sr (PI i : s) q 
sr s [] = blocker s (Block [] : [])


blocker :: [Token] -> [Token] -> [Token]
--makes sure list is only semis and PI's then puts it in a block
blocker [] x = x
blocker (x:xs) (Block(i):[]) = case x of 
    RBra -> blocker xs (Block(i):[])
    Semi -> blocker xs (Block(i):[])
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
    putStrLn $ replicate 40 '~'
    putStrLn "Enter file name:"
    fileName <- getLine
    if fileName == "quit"
        then do
            putStrLn "Cya! it was fun while it lasted"
            return ()
        else do
            contents <- readFile fileName
            putStrLn $ replicate 40 'V' -- Print 40 V to show that the specific file output
            case parse (lexer contents) of 
                Left expr -> putStrLn ("Evaluates to: " ++ show (run expr))
                Right err -> putStrLn err
            putStrLn $ replicate 40 '^' -- Print 40 equals signs for separation
            repl  -- Loop back to the start
        
        

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
    , FCall "bruh" [ValArg 5]
    ]

testLexFun :: String
testLexFun = "Bruh(x){ x:=(x*2); return x; } Bruh[5];"

testLex2 :: String
testLex2 = "Bruh(x, d,y){if (x <= d) then d:=x; else while (d < x) {d:=(d+x); x:=(x+4); d:=(d-y);}; return d;} z:=17; q:=3; r:=1; Bruh[z,q,r];"

test = parse (lexer testLexFun)

runTests :: IO ()
runTests = do
        -- Get all files in the current directory
        files <- listDirectory "."

        -- Filter out the .imp files
        let impFiles = filter (\file -> takeExtension file == ".imp") files

        -- Run the interpreter on each .imp file
        mapM_ runTest impFiles
    where
        runTest file = do
                content <- readFile file
                case parse (lexer content) of 
                        Left expr -> putStrLn (file ++ " evaluates to: " ++ show (run expr))
                        Right err -> putStrLn (file ++ " error: " ++ err)
{-
parse [NSym "Bruh",LPar,VSym "x",RPar,LBra,VSym "x",AssignOp,VSym "x",BOp MulOp,CSym 2,Semi,Keyword ReturnK,VSym "x",Semi,RBra,NSym "Bruh",LSqu,CSym 5,RSqu,Semi]


"Lexical Error: Block ErrorPA (Const 5) in [PA (Const 5),Params [],
NSym \"Bruh\",LPar,RBra,Semi,PI (Return (Var \"x\")),Semi,
PA (Const 2),BOp MulOp,PI (Assign \"x\" (Var \"x\")),Block [],
RPar,Params [\"x\"],NSym \"Bruh\",LPar]"

--Inputs 5 ( Bruh } ; Return x ; 2 * =: x 



-}