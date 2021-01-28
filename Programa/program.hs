import Data.List
import System.IO

data Proposicion = Constante Bool
    | Variable String
    | Negacion Proposicion
    | Conjuncion Proposicion Proposicion
    | Disyuncion Proposicion Proposicion
    | Implicacion Proposicion Proposicion
    | Equivalencia Proposicion Proposicion

data EvaluacionTaut = Tautologia
                    | NoTautologia [(String, Bool)]

printProposition :: Proposicion -> String
printProposition prop = 
    case prop of
        Constante False -> "False"
        Constante True -> "True"
        Variable var -> var
        Negacion prop1 -> "Negacion (" ++ printProposition prop1 ++ ")"
        Conjuncion prop1 prop2 -> "Conjuncion (" ++ printProposition prop1 ++ ", " ++ printProposition prop2 ++ ")"
        Disyuncion prop1 prop2 -> "Disyuncion (" ++ printProposition prop1 ++ ", " ++ printProposition prop2 ++ ")"
        Implicacion prop1 prop2 -> "Implicacion (" ++ printProposition prop1 ++ ", " ++ printProposition prop2 ++ ")"
        Equivalencia prop1 prop2 -> "Equivalencia (" ++ printProposition prop1 ++ ", " ++ printProposition prop2 ++ ")"

impr_as_vals :: [(String, Bool)] -> String
impr_as_vals [] = ""
impr_as_vals ((v,b):vbs) = "(" ++ v ++ "," ++ (if b then "true" else "false") ++ ")" ++ impr_as_vals  vbs

impr_vals :: [[(String, Bool)]] -> String
impr_vals [] = ""
impr_vals (x:xs) = "[" ++  (impr_as_vals x) ++ "] " ++ (impr_vals xs)


impr_vars :: [String] -> String
impr_vars [] = ""
impr_vars (x:xs) = x ++ impr_vars xs

esVariable :: Proposicion -> Bool
esVariable (Variable _) = True
esVariable _ = False

getPrecedencia :: Proposicion -> Int
getPrecedencia (Conjuncion prop1 prop2) = 7
getPrecedencia (Disyuncion prop1 prop2) = 6
getPrecedencia (Implicacion prop1 prop2) = 5
getPrecedencia (Equivalencia prop1 prop2) = 4
getPrecedencia _ = 0

vars :: Proposicion -> [String]
vars prop = 
  let 
    las_vars :: Proposicion -> [String]
    las_vars prop = 
        case prop of 
            Constante _ -> []
            Variable var -> [var]
            Negacion prop1 -> las_vars prop1
            Conjuncion prop1 prop2 -> let vars1 = las_vars prop1
                                          vars2 = las_vars prop2
                                          in vars1 ++ vars2
            Disyuncion prop1 prop2 -> let vars1 = las_vars prop1;
                                             vars2 = las_vars prop2
                                             in vars1 ++ vars2
            Implicacion prop1 prop2 -> let vars1 = las_vars prop1;
                                              vars2 = las_vars prop2
                                              in vars1 ++ vars2
            Equivalencia prop1 prop2 -> let vars1 = las_vars prop1;
                                               vars2 = las_vars prop2
                                               in vars1 ++ vars2
  in 
    nub (las_vars prop)

gen_bools :: Int -> [[Bool]]
gen_bools 0 = [[]]
gen_bools n = (map (True :) anterior) ++ (map (False :) anterior)
              where anterior = gen_bools (n - 1)

as_vals :: [String] -> [Bool] -> [(String,Bool)]
as_vals [] [] = []
as_vals (x:xs) (y:ys) = (x,y) : as_vals xs ys
as_vals _ _ = error "Listas de longitudes distintas"


busca :: String -> [(String, Bool)] -> Bool
busca ident ((var, value):lista) =
    if ident == var 
    then value
    else busca ident lista
busca ident [] = error "No se encuentra en la lista de variables"

evalProp :: Proposicion -> [(String, Bool)] -> Bool
evalProp prop asignacion =
    case prop of
        Constante valor -> valor
        Variable var -> busca var asignacion
        Negacion prop -> not (evalProp prop asignacion)
        Conjuncion prop1 prop2 -> let vars1 = evalProp prop1 asignacion
                                      vars2 = evalProp prop2 asignacion 
                                      in vars1 && vars2
        Disyuncion prop1 prop2 -> let vars1 = evalProp prop1 asignacion
                                      vars2 = evalProp prop2 asignacion 
                                      in vars1 || vars2
        Implicacion prop1 prop2 -> let vars1 = evalProp prop1 asignacion
                                       vars2 = evalProp prop2 asignacion 
                                       in 
                                           case (vars1, vars2) of
                                               (True, False) -> False
                                               (False, True) -> False
                                               _          -> True
        Equivalencia prop1 prop2 -> let vars1 = evalProp prop1 asignacion
                                        vars2 = evalProp prop2 asignacion 
                                        in vars1 == vars2

taut :: Proposicion -> String
taut prop = 
    let 
        variables = vars prop
        n = length variables
        bools = gen_bools n

        isTaut :: [[Bool]] -> EvaluacionTaut
        isTaut [] = Tautologia
        isTaut (fila:mas_filas) =
            let 
                asignacion = as_vals variables fila
                evaluacion = evalProp prop asignacion
            in 
                case evaluacion of
                    True -> isTaut mas_filas
                    False -> NoTautologia asignacion
    in 
        case isTaut bools of
            Tautologia -> bonita prop ++ ": es una tautologia"
            NoTautologia asignacion -> bonita prop ++ ": no es tautologia porque : " ++ impr_as_vals asignacion ++ " la falsifica"

fndNegacion :: Proposicion -> Proposicion
fndNegacion prop =  
    case prop of 
        Constante True -> 
            Constante False
        Constante False -> 
            Constante True
        Variable var -> 
            Negacion (Variable var)
        Negacion prop1 ->
            prop1
        Conjuncion prop1 prop2 -> 
            Conjuncion (fndNegacion prop1) (fndNegacion prop2)
        Disyuncion prop1 prop2 -> 
            Disyuncion (fndNegacion prop1) (fndNegacion prop2)
        Implicacion prop1 prop2 -> 
            Disyuncion (fndNegacion (Negacion prop1)) (fndNegacion prop2)
        Equivalencia prop1 prop2 -> 
            Disyuncion (Conjuncion (fndNegacion prop1) (fndNegacion prop2)) 
                       (Conjuncion (fndNegacion (Negacion prop1)) (fndNegacion (Negacion prop2)))


fnd :: Proposicion -> Proposicion
fnd prop =  
    case prop of 
        Constante bool -> 
            Constante bool
        Variable var -> 
            Variable var
        Negacion prop1 ->
            if esVariable prop1
            then Negacion prop1
            else fndNegacion prop1
        Conjuncion prop1 prop2 -> 
            Conjuncion (fnd prop1) (fnd prop2)
        Disyuncion prop1 prop2 -> 
            Disyuncion (fnd prop1) (fnd prop2)
        Implicacion prop1 prop2 -> 
            Disyuncion (fnd (Negacion prop1)) (fnd prop2)
        Equivalencia prop1 prop2 -> 
            Disyuncion (Conjuncion (fnd prop1) (fnd prop2)) 
                       (Conjuncion (fnd (Negacion prop1)) (fnd (Negacion prop2)))

bonita :: Proposicion -> String
bonita prop = 
    case prop of 
        Constante True -> "True"
        Constante False -> "False"
        Variable var -> var
        Negacion prop ->
            let str = bonita prop
            in 
                case prop of 
                    Constante True -> "False"
                    Constante False -> "True"
                    Variable var -> "~" ++ str
                    _ -> "~(" ++ str ++ ")"
        Conjuncion prop1 prop2 -> 
            bonitaString prop prop1 prop2 "/\\"
        Disyuncion prop1 prop2 -> 
            bonitaString prop prop1 prop2 "\\/"
        Implicacion prop1 prop2 -> 
            bonitaString prop prop1 prop2 "=>"
        Equivalencia prop1 prop2 -> 
            bonitaString prop prop1 prop2 "<=>"

bonitaString :: Proposicion -> Proposicion -> Proposicion -> String -> String
bonitaString prop prop1 prop2 operador =
    let 
        precedencia1 = getPrecedencia prop1
        precedencia2 = getPrecedencia prop2

        str1 = 
            if precedencia1 > getPrecedencia prop 
            then "(" ++ bonita prop1 ++ ")"
            else bonita prop1
        str2 = 
            if precedencia2 > getPrecedencia prop
            then "(" ++ bonita prop2 ++ ")"
            else bonita prop2
    in 
        str1 ++ operador ++ str2
            

test :: String -> IO()
test "vars" = 
    let 
        prop = (Disyuncion (Negacion(Variable "a")) (Variable "b"))
    in print (vars prop)
test "genBools" = 
    let 
        prop = (Disyuncion (Negacion(Variable "a")) (Variable "b"))
        variables = vars prop
        n = length variables
        bools = gen_bools n
    in print (bools)
test "taut" = 
    let 
        prop = (Disyuncion (Negacion(Variable "a")) (Variable "a"))
    in print (taut prop)
test "bonita" = 
    let 
        prop = (Disyuncion (Negacion(Variable "a")) (Conjuncion (Variable "a") (Variable "b")))
    in print (bonita prop)
test "fnd" = 
    let 
        prop = (Implicacion (Negacion(Variable "a")) (Conjuncion (Variable "a") (Variable "b")))
    in print (bonita (fnd prop))
test "asVals" = 
    let 
        prop = (Implicacion (Negacion(Variable "a")) (Conjuncion (Variable "a") (Variable "b")))
        variables = vars prop
        n = length variables
        bools = gen_bools n

        asigVals :: [[Bool]] -> [[(String,Bool)]]
        asigVals [] = []
        asigVals (fila:mas_filas) = as_vals variables fila : asigVals mas_filas
    in 
        print (impr_vals (asigVals bools))

main :: IO()
main = do 
    test "asVals"

