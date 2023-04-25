load "Listsort";
load "Int";
load "Bool";

(*Tipi "primitivi" per le regole di tipaggio*)
datatype type_L =  int  
  | unit  
  | bool
  | func of type_L * type_L;

(*Operazioni che poi vado ad utilizzare nella small-step dell'Op*)
datatype oper = piu 
  | mu
  | uguale (*Devo implementare l'uguaglianza per il calcolo di Fibonacci*)

datatype type_loc = intref

type loc = string

type store = (loc * int) list

type typeE = (loc * type_loc) list 

(*definizione del "tipo primitivo" per la var*)
type var_T = string


(*Sintassi*)
datatype exp =
        Boolean of bool
    |   Integer of int
    |   Op of exp * oper * exp
    |   If of exp * exp * exp
    |   Assign of loc * exp
    |   Skip 
    |   Seq of exp * exp (*e1;e2*)
    |   While of exp * exp
    |   Deref of loc 
    (*Sintassi aggiunta per l'elaborato*)
    |   Var of var_T (*Nuovo tipo per la var in quanto non può essere nè int nè un altro tipo primitivo*)
    |   Fn of string * type_L * exp
    |   AppCBN of exp * exp
    |   FixCBN of exp
    (*#########################*)
    |   Fibonacci of exp

(*FUNZIONI DI SUPPORTO*)
(*Funzione di supporto che mi serve nella small-step se il parametro è effettivamente uno dei valori "primitivi"*)
fun valore (Integer n) = true
  | valore (Boolean b) = true
  | valore (Skip) = true
  | valore (Fn ( variable, t, e)) = true
  | valore _ = false

(*e1 -> e2*)

(*(exp * store) -> (exp * store) option*)
(*(''a * b) list *''a ->ib option*)
(*Immaginiamo che lo store sia una lista di coppie loc * int
Abbiamo bisogno di una funzione di supporto per consultare lo sotre*)
fun lookup ( [], l ) = NONE
  | lookup ( (l',n')::pairs, l) = 
    if l=l' then SOME n' else lookup (pairs,l)


(* fn:store * (loc*int)->store option *)

(* fn: (''a * 'b) list -> (''a * 'b) list -> ''a * 'b -> (''a * 'b) list option *)
(*Update nata come funzione di supporto per l'Assign che prende lo store e ci "mette" il valore
dell'int che gli andiamo a passare restituendo lo store modificato tramite l'uso di un'altra funzione di supporto
[infatti update chiama update']*)
fun update'  front [] (l,n) = NONE
 |  update'  front ((l',n')::pairs) (l,n) = 
    if l=l' then 
        SOME(front @ ((l,n)::pairs) )
    else 
        update' ((l',n')::front) pairs (l,n)

fun update (s, (l,n)) = update' [] s (l,n)

(*FUNZIONE PER LA SOSTITUZIONE -> va' a sostituire le occorrenze delle variabili passate in ingresso e l'espressione
con il terzo tipo di espressione passato in ingresso supponendo che le variabili passate siano fresh per evitare il problema dell'alpha conversion
(supposizione fatta dato che la gestione dell'alpha conversion non è da specifica)*)
fun sostituzione expr var (Integer n)           = Integer n
  | sostituzione expr var (Boolean b)           = Boolean b 
  (*fine dei casi base*)
  | sostituzione expr var (Op (e1, oper, e2))   = Op (sostituzione expr var e1, oper , sostituzione expr var e2)
  | sostituzione expr var (If (e1, e2, e3))     = If (sostituzione expr var e1, sostituzione expr var e2, sostituzione expr var e3)
  | sostituzione expr var (Assign (loc, e))     = Assign(loc, sostituzione expr var e)
  | sostituzione expr var (Deref loc)           = Deref loc
  | sostituzione expr var (Skip)                = Skip
  | sostituzione expr var (Seq (e1, e2))        = Seq (sostituzione expr var e1, sostituzione expr var e2)
  | sostituzione expr var (While (e1, e2))      = While (sostituzione expr var e1, sostituzione expr var e2)
  (*Espressioni "nuove" per l'elaborato*)
  | sostituzione expr var (Var(x))              = if var = x then expr else (Var(x))
  | sostituzione expr var (Fn (variable, t, e)) = Fn(variable, t, sostituzione expr variable e)
  | sostituzione expr var (AppCBN(e1, e2))      = AppCBN(sostituzione expr var e1, sostituzione expr var e2)
  | sostituzione expr var (FixCBN(e))           = FixCBN(sostituzione expr var e)
  | sostituzione expr var (Fibonacci(n))        = Fibonacci(n)

(*INIZIO SEMANTICA SMALL STEP -> funzione che "estrae" i valori una volta utilizzati*)
fun red (Integer n,s) = NONE
    | red (Boolean b,s) = NONE
    | red (Op (e1,oper,e2),s) = 
        (case (e1,oper,e2) of
            (Integer x1, piu, Integer x2) => SOME(Integer (x1+x2), s)   (*op+*)
        | (Integer x1, mu, Integer x2) => SOME(Boolean (x1 >= x2), s)(*op>=*)
        | (Integer x1, uguale, Integer x2) => SOME(Boolean (x1 = x2), s) (*op ==*)
        | (e1,oper,e2) => (                                               
            if (valore e1) then (                                        
                case red (e2,s) of 
                    SOME (e2',s') => SOME (Op(e1,oper,e2'),s')     (*op2*)
                | NONE => NONE )                           
            else (                                                 
                case red (e1,s) of 
                    SOME (e1',s') => SOME(Op(e1',oper,e2),s')      (*op1*)
                | NONE => NONE ) ) )
    | red (If (e1,e2,e3),s) =
        (case e1 of
            Boolean(true) => SOME(e2,s)                           
        | Boolean(false) => SOME(e3,s)                          
        | _ => (case red (e1,s) of
                    SOME(e1',s') => SOME(If(e1',e2,e3),s')      (*if*)
                    | NONE => NONE ))
    | red (Deref l,s) = 
        (case lookup  (s,l) of                
            SOME n => SOME(Integer n,s)                          
            | NONE => NONE )                  
    | red (Assign (l,e),s) =                                  
        (case e of                                                 
            Integer n => (case update (s,(l,n)) of 
                            SOME s' => SOME(Skip, s')           
                            | NONE => NONE)                                   
        | _ => (case red (e,s) of                           
                    SOME (e',s') => SOME(Assign (l,e'), s')    
                    | NONE => NONE  ) )                          
    | red (While (e1,e2),s) = SOME( If(e1,Seq(e2,While(e1,e2)),Skip),s) (* (while) *)
    | red (Skip,s) = NONE                                     
    | red (Seq (e1,e2),s) =                                   
        (case e1 of                                                 
            Skip => SOME(e2,s)                                     
        | _ => ( case red (e1,s) of                           
                    SOME (e1',s') => SOME(Seq (e1',e2), s')       
                | NONE => NONE ) )  
    (*Adding custom function for the assignement*)
    | red (Var (n),s) = NONE
    | red (Fn (variable, tipo, e), s) = NONE (*Versione CBN*)
    | red (AppCBN(e1, e2), s) =
      (case e1 of
        Fn(x, t, e) => (SOME (sostituzione e2 x e, s))  (*caso in cui e1 sia una funzione andare a chiamare sostituire con e2 passato come espressione*)
        | _ => (case red (e1, s) of (*in tutti gli altri a casi si va' a ridurre e1 e si ottengono 2 casi*)
                SOME (e1', s') => SOME(AppCBN (e1', e2), s') (*applicazione di fuznioni in versione CBN*)
                | _ => NONE))
    | red (FixCBN(e), s) = SOME(AppCBN(e, FixCBN(e)), s)(*regole small step = no premesse; fix.e -> e(fix.e)*)
    (*##################IL PROBLEMA E' QUI DA QUALCHE PARTE##########################*)
    (*FIBONACCI => prende in input un intero n e restituisce l'n-esimo elemento della successione
    -> implemento i casi base e poi utilizzo il ciclo while per calcolare l'elemento della successione
    ho bisogno di 3 variabili per restituire il valore (li chiamo x, y, z dove x = Fib(n - 1) + Fib(n - 2), y = Fib(n - 1) e z = Fib(n - 2))*)
    | red (Fibonacci(n), s)
      = SOME(AppCBN(Fn("n", int, If(
              Op(Var("n"), uguale, Integer 0), Deref("z"), (*Se n = 0 return 1*)
              If(Op(Var("n"), uguale, Integer 1), Deref("y"),  (*Se n = 1 return 1*)
                Seq(While(Op(Op(Var("n"), piu, Integer (~1)), mu, Deref("i")) (*Finchè (n-1) >= counter [rappresentato da i]*)
                  , Seq( Seq( Seq( 
                          Assign("x", Op(Deref("y"), piu, Deref("z"))) (*x = Fib(n-1) + Fib(n-2)*)
                          , Assign("z", Deref("y")) (*Incremento Fib(n-2)*)
                        ), Assign("y", Deref("x")) (*Incremento Fib(n-1)*)
                      ), Assign("i", Op(Deref("i"), piu, Integer 1)) (*Incremento il contatore del While*)
                    )
                  )(*Fine del while*), Deref("x")
                )(*Fine prima Seq*)
              )(*Fine secondo If*)
            )(*Fine primo If*)
          )(*Fine Fn*)
        , n)(*Fine AppCBN*)
      , s)(*Fine del SOME*)
    

(*Fine semantica small step*)

(*Funzione big step: uguale alla smal step ma con più passi di computazione alla volta*)
fun evaluate (e,s) = case red (e,s) of 
                         NONE => (e,s)
                       | SOME (e',s') => evaluate (e',s')


(*   e,s -> e2,s2 ---..... *)
(*Tipaggio*)
fun infertype gamma (Integer n) = SOME int
  | infertype gamma (Boolean b) = SOME bool
  | infertype gamma (Op (e1,oper,e2)) 
    = (case (infertype gamma e1, oper, infertype gamma e2) of
          (SOME int, piu, SOME int) => SOME int
        | (SOME int, mu, SOME int) => SOME bool
        | (SOME int, uguale, SOME int) => SOME bool         (*aggiunta dell'operazione == per l'implementazione di Fibonacci*)
        | _ => NONE)
  | infertype gamma (If (e1,e2,e3)) 
    = (case (infertype gamma e1, infertype gamma e2, infertype gamma e3) of
           (SOME bool, SOME t2, SOME t3) => 
           (if t2=t3 then SOME t2 else NONE)
         | _ => NONE)
  | infertype gamma (Deref l) 
    = (case lookup (#1 gamma,l) of
           SOME intref => SOME int
         | NONE => NONE)
  | infertype gamma (Assign (l,e)) 
    = (case (lookup (#1 gamma,l), infertype gamma e) of
           (SOME intref,SOME int) => SOME unit
         | _ => NONE)
  | infertype gamma (Skip) = SOME unit
  | infertype gamma (Seq (e1,e2))  
    = (case (infertype gamma e1, infertype gamma e2) of
           (SOME unit, SOME t2) => SOME t2
         | _ => NONE )
  | infertype gamma (While (e1,e2)) 
    = (case (infertype gamma e1, infertype gamma e2) of
           (SOME bool, SOME unit) => SOME unit 
         | _ => NONE )
  (*Funzioni implementate per l'elaborato*)
  | infertype gamma (Var (n)) =  
    (case (lookup (#2 gamma, n)) of
      (SOME t) => SOME t (*restituisce il tipo della variabile preso in considerazione*)
      | NONE => NONE)
  | infertype gamma (Fn (variabile, t, e)) 
    = (case (infertype (#1 gamma, (variabile, t)::(#2 gamma)) e) of
      (SOME t1) => SOME(func (t, t1)) (*regola di tipaggio secondo la quale T -> T'*)
      | _ => NONE)
  | infertype gamma (AppCBN(e1, e2)) (* e1 : T -> T'    e2 : T [premesse] = e1e2 : T'*)
    = (case (infertype gamma e1, infertype gamma e2) of (*controllo il tipo di e1 e di e2*)
        (SOME (func (t1, t2)), SOME tipo_e2) => (*se e1 risulta tipo func*)
          (if t1 = tipo_e2 then SOME t2 else NONE) (*se t1 e e2 hanno lo stesso tipo allora restituisci il tipo di t2, altrimenti tipo non valido*)
        | _ => NONE) (*in tutti gli altri casi il tipo non è valido*)
  | infertype gamma (FixCBN(e)) (*[premessa] e : (T1 -> T2) -> (T1 -> T2) => fix.e : T1 -> T2*)
    = (case (infertype gamma e ) of
        SOME (func((func (t1, t2)), (func(t1', t2'))))
        => (if t1 = t1' andalso t2 = t2' then SOME(func(t1, t2)) else NONE) (*controllo che i tipi delle funzioni siano uguali*)
        | _ => NONE) 
  (*TIPAGGIO FIBONACCI -> molto facile in quanto si occupa solo di verificare che il tipo in entrata e in uscita siano int*)
  | infertype gamma (Fibonacci(n))
    = (case (infertype gamma (n)) of
        (SOME int) => (SOME int)
        | _ => NONE)
  

(*Funzioni di stampa*)
fun printop piu = "+"
  | printop mu = ">="
  | printop uguale  = "=="
                         
fun printexp (Integer n) = Int.toString n
  | printexp (Boolean b) = Bool.toString b
  | printexp (Op (e1,oper,e2)) 
    = "(" ^ (printexp e1) ^ (printop oper) 
      ^ (printexp e2) ^ ")"
  | printexp (If (e1,e2,e3)) 
    = "if " ^ (printexp e1 ) ^ " then " ^ (printexp e2)
      ^ " else " ^ (printexp e3)
  | printexp (Deref l) = "!" ^ l
  | printexp (Assign (l,e)) =  l ^ ":=" ^ (printexp e )
  | printexp (Skip) = "skip"
  | printexp (Seq (e1,e2)) =  (printexp e1 ) ^ ";" 
                                     ^ (printexp e2)
  | printexp (While (e1,e2)) =  "while " ^ (printexp e1 ) 
                                       ^ " do " ^ (printexp e2)
  (*################################################################################*)
  | printexp (Var n) = "Var(" ^(n) ^")"
  | printexp (Fn (variable, t, e)) = "Fn " ^(printexp e)
  | printexp (AppCBN(e1, e2)) = "App (" ^(printexp e1)^ ", " ^(printexp e2)^ ")"
  | printexp (FixCBN(e)) = "Fix (" ^(printexp e)^ ")"
  | printexp (Fibonacci(n)) = "Fibonacci(" ^(printexp n)^ ")"


(*Funzioni per stampare a video lo store*)
fun printstore' [] = ""
  | printstore' ((l,n)::pairs) = l ^ "=" ^ (Int.toString n) 
                                   ^ " " ^ (printstore' pairs)

fun printstore pairs = 
    let val pairs' = Listsort.sort 
                         (fn ((l,n),(l',n')) => String.compare (l,l'))
                         pairs
    in
        "{" ^ printstore' pairs' ^ "}" end

(*Funzione per stampare a video le configurazioni*)
fun printconf (e,s) = "< " ^ (printexp e) 
                             ^ " , " ^ (printstore s) ^ " >"

(*Funzione per stampare a video le riduzioni*)
fun printred' (e,s) = 
    case red (e,s) of 
        SOME (e',s') => 
        ( TextIO.print ("\n -->  " ^ printconf (e',s') ) ;
          printred' (e',s'))
      | NONE => (TextIO.print "\n -/->  " ; 
                 if valore e then 
                     TextIO.print "(a value)\n" 
                 else 
                     TextIO.print "(stuck - not a value)" )

fun printred (e,s) = (TextIO.print ("      "^(printconf (e,s))) ;
                          printred' (e,s))
                        

