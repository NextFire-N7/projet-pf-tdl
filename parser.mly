/* Imports. */

%{

open Type
open Ast.AstSyntax
%}


%token <int> ENTIER
%token <string> ID
%token RETURN
%token PV
%token AO
%token AF
%token PF
%token PO
%token EQUAL
%token CONST
%token PRINT
%token IF
%token ELSE
%token WHILE
%token BOOL
%token INT
%token RAT
%token CALL 
%token CO
%token CF
%token SLASH
%token NUM
%token DENOM
%token TRUE
%token FALSE
%token PLUS
%token MULT
%token INF
%token EOF
// Pointeurs
%token AND
%token NEW
%token NULL
// Types nommés
%token <string> TID
%token TYPEDEF
// struct
%token STRUCT
%token DOT

(* Type de l'attribut synthétisé des non-terminaux *)
%type <programme> prog
%type <instruction list> bloc
%type <fonction> fonc
%type <instruction list> is
%type <instruction> i
%type <typ> typ
%type <(typ*string) list> dp
%type <expression> e 
%type <expression list> cp
%type <affectable> a
%type <typedef list> td

(* Type et définition de l'axiome *)
%start <Ast.AstSyntax.programme> main

%%

main : lfi = prog EOF     {lfi}

prog :
// update: types nommés
| ltd = td  lf = fonc  lfi = prog   {let (Programme (ltd1,lf1,li))=lfi in (Programme (ltd@ltd1,lf::lf1,li))}
| ID li = bloc            {Programme ([],[],li)}

fonc : t=typ n=ID PO p=dp PF AO li=is AF {Fonction(t,n,p,li)}

bloc : AO li = is AF      {li}

is :
|                         {[]}
| i1=i li=is              {i1::li}

i :
| t=typ n=ID EQUAL e1=e PV          {Declaration (t,n,e1)}
| a=a EQUAL e=e PV                  {Affectation (a, e)}
| CONST n=ID EQUAL e=ENTIER PV      {Constante (n,e)}
| PRINT e1=e PV                     {Affichage (e1)}
| IF exp=e li1=bloc ELSE li2=bloc   {Conditionnelle (exp,li1,li2)}
| WHILE exp=e li=bloc               {TantQue (exp,li)}
| RETURN exp=e PV                   {Retour (exp)}
(* Addition-affectation *)
| a=a PLUS EQUAL e=e PV             {AddAff(a, e)}
// types nommés
| TYPEDEF n=TID EQUAL t=typ PV      {TypedefLocal (n,t)}

dp :
|                         {[]}
| t=typ n=ID lp=dp        {(t,n)::lp}

typ :
| BOOL                  {Bool}
| INT                   {Int}
| RAT                   {Rat}
| t=typ MULT            {Pointeur (t)}
| tid=TID               {NamedTyp (tid)}
//struct
| STRUCT AO dp=dp AF    {Struct (dp)}

e : 
| CALL n=ID PO lp=cp PF   {AppelFonction (n,lp)}
| CO e1=e SLASH e2=e CF   {Binaire(Fraction,e1,e2)}
| n=a                     {Affectable n}
| TRUE                    {Booleen true}
| FALSE                   {Booleen false}
| e=ENTIER                {Entier e}
| NUM e1=e                {Unaire(Numerateur,e1)}
| DENOM e1=e              {Unaire(Denominateur,e1)}
| PO e1=e PLUS e2=e PF    {Binaire (Plus,e1,e2)}
| PO e1=e MULT e2=e PF    {Binaire (Mult,e1,e2)}
| PO e1=e EQUAL e2=e PF   {Binaire (Equ,e1,e2)}
| PO e1=e INF e2=e PF     {Binaire (Inf,e1,e2)}
| PO exp=e PF             {exp}
| AND n=ID                {Adresse (n)}
| PO NEW t=typ PF         {New (t)}
| NULL                    {Null}
| AO lp=cp AF             {StructExpr(lp)}

cp :
|               {[]}
| e1=e le=cp    {e1::le}

(* POINTEURS *)
a :
| n=ID                  {Ident (n)}
| PO MULT a=a PF        {Deref (a)}
// structure
| PO a=a DOT p=ID PF    {Attribut(a, p)}

// Types nommés
td :
|                                       {[]}
| TYPEDEF n=TID EQUAL t=typ PV ltd=td   {(TypedefGlobal (n,t))::ltd}
