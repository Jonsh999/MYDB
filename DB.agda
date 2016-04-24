module DB where

open import Data.Bool hiding (_≟_)
open import Data.BoundedVec hiding (fromList ; _∷_ ; [])
open import Data.Char hiding (_==_ ; _≟_)
open import Data.Empty
open import Data.List hiding (_++_)
open import Data.Maybe hiding (All; Any)
open import Data.Nat
open import Data.Product
open import Data.String hiding (toList ; _≟_)
open import Data.Unit hiding (_≤?_ ; _≟_ ; _≤_ )
open import Function using (_∘_)
open import Relation.Binary.Core using (_≡_)
open import Data.List.All hiding (lookup)
open import Data.List.Any
open import Relation.Nullary
open import Data.BoundedVec hiding (toList ; fromList) renaming ([] to ⟨⟩ ; _∷_ to _::_)

import Data.Nat.Show as NS

data AtrType : Set where
  CHAR : AtrType
  NAT  : AtrType
  BOOL : AtrType
  STR  : ℕ → AtrType

typeName : AtrType → String
typeName CHAR     = "CHAR"
typeName NAT      = "INTEGER"
typeName BOOL     = "Boolean"
typeName (STR x)  = "CHAR(" ++ NS.show x ++ ")"

el : AtrType → Set
el CHAR     = Char
el NAT      = ℕ
el BOOL     = Bool
el (STR x)  = BoundedVec Char x

So : Bool → Set
So true  = ⊤
So false = ⊥

Lo : { t : Set } → Dec t → Set
Lo ( yes _ ) = ⊤
Lo ( no _ ) = ⊥

KK : { t : Set } → Dec t → Bool → Set
KK ( yes _ ) true = ⊤
KK ( yes _ ) false = ⊥
KK ( no _ ) _ = ⊥

Attribute : Set
Attribute = Σ String (λ _ → AtrType)

Schema : Set
Schema = List Attribute

Elem : Set
Elem = Σ String (λ _ → AtrType)


fl : Schema → List Elem → Set
fl [] _ = ⊤
fl _ [] = ⊤
fl ( ( a , b ) ∷ s ) ( ( c , d ) ∷ le )
              = Σ ( KK ( length s ≟ length le ) ( typeName b == typeName d ) )  ( λ z → fl s le )

data Row : Schema → List Elem → Set where
  EmptyRow : Row [] []
  CRow     : ( s : Schema ) → ( le : List Elem ) → ( fff : fl s le  ) → Row s le

data Constraint : ( s : Schema ) → Set where
  EmptyConstraint : Constraint []
  NonConstraint : ∀ { s : Schema } → Constraint s
  Unique : ∀ { s : Schema }  → ( n : ℕ ) → n ≤ ( length s )  → Constraint s

lop : { t : Set } → Dec t → Bool → Set
lop ( yes _ ) false = ⊤
lop ( yes _ ) true = ⊥
lop ( no _ ) _ = ⊤

eqn : ( a : List Elem ) → ( b : List Elem ) → ( n : ℕ ) → ( step : ℕ ) → Set -- беск цикл
eqn [] _ _ _ = ⊤
eqn _ [] _ _ = ⊤
eqn ( ( a , b ) ∷ la ) ( ( c , d ) ∷ lb ) n  step = Σ (  lop ( n ≟ step ) (a == c) ) ( λ z → eqn la lb n ( step + 1 ) )

UniqElem : { le : List Elem } → { le2 : List Elem } → (s : Schema ) → ( l : List ( Row s le ) ) → ( r : Row s le2 ) → ( n : ℕ ) → Set
UniqElem _ [] _ _ = ⊤
UniqElem [] _ _ _ = ⊤
UniqElem {le} {le2} s ( nr ∷ l ) r n = Σ ( eqn le le2 n zero ) ( λ z → UniqElem s l r n)

f : { le : List Elem} → ( s : Schema ) → ( c : Constraint s ) → ( lr : List ( Row s le ) ) → Set
f [] EmptyConstraint _ = ⊤
f _ ( NonConstraint ) _ = ⊤
f s ( Unique  nn _ ) [] = ⊤
f s ( Unique  nn yy ) ( r ∷ lr )  =  Σ ( UniqElem s lr r nn )  (λ z → f s ( Unique nn yy ) lr )

data Table : { le : List Elem } → ( s : Schema ) → ( c : Constraint s ) → ( lr : List ( Row s le ) ) → Set where
  EmptyTable : Table {[]} [] EmptyConstraint []
  CTable : { le : List Elem } → ∀ s  → ∀  (c : Constraint s ) → ∀ ( lr : List ( Row s le ) ) → ( f s c lr ) → Table s c lr

Insert : { s : Schema } → { c : Constraint s } → { le : List Elem } → { le2 : List Elem } → { lr : List ( Row s le ) } → ( t : Table s c lr ) → ( r : Row s le ) → ( ff : f s c ( r ∷ lr ) ) → Table s c ( r ∷ lr )
Insert {s} {c} {le} {le2} {lr} t r ff = CTable s c ( r ∷ lr ) ff





DissertationCounsil : Schema
DissertationCounsil =  ("id", NAT)
                    ∷  ("number", STR 255)
                    ∷  ("name", STR 255)
                    ∷  ("phone", STR 100)
                    ∷  ("place", STR 1000)
                    ∷  ("approved", BOOL) ∷ []

ConstraintNumber : Constraint DissertationCounsil
ConstraintNumber = Unique 2 _

ListEl1 : List Elem
ListEl1 = ("1" , NAT )
       ∷ ("Д 446.004.05" , STR 255 )
       ∷ ("РГТЭУ" , STR 255 )
       ∷ ("" , STR 100 )
       ∷ ("" , STR 1000 )
       ∷ ("" , BOOL ) ∷ []

ListEl2 : List Elem
ListEl2 = ("2" , NAT )
        ∷ ("Д 501.001.94" , STR 255 )
        ∷ ("" , STR 255 )
        ∷ ("495-629-75-21" , STR 100 )
        ∷ ("125009, г. Москва, Моховая ул., д. 11, НИИ и Музей антропологии МГУ, ауд. 215" , STR 1000 )
        ∷ ("true" , BOOL ) ∷ []

ListEl3 : List Elem
ListEl3 = ("3" , NAT )
        ∷ ("К 053.05.21" , STR 255 )
        ∷ ("Отделение Радиофизики физического факультета МГУ" , STR 255 )
        ∷ ("" , STR 100 )
        ∷ ("" , STR 1000 )
        ∷ ("" , BOOL ) ∷ []

ListEl4 : List Elem
ListEl4 = ("4" , NAT )
        ∷ ("Д 501.001.52" , STR 255 )
        ∷ ("МГУ им. М.В. Ломоносова" , STR 255 )
        ∷ ("" , STR 100 )
        ∷ ("" , STR 1000 )
        ∷ ("true" , BOOL ) ∷ []

ListEl5 : List Elem
ListEl5 = ("5" , NAT )
        ∷ ("Д 501 002 13 при МГУ имени М.В. Ломоносова" , STR 255 )
        ∷ ("МГУ имени М.В. Ломоносова, факультет Почвоведения" , STR 255 )
        ∷ ("" , STR 100 )
        ∷ ("" , STR 1000 )
        ∷ ("false" , BOOL ) ∷ []

Row1 : Row DissertationCounsil ListEl1
Row1 = Crow DissertationCounsil ListEl1 _

Row2 : Row DissertationCounsil ListEl2
Row2 = Crow DissertationCounsil ListEl2 _

Row3 : Row DissertationCounsil ListEl3
Row3 = Crow DissertationCounsil ListEl3 _

Row4 : Row DissertationCounsil ListEl4
Row4 = Crow DissertationCounsil ListEl4 _

Row5 : Row DissertationCounsil ListEl5
Row5 = Crow DissertationCounsil ListEl5 _

RightLR = Row1 ∷ Row2 ∷ Row3 ∷ Row4 ∷ Row5 ∷ []

NRightLR = Row1 ∷ Row2 ∷ Row3 ∷ Row4 ∷ Row5 ∷ Row3 ∷ []

Table1 : Table DissertationCounsil (ConstrintNumber _) RightLR
Table1 = CTable DissertationCounsil (ConstrintNumber _) RightLR _


Table1 : Table DissertationCounsil (ConstrintNumber _) NRightLR
Table1 = CTable DissertationCounsil (ConstrintNumber _) NRightLR _



RightLR = Row1 ∷ Row2 ∷ Row3 ∷ Row4 ∷ []

Table1 : Table DissertationCounsil (ConstrintNumber _) RightLR
Table1 = CTable DissertationCounsil (ConstrintNumber _) RightLR _

Table2 = Insert Table1 Row5 _

Table3 = Insert Table2 Row3 _



















_≠0 : ℕ → Set
0 ≠0 = ⊥
_ ≠0 = ⊤


nzplus : ( n : ℕ ) → {nz : n ≠0} → ℕ → ℕ
nzplus zero {()} m
nzplus (suc n) m = n + m
-- testnzplus = nzplus 1 3
testnzplus = nzplus 0 3

-- DC2 : Schema
-- DC2 = ("id", NAT) ∷ ("number", STR 255) ∷ []

-- LE : List Elem
-- LE = ( "12" , NAT) ∷ ("dwqd" , STR 255) ∷ []

-- TestTable : Table DC EmptyConstraint []
-- TestTable = CTable DC EmptyConstraint [] ( f DC EmptyConstraint [] )

-- s : Schema
-- s = []

-- le : List Elem
-- le = []

-- ff : Set
-- ff = fl DC2 LE

-- FR : Row DC2 LE
-- FR = CRow DC2 LE ( ff )



-- nel : {s : Schema} → ( n : ℕ ) → ( step : ℕ ) → ( ls : List (String)  ) → ( n == step ) → Set
-- nel _ _ [] _ = ⊥
-- nel _ _ (a ∷ ls) _ = a
-- nel n step (a ∷ ls) _ = nel n ( step + 1 ) ls _

-- streq : {s : Schema} → ( n : ℕ ) → ( r : Row s ) → ( str : String ) → ( lr : List (Row s) ) → Set
-- streq n r str lr =

-- checker : {s : Schema} → ( n : ℕ ) → ( nn : ℕ ) → (lr :  List ( Row s )) → ( str : String ) → ( n ≟ nn ) → Set
-- checker _ _ _ _ no _ = ⊥
-- checker n nn lr str _ = streq

-- Get : { s : Schema } → {c : Constrain s } → { lr : List (Row s) } → (t : Table s c lr ) → ( n : ℕ ) → ( str : String ) → ( f s c lr ) → Set
-- Get {s} { EmpetyConstraint _} { lr } _ _ _ _ = ⊥
-- Get {s} { Unique nn _ } {lr} t n str = checker n nn lr str _
