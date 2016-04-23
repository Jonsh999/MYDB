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

import Data.Nat.Show as NS

-- Our mini universe of types
-- This is a representation of the types that our database bindings
-- suppports. These types are mapped into the corresponding SQL types
-- to perform queries and are converted into the appropriate Agda types
-- when query results are returned.
data AtrType : Set where
  CHAR : AtrType
  NAT  : AtrType
  BOOL : AtrType
  STR  : ℕ → AtrType

-- The name of a type as it corresponds to its given SQL name.
typeName : AtrType → String
typeName CHAR     = "CHAR"
typeName NAT      = "INTEGER"
typeName BOOL     = "Boolean"
typeName (STR x)  = "CHAR(" ++ NS.show x ++ ")"

-- Map the universe of SQL types to agda
-- equivalents.
-- Strings are a little odd in SQL in that they are
-- paramterized by a length, but the length serves only
-- as an upper bound on the number of characters present.
-- This behaviour is mimicked by the BoundedVec type, but we
-- should also add an unbounded string type for convenience as well.
el : AtrType → Set
el CHAR     = Char
el NAT      = ℕ
el BOOL     = Bool
el (STR x)  = BoundedVec Char x

So : Bool → Set
So true  = Unit
So false = ⊥

-- An attribute corresponds to a column in the database.
-- It is a column name along with the SQL type.



Attribute : Set
Attribute = Σ String (λ _ → AtrType)

Schema : Set
Schema = List Attribute


-- A row from the database is a list with knowlege of the
-- database schema.


data Row : Schema → Set where
  EmptyRow : Row []
  ConsRow  : ∀ {s name} → {u : AtrType} → el u → Row s → Row (( name , u ) ∷ s)

rowToList : {s : Schema} → Row s → List String
rowToList {[]} EmptyRow                         = []
rowToList {( n , CHAR ) ∷ s} (ConsRow x xs)     = ("'" ++ fromList [ x ] ++ "'") ∷ rowToList xs
rowToList {( n , NAT ) ∷ s} (ConsRow x xs)      = NS.show x ∷ rowToList xs
rowToList {( n , BOOL ) ∷ s} (ConsRow true xs)  = "1" ∷ rowToList xs
rowToList {( n , BOOL ) ∷ s} (ConsRow false xs) = "0" ∷ rowToList xs
rowToList {( n , STR x ) ∷ s} (ConsRow x₁ xs)   = ("\"" ++ fromList (toList x₁) ++ "\"") ∷ rowToList xs



  -- Unique : ∀{ s } → (a : Attribute) → All (λ y → a ≡ y ) s → Constraint s
  -- Unique : ∀{ s } → (a : Attribute) → ( t : Any (_≡_ a) s ) → Constraint s


-- gg : { a : ℕ } → { b : ℕ } → Dec ( a ≡ b ) → Bool
-- gg ( yes _ ) = true
-- gg ( no _ ) = false


-- constraint_el : Schema -> Row Schema -> List (Row Schema) -> Set


-- cmp : ( n : ℕ ) → ( t : ℕ ) → n ≤? t → Set
-- cmp _ _ yes _ = ⊤
-- cmp _ _ no _ = ⊥

data Constraint : ( s : Schema ) → Set where
  EmptyConstraint : Constraint []
  Unique : ∀ { s : Schema }  → ( n : ℕ ) → n ≤ ( length s )  → Constraint s

lop : { t : Set } → Dec t → Bool → Set
lop ( yes _ ) true = ⊤
lop ( yes _ ) false = ⊥
lop ( no _ ) _ = ⊤

eqn : ( a : List String ) → ( b : List String ) → ( n : ℕ ) → ( step : ℕ ) → Set -- беск цикл
eqn [] _ _ _ = ⊤
eqn _ [] _ _ = ⊤
eqn ( a ∷ la ) ( b ∷ lb ) n  step = Σ (  lop ( n ≟ step ) (a == b) ) ( λ z → eqn la lb n ( step + 1 ) )

UniqElem : (s : Schema ) → ( l : List ( Row s ) ) → ( r : Row s ) → ( n : ℕ ) → Set
UniqElem _ [] _ _ = ⊤
UniqElem [] _ _ _ = ⊤
UniqElem s ( nr ∷ l ) r n = Σ ( eqn ( rowToList nr ) ( rowToList r ) n zero ) ( λ z → UniqElem s l r n)

f : ( s : Schema ) → ( c : Constraint s ) → ( lr : List ( Row s) ) → Set
f [] EmptyConstraint _ = ⊤
f s ( Unique  nn _ ) [] = ⊤
f s ( Unique  nn yy ) ( r ∷ lr )  =  Σ ( UniqElem s lr r nn )  (λ z → f s ( Unique nn yy ) lr )


data Table : ( s : Schema ) → ( c : Constraint s ) → ( lr : List ( Row s ) ) → Set where
  EmptyTable : Table [] EmptyConstraint []
  CTable : ∀ s  → ∀  (c : Constraint s ) → ∀ ( lr : List ( Row s ) ) → ( f s c lr ) → Table s c lr

Insert : { s : Schema } → { c : Constraint s } → { lr : List ( Row s ) } → ( t : Table s c lr ) → ( r : Row s ) → ( ff : f s c ( r ∷ lr ) ) → Table s c ( r ∷ lr )
Insert {s} {c} {lr} t r ff = CTable s c ( r ∷ lr ) ff

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


-- f : ( s : Schema ) → ( c : Constraint ) → ( r : Row ) → ( t : Table ) → ( tr : Table )
--   ( Unique _ _ _) r [] EmptyTable → EmptyTable
--   ( _ ) r t → ∑ All ( λ y → rowToList s r ≡ y )


-- неравенство и атрибут вместо строки
  -- st (Row Schema) -> Set
  -- data Constraint : ( s : Schema) → ( x : Attribute ) → All (λ y → x ≡ y ) s → Set where
  --  Unique : ∀ s → ∀ x → ∀ a → Constraint s x a

-- data Table : ( s : Schema ) → ( c : Constraint s  ) → ( l : List (Row) ) → Set where
--   EmptyTable : Table []

-- insert : {a : Table} -> Row s -> {b : Table}
-- insert _ EmpetyRow  = a




-- dd : (s : Schema) → (r : Row s ) → length s ≡ length (rowToList r)
-- dd s r = _-c


-- Show a row
showRow : {s : Schema} → Row s → String
showRow = foldr _++_ "" ∘ intersperse "|" ∘ rowToList

-- Table : Schema → Set
-- Table = List ∘ Row

-- The length of a row from the database. This is, perhaps, not that useful.
∥_∥ : ∀ {s} → Row s → ℕ
∥ EmptyRow ∥    = zero
∥ ConsRow x y ∥ = suc ∥ y ∥
