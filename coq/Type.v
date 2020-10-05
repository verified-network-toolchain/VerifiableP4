Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.

Inductive OpUni : Type :=
  | Not
  | BitNot
  | UMinus.

Inductive OpBin : Type :=
  |  Plus
  | PlusSat
  | Minus
  | MinusSat
  | Mul
  | Div
  | Mod
  | Shl
  | Shr
  | Le
  | Ge
  | Lt
  | Gt
  | Eq
  | NotEq
  | BitAnd
  | BitXor
  | BitOr
  | PlusPlus
  | And
  | Or.

Inductive Name : Type :=
  | BareName : string -> Name
  | QualifiedName : list string -> string -> Name.

Inductive FunctionTypeKind : Type :=
  | Parser
  | Control
  | Extern
  | Table
  | Action
  | Function
  | Builtin.

Inductive Direction : Type :=
  | In
  | Out
  | InOut
  | Directionless.

Inductive Expression :=
  | ETrue
  | EFalse
  | EInt : Z -> Expression
  | EString : string -> Expression
  | EName : Name -> Expression
  | EArrayAccess: Expression -> Expression -> Expression
  | EBitStringAccess: Expression -> Z -> Z -> Expression
  | EList: list Expression -> Expression
  | ERecord: list KeyValue -> Expression
  | EUnaryOp : OpUni -> Expression -> Expression
  | EbinaryOp : OpBin -> Expression -> Expression -> Expression
  | ECast : Typ -> Expression -> Expression
  | ETypeMember : Name -> string -> Expression
  | EErrorMember : string -> Expression
  | EExpressionMember : Expression -> string -> Expression
  | ETernary : Expression -> Expression -> Expression -> Expression
  | EFunctionCall : Expression -> list Typ -> list (option Expression) -> Expression
  | ENamelessInstantiation : Typ -> list Expression -> Expression
  | EDontCare
  | EMask : Expression -> Expression -> Expression
  | ERange : Expression -> Expression -> Expression
with KeyValue :=
  | KV : string -> Expression -> KeyValue
with Typ :=
  | TBool
  | TString
  | TInteger
  | TInt : nat -> Typ
  | TBit : nat -> Typ
  | TVarBit : nat -> Typ
  | TArray : Typ -> nat -> Typ
  | TTuple : list Typ -> Typ
  | TList : list Typ -> Typ
  | TRecord : RecordType -> Typ
  | TSet : Typ -> Typ
  | TError
  | TMatchKind
  | TTypeName : Name -> Typ
  | TNewType : string -> Typ -> Typ
  | TVoid
  | THeader : RecordType -> Typ
  | THeaderUnion : RecordType -> Typ
  | TStruct : RecordType -> Typ
  | TEnum : string -> option Typ -> list string -> Typ
  | TSpecializedType : Typ -> list Typ -> Typ
  | TPackage : list string -> list string -> list Param -> Typ
  | TControl : ControlType -> Typ
  | TParser : ControlType -> Typ
  | TExtern : list string -> list (string * FunctionType) -> Typ
  | TFunction : FunctionType -> Typ
  | TAction : list Param -> list Param -> Typ
  | TConstructor : list string -> list string -> list Param -> Typ -> Typ
  | TTable : string -> Typ
with RecordType :=
  | RecordT : list (string * Typ) -> RecordType
with ControlType :=
  | ControlT : list string -> list Param -> ControlType
with FunctionType :=
  | FunctionT : list string -> list Param -> FunctionTypeKind -> Typ -> FunctionType
with Param :=
  | ParameterC : list Annotation -> Direction -> Typ -> string -> option Expression -> Param
with Annotation_body :=
  | Empty
  | Unparsed : list string -> Annotation_body
  | AExpression : list Expression -> Annotation_body
  | AKeyValue : list KeyValue -> Annotation_body
with Annotation :=
  | MkAnnotation : string -> Annotation_body -> Annotation.








