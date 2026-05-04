#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Expr {
    Bool(bool),
    Int(IntLiteral),
    Var(String),
    Interpolated(String),
    RustType(RustTypeExpr),
    SeqLit(Vec<Expr>),
    StructLit {
        name: String,
        fields: Vec<StructLitField>,
    },
    Match {
        scrutinee: Box<Expr>,
        arms: Vec<MatchArm>,
        default: Option<Box<Expr>>,
    },
    Call {
        func: String,
        type_args: Vec<SpecTy>,
        args: Vec<Expr>,
    },
    Field {
        base: Box<Expr>,
        name: String,
    },
    TupleField {
        base: Box<Expr>,
        index: usize,
    },
    Index {
        base: Box<Expr>,
        index: Box<Expr>,
    },
    Deref {
        base: Box<Expr>,
    },
    Unary {
        op: UnaryOp,
        arg: Box<Expr>,
    },
    Binary {
        op: BinaryOp,
        lhs: Box<Expr>,
        rhs: Box<Expr>,
    },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TypedExpr {
    pub ty: SpecTy,
    pub kind: TypedExprKind,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MatchArm {
    pub pattern: MatchPattern,
    pub body: Expr,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct StructLitField {
    pub name: String,
    pub value: Expr,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum MatchPattern {
    Constructor {
        enum_name: String,
        ctor_name: String,
        bindings: Vec<MatchBinding>,
    },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum MatchBinding {
    Var(String),
    Wildcard,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TypedExprKind {
    Bool(bool),
    Int(IntLiteral),
    Var(String),
    RustVar(String),
    RustType(RustTyKey),
    SeqLit(Vec<TypedExpr>),
    StructLit {
        fields: Vec<TypedExpr>,
    },
    Match {
        scrutinee: Box<TypedExpr>,
        arms: Vec<TypedMatchArm>,
        default: Option<Box<TypedExpr>>,
    },
    PureCall {
        func: String,
        args: Vec<TypedExpr>,
    },
    CtorCall {
        enum_name: String,
        ctor_name: String,
        ctor_index: usize,
        args: Vec<TypedExpr>,
    },
    Field {
        base: Box<TypedExpr>,
        name: String,
        index: usize,
    },
    TupleField {
        base: Box<TypedExpr>,
        index: usize,
    },
    Index {
        base: Box<TypedExpr>,
        index: Box<TypedExpr>,
    },
    Unary {
        op: UnaryOp,
        arg: Box<TypedExpr>,
    },
    Binary {
        op: BinaryOp,
        lhs: Box<TypedExpr>,
        rhs: Box<TypedExpr>,
    },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TypedMatchArm {
    pub ctor_index: usize,
    pub enum_name: String,
    pub ctor_name: String,
    pub bindings: Vec<TypedMatchBinding>,
    pub body: TypedExpr,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TypedMatchBinding {
    Var { name: String, ty: SpecTy },
    Wildcard { ty: SpecTy },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum IntSuffix {
    Nat,
    I8,
    I16,
    I32,
    I64,
    Isize,
    U8,
    U16,
    U32,
    U64,
    Usize,
}

impl IntSuffix {
    pub fn spec_ty(self) -> SpecTy {
        match self {
            Self::Nat => SpecTy::Enum {
                name: "Nat".to_owned(),
                args: vec![],
            },
            Self::I8 => SpecTy::I8,
            Self::I16 => SpecTy::I16,
            Self::I32 => SpecTy::I32,
            Self::I64 => SpecTy::I64,
            Self::Isize => SpecTy::Isize,
            Self::U8 => SpecTy::U8,
            Self::U16 => SpecTy::U16,
            Self::U32 => SpecTy::U32,
            Self::U64 => SpecTy::U64,
            Self::Usize => SpecTy::Usize,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct IntLiteral {
    pub digits: String,
    pub suffix: Option<IntSuffix>,
}

impl IntLiteral {
    pub fn spec_ty(&self) -> SpecTy {
        self.suffix
            .map(IntSuffix::spec_ty)
            .unwrap_or(SpecTy::IntLiteral)
    }

    pub(crate) fn as_unsuffixed_usize(&self) -> Option<usize> {
        match self.suffix {
            Some(_) => None,
            None => self.digits.parse::<usize>().ok(),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct RustTypeExpr {
    pub text: String,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct RustTyKey {
    canonical: String,
}

impl RustTyKey {
    pub fn new(canonical: impl Into<String>) -> Self {
        Self {
            canonical: canonical.into(),
        }
    }

    pub fn as_str(&self) -> &str {
        &self.canonical
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum SpecTy {
    Bool,
    RustTy,
    Int,
    IntLiteral,
    I8,
    I16,
    I32,
    I64,
    Isize,
    U8,
    U16,
    U32,
    U64,
    Usize,
    Seq(Box<SpecTy>),
    Tuple(Vec<SpecTy>),
    Struct(StructTy),
    Enum { name: String, args: Vec<SpecTy> },
    TypeParam(String),
    Ref(Box<SpecTy>),
    Mut(Box<SpecTy>),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PureFnParam {
    pub name: String,
    pub ty: SpecTy,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PureFnDef {
    pub name: String,
    pub type_params: Vec<String>,
    pub params: Vec<PureFnParam>,
    pub result_ty: SpecTy,
    pub body: Expr,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum GhostStmt {
    Assert(Expr),
    Assume(Expr),
    Call {
        name: String,
        type_args: Vec<SpecTy>,
        args: Vec<Expr>,
    },
    Match {
        scrutinee: Expr,
        arms: Vec<GhostMatchArm>,
        default: Option<Vec<GhostStmt>>,
    },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct GhostMatchArm {
    pub pattern: MatchPattern,
    pub body: Vec<GhostStmt>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LemmaDef {
    pub name: String,
    pub is_unsafe: bool,
    pub type_params: Vec<String>,
    pub params: Vec<PureFnParam>,
    pub req: Expr,
    pub resource_reqs: Vec<ResourceAssertion>,
    pub ens: Expr,
    pub resource_ens: Vec<ResourceAssertion>,
    pub body: Vec<GhostStmt>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ResourceAssertion {
    pub pattern: ResourcePattern,
    pub condition: Expr,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ResourcePattern {
    Star(Box<ResourcePattern>, Box<ResourcePattern>),
    PointsTo {
        addr: Expr,
        ty: Expr,
        value: ValuePattern,
    },
    PointsToSugar {
        pointer: String,
        value: ValuePattern,
    },
    DeallocToken {
        base: Expr,
        size: Expr,
        alignment: Expr,
    },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ValuePattern {
    Bind(String),
    Expr(Expr),
    SeqLit(Vec<ValuePattern>),
    StructLit {
        name: String,
        fields: Vec<ValuePatternStructField>,
    },
    Call {
        func: String,
        type_args: Vec<SpecTy>,
        args: Vec<ValuePattern>,
    },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ValuePatternStructField {
    pub name: String,
    pub value: ValuePattern,
}

#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct GhostBlock {
    pub enums: Vec<EnumDef>,
    pub structs: Vec<StructDef>,
    pub pure_fns: Vec<PureFnDef>,
    pub lemmas: Vec<LemmaDef>,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct EnumDef {
    pub name: String,
    pub type_params: Vec<String>,
    pub ctors: Vec<EnumCtorDef>,
}

impl EnumDef {
    pub fn ctor(&self, name: &str) -> Option<(usize, &EnumCtorDef)> {
        self.ctors
            .iter()
            .enumerate()
            .find(|(_, ctor)| ctor.name == name)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct EnumCtorDef {
    pub name: String,
    pub fields: Vec<SpecTy>,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct StructDef {
    pub name: String,
    pub type_params: Vec<String>,
    pub fields: Vec<StructFieldTy>,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct StructTy {
    pub name: String,
    pub fields: Vec<StructFieldTy>,
}

impl StructTy {
    pub fn field(&self, name: &str) -> Option<(usize, &StructFieldTy)> {
        self.fields
            .iter()
            .enumerate()
            .find(|(_, field)| field.name == name)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct StructFieldTy {
    pub name: String,
    pub ty: SpecTy,
}

pub fn rust_ty_spec_ty() -> SpecTy {
    SpecTy::RustTy
}

pub fn option_spec_ty(inner: SpecTy) -> SpecTy {
    SpecTy::Enum {
        name: "Option".to_owned(),
        args: vec![inner],
    }
}

pub fn provenance_spec_ty() -> SpecTy {
    SpecTy::Struct(StructTy {
        name: "Provenance".to_owned(),
        fields: vec![StructFieldTy {
            name: "base".to_owned(),
            ty: SpecTy::Usize,
        }],
    })
}

pub fn ptr_spec_ty() -> SpecTy {
    SpecTy::Struct(StructTy {
        name: "Ptr".to_owned(),
        fields: vec![
            StructFieldTy {
                name: "addr".to_owned(),
                ty: SpecTy::Usize,
            },
            StructFieldTy {
                name: "prov".to_owned(),
                ty: option_spec_ty(provenance_spec_ty()),
            },
            StructFieldTy {
                name: "ty".to_owned(),
                ty: rust_ty_spec_ty(),
            },
        ],
    })
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum UnaryOp {
    Not,
    Neg,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BinaryOp {
    Add,
    Sub,
    Mul,
    Concat,
    Eq,
    Ne,
    Gt,
    Ge,
    Lt,
    Le,
    And,
    Or,
}
