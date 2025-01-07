/* smt语言定义
*/ 
use egg::*;
use ordered_float::NotNan;

// SMT Language Definition
pub enum Smt {
    Add([Id; 2]),
    Sub([Id; 2]),
    Mul([Id; 2]),
    Div([Id; 2]),
    Pow([Id; 2]),

    Gt([Id; 2]),
    Ge([Id; 2]),
    Lt([Id; 2]),
    Le([Id; 2]),
    Eq([Id; 2]),

    And([Id; 2]),
    Or([Id; 2]),
    Not(Id),

    Symbol(Symbol),
    Constant(NotNan<f64>),
}

define_language! {
    pub enum SmtLang {
        "add" = AddMultiset(Vec<Id>),  // 多项加法
        "mul" = MulMultiset(Vec<Id>),  // 多项乘法
        "+" = Add([Id; 2]),
        "-" = Sub([Id; 2]),
        "*" = Mul([Id; 2]),
        "/" = Div([Id; 2]),
        "^" = Pow([Id; 2]),

        ">" = Gt([Id; 2]),
        ">=" = Ge([Id; 2]),
        "<" = Lt([Id; 2]),
        "<=" = Le([Id; 2]),
        "=" = Eq([Id; 2]),

        "and" = And([Id; 2]),
        "or" = Or([Id; 2]),
        "not" = Not(Id),

        Symbol(Symbol),
        Constant(NotNan<f64>),
    }
}