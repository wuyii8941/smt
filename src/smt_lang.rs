
use egg::*;
use ordered_float::NotNan;


define_language! {
    pub enum SmtLang {
        "+" = Add(Vec<Id>),
        "-" = Sub([Id; 2]),
        "*" = Mul(Vec<Id>),
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

        "sqrt" = Sqrt(Id),


        Symbol(Symbol),
        Constant(NotNan<f64>),
    }
}