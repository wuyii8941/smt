use crate::smt_lang::SmtLang;
use egg::{rewrite as rw, *};
use ordered_float::NotNan;
use std::collections::HashMap;

#[derive(Default)]
pub struct ConstantFold;

fn expression_cost(expr: &RecExpr<SmtLang>) -> usize {
    expr.as_ref()
        .iter()
        .map(|node| match node {
            SmtLang::Add(_) => 1,
            SmtLang::Mul(_) => 2,
            SmtLang::Pow(_) => 5, // 假设乘方的代价较高
            SmtLang::Sqrt(_) => 10, // 假设平方根的代价最高
            _ => 0,
        })
        .sum() // 累加代价
}

impl Analysis<SmtLang> for ConstantFold {
    type Data = Option<(NotNan<f64>, PatternAst<SmtLang>)>;

    fn make(egraph: &EGraph<SmtLang, ConstantFold>, enode: &SmtLang) -> Self::Data {
        let x = |i: &Id| egraph[*i].data.as_ref().map(|d| d.0);
        Some(match enode {
            SmtLang::Constant(c) => (*c, format!("{}", c).parse().unwrap()),
            SmtLang::Symbol(symbol) => {
                println!("Symbol encountered: {:?}", symbol);
                return None;
            }
            SmtLang::Add(children) => {
                let mut sum = NotNan::new(0.0).unwrap();
                let mut has_symbol = false;
                let mut pattern_parts = Vec::new();

                for &child in children {
                    match x(&child) {
                        Some(value) => {
                            sum += value;
                            pattern_parts.push(format!("{}", value));
                        }
                        None => has_symbol = true,
                    }
                }

                if has_symbol {
                    return None;
                }

                (
                    sum,
                    format!("(+ {})", pattern_parts.join(" ")).parse().unwrap(),
                )
            }

            SmtLang::Mul(children) => {
                let mut product = NotNan::new(1.0).unwrap();
                let mut has_symbol = false;
                let mut pattern_parts = Vec::new();

                for &child in children {
                    match x(&child) {
                        Some(value) => {
                            product *= value;
                            pattern_parts.push(format!("{}", value));
                        }
                        None => has_symbol = true,
                    }
                }

                if has_symbol {
                    return None;
                }

                (
                    product,
                    format!("(* {})", pattern_parts.join(" ")).parse().unwrap(),
                )
            }
            SmtLang::Div([a, b]) if x(b) != Some(NotNan::new(0.0).unwrap()) => (
                x(a)? / x(b)?,
                format!("(/ {} {})", x(a)?, x(b)?).parse().unwrap(),
            ),
            SmtLang::Pow([a, b]) => {
                let base = x(a)?;
                let exponent = x(b)?.into_inner(); // 转换 NotNan<f64> 为 f64
                (
                    NotNan::new(base.powf(exponent)).unwrap(), // 重新封装为 NotNan<f64>
                    format!("(^ {} {})", base, exponent).parse().unwrap(),
                )
            }
            SmtLang::Gt([a, b]) => {
                let left = x(a)?;
                let right = x(b)?;
                (
                    NotNan::new((left > right) as u8 as f64).unwrap(),
                    format!("(> {} {})", left, right).parse().unwrap(),
                )
            }
            SmtLang::Ge([a, b]) => {
                let left = x(a)?;
                let right = x(b)?;
                (
                    NotNan::new((left >= right) as u8 as f64).unwrap(),
                    format!("(>= {} {})", left, right).parse().unwrap(),
                )
            }
            SmtLang::Lt([a, b]) => {
                let left = x(a)?;
                let right = x(b)?;
                (
                    NotNan::new((left < right) as u8 as f64).unwrap(),
                    format!("(< {} {})", left, right).parse().unwrap(),
                )
            }
            SmtLang::Le([a, b]) => {
                let left = x(a)?;
                let right = x(b)?;
                (
                    NotNan::new((left <= right) as u8 as f64).unwrap(),
                    format!("(<= {} {})", left, right).parse().unwrap(),
                )
            }
            SmtLang::Eq([a, b]) => {
                let left = x(a)?;
                let right = x(b)?;
                (
                    NotNan::new((left == right) as u8 as f64).unwrap(),
                    format!("(= {} {})", left, right).parse().unwrap(),
                )
            }
            SmtLang::And([a, b]) => {
                let left = x(a)?;
                let right = x(b)?;
                (
                    NotNan::new(((left != 0.0) && (right != 0.0)) as u8 as f64).unwrap(),
                    format!("(and {} {})", left, right).parse().unwrap(),
                )
            }
            SmtLang::Or([a, b]) => {
                let left = x(a)?;
                let right = x(b)?;
                (
                    NotNan::new(((left != 0.0) || (right != 0.0)) as u8 as f64).unwrap(),
                    format!("(or {} {})", left, right).parse().unwrap(),
                )
            }
            SmtLang::Not(a) => {
                let value = x(a)?;
                (
                    NotNan::new((value == 0.0) as u8 as f64).unwrap(),
                    format!("(not {})", value).parse().unwrap(),
                )
            }
            SmtLang::Sqrt(a) => {
                let value_opt = x(a);
                if let Some(value) = value_opt {
                    if value >= NotNan::new(0.0).unwrap() {
                        return Some((
                            NotNan::new(value.into_inner().sqrt()).unwrap(),
                            format!("(sqrt {})", value).parse().unwrap(),
                        ));
                    }
                }
                println!("Skipping direct sqrt computation for non-constant {:?}", a);
                return None; // 直接返回 None
            }
            _ => {
                println!("BadOp detected in node: {:?}", enode);
                return None;
            }
        })
    }

    fn merge(&mut self, to: &mut Self::Data, from: Self::Data) -> DidMerge {
        merge_option(to, from, |a, b| {
            assert_eq!(a.0, b.0, "Merged non-equal constants");
            DidMerge(false, false)
        })
    }

    fn modify(egraph: &mut EGraph<SmtLang, ConstantFold>, id: Id) {
        let data = egraph[id].data.clone();
        if let Some((c, pat)) = data {
            if egraph.are_explanations_enabled() {
                egraph.union_instantiations(
                    &pat,
                    &format!("{}", c).parse().unwrap(),
                    &Default::default(),
                    "constant_fold".to_string(),
                );
            } else {
                let added = egraph.add(SmtLang::Constant(c));
                egraph.union(id, added);
            }
            egraph[id].nodes.retain(|n| n.is_leaf());
        }
    }
}

// /// 计算表达式的复杂度（通过加法、乘法等操作的数量）
// fn expression_complexity(expr: &str) -> usize {
//     expr.chars()
//         .filter(|&c| c == '+' || c == '*' || c == '^')
//         .count()
// }


pub fn rules() -> Vec<Rewrite<SmtLang, ConstantFold>> {
    let mut rules = vec![
        // 加法和乘法的交换律
        rewrite!("add-comm"; "(+ ?a ?b)" => "(+ ?b ?a)"),
        rewrite!("mul-comm"; "(* ?a ?b)" => "(* ?b ?a)"),
        // 加法和乘法的结合律
        rewrite!("add-assoc"; "(+ ?a (+ ?b ?c))" => "(+ (+ ?a ?b) ?c)"),
        rewrite!("add-assoc-rev"; "(+ (+ ?a ?b) ?c)" => "(+ ?a (+ ?b ?c))"),
        rewrite!("mul-assoc"; "(* ?a (* ?b ?c))" => "(* (* ?a ?b) ?c)"),
        rewrite!("mul-assoc-rev"; "(* (* ?a ?b) ?c)" => "(* ?a (* ?b ?c))"),
        // 减法的等价重写
        rewrite!("sub-canon"; "(+ ?a (- ?b ?c))" => "(- (+ ?a ?b) ?c)"),
        rewrite!("sub-canon-rev"; "(- (+ ?a ?b) ?c)" => "(+ ?a (- ?b ?c))"),
        // 除法的等价重写
        rewrite!("div-canon"; "(/ ?x ?y)" => "(* ?x (/ 1 ?y))"),
        rewrite!("div-canon-rev"; "(* ?x (/ 1 ?y))" => "(/ ?x ?y)"),
        // 处理加法和乘法的单位元
        rewrite!("add-zero"; "(+ ?a 0)" => "?a"),
        rewrite!("add-zero-rev"; "?a" => "(+ ?a 0)"),
        rewrite!("mul-one"; "(* ?a 1)" => "?a"),
        rewrite!("mul-one-rev"; "?a" => "(* ?a 1)"),
        // 平方公式的展开与折叠
        rewrite!("square-expand"; "(^ (+ ?a ?b) 2)" => "(+ (^ ?a 2) (+ (^ ?b 2) (* 2 (* ?a ?b))))"),
        rewrite!("square-collapse"; "(+ (^ ?a 2) (+ (^ ?b 2) (* 2 (* ?a ?b))))" => "(^ (+ ?a ?b) 2)"),
        // 均值不等式重写
        rewrite!(
            "apply-mean-inequality";
            "(+ (/ ?x (sqrt (+ (^ ?x 2) (* 8 ?y ?z)))) \
                (/ ?y (sqrt (+ (^ ?y 2) (* 8 ?z ?x)))) \
                (/ ?z (sqrt (+ (^ ?z 2) (* 8 ?x ?y)))))" =>
            "(>= (+ ?x ?y ?z) 1)"
        ),
        // 平方根平方消除
        rewrite!("sqrt-square"; "(^ (sqrt ?x) 2)" => "?x"),
        // 根式乘法展开
        rewrite!("sqrt-mul-expand"; "(* (sqrt ?x) (sqrt ?y))" => "(sqrt (* ?x ?y))"),
        // 根式分母有理化
        rewrite!("rationalize-denominator"; "(/ ?a (sqrt ?b))" => "(/ (* ?a (sqrt ?b)) ?b)"),
        rewrite!("sqrt-ineq-gt-alt"; "(> (sqrt ?a) ?b)" => "(> ?a (^ ?b 2))") ,
        rewrite!("sqrt-ineq-lt"; "(< (sqrt ?a) ?b)" => "(< ?a (^ ?b 2))"),
        rewrite!("sqrt-ineq-ge"; "(>= (sqrt ?a) ?b)" => "(>= ?a (^ ?b 2))"),
        rewrite!("sqrt-ineq-le"; "(<= (sqrt ?a) ?b)" => "(<= ?a (^ ?b 2))"),
    ];
    rules
}

pub fn apply_rewrites(expr: &RecExpr<SmtLang>) -> RecExpr<SmtLang> {
    let rewrites = rules();
    println!("Original expression: {}", expr);
    println!("Checking initial EGraph state:");

    let cost = expression_cost(expr);
    if cost > 50 { // 设定一个代价阈值，超过阈值则不重写
        println!("Expression has too high cost ({}), skipping rewrite.", cost);
        return expr.clone(); // 返回原始表达式
    }

    let runner = Runner::default()
        .with_expr(expr)
        .with_hook(|runner| {
            let iter_index = runner.iterations.len();
            if iter_index > 0 {
                println!("--- Iteration {} ---", iter_index);
                println!("Applied rules: {:?}", runner.iterations[iter_index - 1].applied);
            }
            println!("Current egraph state:");
            for id in 0..runner.egraph.number_of_classes() {
                println!("EClass {}: {:?}", id, runner.egraph[Id::from(id)].nodes);
            }
            Ok(())
        })
        
        .run(&rewrites);

    if runner.roots.is_empty() {
        panic!("No roots found after applying rewrites.");
    }

    let extractor = Extractor::new(&runner.egraph, AstSize);
    let (_, best_expr) = extractor.find_best(runner.roots[0]);
    println!("Best expression found: {}", best_expr);

    best_expr
}

pub fn rewrite_expressions<'a>(expressions: Vec<RecExpr<SmtLang>>) -> Vec<String> {
    expressions
        .into_iter()
        .map(|expr| {
            let rewritten = apply_rewrites(&expr);
            format!("{}", rewritten) // 将重写结果格式化为字符串
        })
        .collect()
}


// 修改rewrite_expressions_with_limit，结合表达式代价和限制
pub fn rewrite_expressions_with_limit(
    expressions: Vec<RecExpr<SmtLang>>,
    limit: usize,
) -> Vec<String> {
    expressions
        .into_iter()
        .map(|expr| {
            let complexity = expression_cost(&expr);
            if complexity <= limit {
                apply_rewrites(&expr)
            } else {
                println!("Expression too complex (cost: {}), skipping rewrite.", complexity);
                expr // 如果复杂度过高，直接返回原表达式
            }
        })
        .map(|rewritten| format!("{}", rewritten))
        .collect()
}