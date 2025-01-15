use egg::{rewrite as rw, *};
use crate::smt_lang::SmtLang;
use ordered_float::NotNan;
use std::collections::HashMap;

#[derive(Default)]
pub struct ConstantFold;

impl Analysis<SmtLang> for ConstantFold {
    type Data = Option<(NotNan<f64>, PatternAst<SmtLang>)>;

    fn make(egraph: &EGraph<SmtLang, ConstantFold>, enode: &SmtLang) -> Self::Data {
        let x = |i: &Id| egraph[*i].data.as_ref().map(|d| d.0);
        Some(match enode {
            SmtLang::Constant(c) => (*c, format!("{}", c).parse().unwrap()),
            SmtLang::Add([a, b]) => (
                x(a)? + x(b)?,
                format!("(+ {} {})", x(a)?, x(b)?).parse().unwrap(),
            ),
            SmtLang::Sub([a, b]) => (
                x(a)? - x(b)?,
                format!("(- {} {})", x(a)?, x(b)?).parse().unwrap(),
            ),
            SmtLang::Mul([a, b]) => (
                x(a)? * x(b)?,
                format!("(* {} {})", x(a)?, x(b)?).parse().unwrap(),
            ),
            SmtLang::Div([a, b]) if x(b) != Some(NotNan::new(0.0).unwrap()) => (
                x(a)? / x(b)?,
                format!("(/ {} {})", x(a)?, x(b)?).parse().unwrap(),
            ),
            _ => return None,
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

pub fn rules() -> Vec<Rewrite<SmtLang, ConstantFold>> {
    vec![
        rw!("gt_lt_swap"; "(> ?a ?b)" => "(< ?b ?a)"),
        rw!("ge_le_swap"; "(>= ?a ?b)" => "(<= ?b ?a)"),

        // 消除冗余项
        rw!("zero-add"; "(+ ?a 0)" => "?a"),
        rw!("zero-mul"; "(* ?a 0)" => "0"),
        rw!("mul-one"; "(* ?a 1)" => "?a"),

        // 扁平化加法
        rw!("flat-sum"; "(+ ?a (+ ?b ?c))" => "(+ (+ ?a ?b) ?c)"),
        rw!("flat-prod"; "(* ?a (* ?b ?c))" => "(* (* ?a ?b) ?c)"),

        // 线性化分数项
        rw!("div-linear"; "(/ 1 (^ (+ ?a ?b) 2))" => "(* 0.5 (^ (+ ?a ?b) -2))"),

        // 提取公因式
        rw!("factor-out"; "(+ (* ?x ?y) (* ?x ?z))" => "(* ?x (+ ?y ?z))"),

        // 分布律展开
        rw!("distribute"; "(* ?x (+ ?y ?z))" => "(+ (* ?x ?y) (* ?x ?z))"),

        // 平方公式的展开与折叠
        rw!("square-expand"; "(^ (+ ?a ?b) 2)" => "(+ (^ ?a 2) (+ (^ ?b 2) (* 2 (* ?a ?b))))"),
        rw!("square-collapse"; "(+ (^ ?a 2) (+ (^ ?b 2) (* 2 (* ?a ?b))))" => "(^ (+ ?a ?b) 2)"),
    ]
}

pub fn apply_rewrites(expr: &RecExpr<SmtLang>) -> RecExpr<SmtLang> {
    let rewrites = rules();
    let runner = Runner::default().with_expr(expr).run(&rewrites);

    if runner.roots.is_empty() {
        panic!("No roots found after applying rewrites.");
    }

    let extractor = Extractor::new(&runner.egraph, AstSize);
    let (_, best_expr) = extractor.find_best(runner.roots[0]);

    best_expr
}

/// 批量重写表达式
pub fn rewrite_expressions<'a>(expressions: Vec<RecExpr<SmtLang>>) -> Vec<String> {
    expressions
        .into_iter()
        .map(|expr| {
            let rewritten = apply_rewrites(&expr);
            format!("{}", rewritten) // 将重写结果格式化为字符串
        })
        .collect()
}

/// 表达式复杂度计算
fn expression_complexity(expr: &str) -> usize {
    expr.chars().filter(|&c| c == '+' || c == '*' || c == '^').count()
}

pub fn rewrite_expressions_with_limit(expressions: Vec<RecExpr<SmtLang>>, limit: usize) -> Vec<String> {
    expressions
        .into_iter()
        .map(|expr| {
            let complexity = expression_complexity(&format!("{}", expr));
            if complexity <= limit {
                // 简单表达式，直接匹配
                apply_rewrites(&expr)
            } else {
                // 复杂表达式，使用缓存逻辑
                let mut cache: HashMap<String, RecExpr<SmtLang>> = HashMap::new();
                if let Some(cached_result) = cache.get(&format!("{}", expr)) {
                    cached_result.clone()
                } else {
                    let result = apply_rewrites(&expr);
                    cache.insert(format!("{}", expr), result.clone());
                    result
                }
            }
        })
        .map(|rewritten| format!("{}", rewritten))
        .collect()
}