use egg::{rewrite as rw, *};
use egg::{Applier, EGraph, Id, Rewrite, Subst};

use crate::smt_lang::SmtLang;
use crate::smt_lang::SmtLang::{Pow, Constant, AddMultiset, Mul};

use ordered_float::NotNan;
use std::str::FromStr; // 确保可以使用 from_str 方法
use log::debug;



#[derive(Default)]
pub struct ConstantFold;

fn validate_mulset(
    egraph: &EGraph<SmtLang, ()>, 
    a: Id, 
    b: Id, 
    c: Id
) -> Option<(Id, Id)> {
    println!("Validating mulset: ?a = {:?}, ?b = {:?}, ?c = {:?}", a, b, c);

    // Helper function to check if a node is a square term (e.g., (^ x 2))
    let is_square = |id: Id| -> Option<Id> {
        for node in &egraph[id].nodes {
            if let SmtLang::Pow([base, exponent]) = node {
                if let Some(SmtLang::Constant(c)) = egraph[*exponent].nodes.iter().find_map(|n| {
                    if let SmtLang::Constant(val) = n {
                        if val.into_inner() == 2.0 {
                            Some(SmtLang::Constant(val.clone()))
                        } else {
                            None
                        }
                    } else {
                        None
                    }
                }) {
                    return Some(*base);
                }
            }
        }
        None
    };

    // Validate if `a` and `b` are square terms
    let a_base = is_square(a)?;
    let b_base = is_square(b)?;

    // Helper to extract the `Symbol` value from an `Id`
    let get_symbol = |id: Id| -> Option<&egg::Symbol> {
        egraph[id].nodes.iter().find_map(|node| {
            if let SmtLang::Symbol(s) = node {
                Some(s)
            } else {
                None
            }
        })
    };

    // Check if `c` matches the structure `(* (* 2 a_base) b_base)`
    let is_valid_c = egraph[c].nodes.iter().any(|node| {
        if let SmtLang::MulMultiset(children) = node {
            let mut has_two = false;
            let mut has_a = false;
            let mut has_b = false;

            for &child in children {
                for inner_node in &egraph[child].nodes {
                    match inner_node {
                        SmtLang::Constant(c) if c.into_inner() == 2.0 => has_two = true,
                        SmtLang::Symbol(symbol) if Some(symbol) == get_symbol(a_base) => has_a = true,
                        SmtLang::Symbol(symbol) if Some(symbol) == get_symbol(b_base) => has_b = true,
                        _ => {}
                    }
                }
            }

            has_two && has_a && has_b
        } else {
            false
        }
    });

    if is_valid_c {
        println!(
            "Validation succeeded: a_base = {:?}, b_base = {:?}, product term matches",
            a_base, b_base
        );
        return Some((a_base, b_base));
    }

    println!("Validation failed for a = {:?}, b = {:?}, c = {:?}", a, b, c);
    None
}



fn condition_to_sort(egraph: &mut EGraph<SmtLang, ()>, _: Id, subst: &Subst) -> bool {
    let x = subst["?x".parse().unwrap()];
    let y = subst["?y".parse().unwrap()];
    x < y // 比较节点的 ID，按顺序排列
}

pub struct SquareCollapseApplier;

impl Applier<SmtLang, ()> for SquareCollapseApplier {
    fn apply_one(
        &self,
        egraph: &mut EGraph<SmtLang, ()>,
        id: Id,
        subst: &Subst,
        _expr: Option<&RecExpr<ENodeOrVar<SmtLang>>>,
        _symbol: Symbol,
    ) -> Vec<Id> {
        let a_var: Var = "?a".parse().unwrap();
        let b_var: Var = "?b".parse().unwrap();
        let c_var: Var = "?c".parse().unwrap();

        let a = subst[a_var];
        let b = subst[b_var];
        let c = subst[c_var];

        println!("Matched: ?a = {:?}, ?b = {:?}, ?c = {:?}", a, b, c);

        if let Some((x, y)) = validate_mulset(egraph, a, b, c) {
            let add_id = egraph.add(SmtLang::Add([x, y]));
            let constant_two = egraph.add(SmtLang::Constant(NotNan::new(2.0).unwrap()));
            let pow_id = egraph.add(SmtLang::Pow([add_id, constant_two]));
        
            // 合并新节点到当前等价类
            egraph.union(id, pow_id);
        
            println!("Merged node {:?} into class {:?}", pow_id, id);
        
            return vec![pow_id];
        }

        vec![]
    }
}


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


pub fn rules() -> Vec<Rewrite<SmtLang, ()>> {
    vec![
        Rewrite::new(
            "square-collapse-mulset",
            "(add ?a ?b ?c)".parse::<Pattern<SmtLang>>().unwrap(),
            SquareCollapseApplier,
        )
        .unwrap(),
    
    // rw!("normalize-add-mulset"; "(add ?x ?y)" => "(add ?y ?x)" if condition_to_sort),
    // rw!("normalize-mul-mulset"; "(mul ?x ?y)" => "(mul ?y ?x)" if condition_to_sort),
    // rw!("flatten-add-mulset"; "(add ?a (add ?b ?c))" => "(add ?a ?b ?c)"),
    // rw!("flatten-mul-mulset"; "(mul ?a (mul ?b ?c))" => "(mul ?a ?b ?c)"),
    // rw!("remove-duplicate-add"; "(add ?a ?a)" => "(mul ?a 2)"),
    // rw!("remove-duplicate-mul"; "(mul ?a ?a)" => "(^ ?a 2)"),

    ]
}



pub fn apply_rewrites(expr: &RecExpr<SmtLang>) -> RecExpr<SmtLang> {
    let rewrites = rules();
    let runner = Runner::default()
        .with_expr(expr)
        .with_scheduler(SimpleScheduler) // 强制简单调度器
        .with_iter_limit(10) // 限制迭代次数
        .with_node_limit(10_000) // 限制节点数
        .run(&rewrites);
    dbg!(expr);
    if runner.roots.is_empty() {
        panic!("No roots found after applying rewrites.");
    }
    for (i, iteration) in runner.iterations.iter().enumerate() {
        println!("Iteration {}: Applied {} rules", i + 1, iteration.applied.len());
        for applied in &iteration.applied {
            println!("  Rule applied: {:?}", applied);
            let rule_name = applied.0.to_string();
            println!("Input after rule application: {:?}", runner.egraph);
            
            // if rule_name == "flatten-add" || rule_name == "flatten-mul" {
            //     println!("E-Graph state after {}: {:#?}", rule_name, runner.egraph);
            // }
        }
    }
    dbg!(expr);
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
