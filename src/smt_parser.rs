use egg::*;
use std::fs;
use ordered_float::NotNan;
use std::collections::HashSet;


use crate::smt_lang;
use crate::smt_lang::SmtLang;


pub fn parse_smt_expression(expr: &str, builder: &mut RecExpr<SmtLang>) -> Result<Id, String> {
    // 去除外层括号
    let expr = expr
       .trim()
       .strip_prefix('(')
       .and_then(|s| s.strip_suffix(')'))
       .unwrap_or(expr);

    // println!("Parsing expression: {}", expr);

    if let Ok(value) = expr.parse::<f64>() {
        let constant = NotNan::new(value).map_err(|_| "Invalid constant value".to_string())?;
        return Ok(builder.add(SmtLang::Constant(constant)));
    }

    if!expr.contains(' ') {
        let symbol = Symbol::from(expr);
        return Ok(builder.add(SmtLang::Symbol(symbol)));
    }

    let first_space = expr.find(' ').ok_or("Invalid SMT expression")?;
    let operator = &expr[..first_space];
    let args = &expr[first_space + 1..];

    println!("Operator: '{}', Arguments: '{}'", operator, args);

    // 修复split_arguments，忽视外层括号
    let arg_list = split_arguments(args).map_err(|e| {
        format!(
            "Error splitting arguments in expression '{}': {}",
            expr, e
        )
    })?;

    let arg_ids: Vec<Id> = arg_list
       .iter()
       .map(|arg| parse_smt_expression(arg, builder))
       .collect::<Result<_, _>>()?;

    let op = match operator {
"+" => {
    let mut combined = Vec::new();
    for &arg in &arg_ids {
        combined.push(arg);
    }
    combined.sort(); // 对元素排序，确保无序匹配
    SmtLang::AddMultiset(combined)
},
"*" => {
    let mut combined = Vec::new();
    for &arg in &arg_ids {
        combined.push(arg);
    }
    combined.sort(); // 对元素排序，确保无序匹配
    SmtLang::MulMultiset(combined)
},
        "-" => SmtLang::Sub([arg_ids[0], arg_ids[1]]),
        "/" => SmtLang::Div([arg_ids[0], arg_ids[1]]),
        "^" => SmtLang::Pow([arg_ids[0], arg_ids[1]]),
        ">" => SmtLang::Gt([arg_ids[0], arg_ids[1]]),
        ">=" => SmtLang::Ge([arg_ids[0], arg_ids[1]]),
        "<" => SmtLang::Lt([arg_ids[0], arg_ids[1]]),
        "<=" => SmtLang::Le([arg_ids[0], arg_ids[1]]),
        "=" => SmtLang::Eq([arg_ids[0], arg_ids[1]]),
        "and" => SmtLang::And([arg_ids[0], arg_ids[1]]),
        "or" => SmtLang::Or([arg_ids[0], arg_ids[1]]),
        "not" => SmtLang::Not(arg_ids[0]),
        _ => return Err(format!("Unsupported operator: {}", operator)),
    };

    Ok(builder.add(op))
}

pub fn split_arguments(args: &str) -> Result<Vec<String>, String> {
    let mut result = Vec::new();
    let mut depth = 0;
    let mut current = String::new();

    // println!("Splitting arguments: {}", args);

    for (i, c) in args.chars().enumerate() {
        match c {
            '(' => {
                depth += 1;
                current.push(c);
                // println!("Depth increased to {} at position {}", depth, i);
            }
            ')' => {
                depth -= 1;
                current.push(c);
                // println!("Depth decreased to {} at position {}", depth, i);
                if depth == 0 {
                    result.push(current.trim().to_string());
                    current.clear();
                } else if depth < 0 {
                    return Err(format!(
                        "Mismatched parentheses at character {}: unexpected ')'",
                        i
                    ));
                }
            }
            ' ' if depth == 0 => {
                if!current.is_empty() {
                    result.push(current.trim().to_string());
                    current.clear();
                }
            }
            _ => current.push(c),
        }
    }

    if!current.is_empty() {
        result.push(current.trim().to_string());
    }

    if depth!= 0 {
        return Err(format!(
            "Mismatched parentheses: {} unmatched '(' in input '{}' at end",
            depth, args
        ));
    }

    Ok(result)
}

pub fn load_expressions(file_path: &str) -> Result<Vec<RecExpr<SmtLang>>, String> {
    let content = fs::read_to_string(file_path)
       .map_err(|e| format!("Failed to read file: {}", e))?;

    let mut expressions = Vec::new();
    for line in content.lines() {
        if line.starts_with("(assert ") {
            if let Some(inner) = line.strip_prefix("(assert ").and_then(|s| s.strip_suffix(")")) {
                let mut builder = RecExpr::default();
                parse_smt_expression(inner, &mut builder)
                   .map_err(|e| format!("Failed to parse expression: {}", e))?;
                println!("RecExpr after parsing: {:?}", builder);

                expressions.push(builder);
            }

        }
    }
    if expressions.is_empty() {
        Err("No valid expressions found in the file".to_string())
    } else {
        Ok(expressions)
    }
}
