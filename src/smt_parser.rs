use egg::*;
use std::fs;
use ordered_float::NotNan;

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
        "+" => SmtLang::Add(arg_ids),
        "*" => SmtLang::Mul(arg_ids),
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
        "sqrt" => if arg_ids.len() == 1 {
            SmtLang::Sqrt(arg_ids[0]) 
        } else {
            return Err("Sqrt requires exactly one argument".to_string());
        },
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

// pub fn parse_smt_expression(expr: &str, builder: &mut RecExpr<SmtLang>) -> Result<Id, String> {
//     let expr = expr.trim();
    
//     let mut count = 0;
//     let mut complete = String::new();
    
//     for c in expr.chars() {
//         complete.push(c);
//         match c {
//             '(' => count += 1,
//             ')' => {
//                 count -= 1;
//                 if count == 0 && complete.starts_with('(') { break; }
//             }
//             _ => {}
//         }
//     }
 
//     let expr = if complete.starts_with('(') && count == 0 {
//         complete[1..complete.len()-1].trim()
//     } else {
//         expr
//     };
 
//     if let Ok(value) = expr.parse::<f64>() {
//         let constant = NotNan::new(value).map_err(|_| "Invalid constant value".to_string())?;
//         return Ok(builder.add(SmtLang::Constant(constant)));
//     }
 
//     if !expr.contains(' ') {
//         let symbol = Symbol::from(expr);
//         return Ok(builder.add(SmtLang::Symbol(symbol)));
//     }
 
//     let first_space = expr.find(' ').ok_or("Invalid SMT expression")?;
//     let operator = expr[..first_space].trim();
//     let args = &expr[first_space + 1..];
 
//     println!("Operator: '{}', Arguments: '{}'", operator, args);
 
//     let arg_list = split_arguments(args)?;
//     let arg_ids = arg_list.iter()
//         .map(|arg| parse_smt_expression(arg, builder))
//         .collect::<Result<_, _>>()?;
 
//     let op = match operator {
//         "+" => SmtLang::Add(arg_ids),
//         "*" => SmtLang::Mul(arg_ids), 
//         "-" => if arg_ids.len() >= 2 { SmtLang::Sub([arg_ids[0], arg_ids[1]]) }
//               else { return Err("Subtraction requires 2 arguments".to_string()) },
//     "/" => if arg_ids.len() == 2 { SmtLang::Div([arg_ids[0], arg_ids[1]]) }
//           else { return Err("Division requires 2 arguments".to_string()) },
//         "^" => if arg_ids.len() >= 2 { SmtLang::Pow([arg_ids[0], arg_ids[1]]) }
//               else { return Err("Power requires 2 arguments".to_string()) },
//         ">" => if arg_ids.len() >= 2 { SmtLang::Gt([arg_ids[0], arg_ids[1]]) }
//               else { return Err("Greater than requires 2 arguments".to_string()) },
//         ">=" => if arg_ids.len() >= 2 { SmtLang::Ge([arg_ids[0], arg_ids[1]]) }
//                else { return Err("Greater than or equal requires 2 arguments".to_string()) },
//         "<" => if arg_ids.len() >= 2 { SmtLang::Lt([arg_ids[0], arg_ids[1]]) }
//               else { return Err("Less than requires 2 arguments".to_string()) },
//         "<=" => if arg_ids.len() >= 2 { SmtLang::Le([arg_ids[0], arg_ids[1]]) }
//                else { return Err("Less than or equal requires 2 arguments".to_string()) },
//         "=" => if arg_ids.len() >= 2 { SmtLang::Eq([arg_ids[0], arg_ids[1]]) }
//               else { return Err("Equals requires 2 arguments".to_string()) },
//         "and" => if arg_ids.len() >= 2 { SmtLang::And([arg_ids[0], arg_ids[1]]) }
//                 else { return Err("And requires 2 arguments".to_string()) },
//         "or" => if arg_ids.len() >= 2 { SmtLang::Or([arg_ids[0], arg_ids[1]]) }
//                else { return Err("Or requires 2 arguments".to_string()) },
//         "not" => if arg_ids.len() >= 1 { SmtLang::Not(arg_ids[0]) }
//                 else { return Err("Not requires 1 argument".to_string()) },
//         "sqrt" => if arg_ids.len() >= 1 { SmtLang::Sqrt(arg_ids[0]) }
//                  else { return Err("Sqrt requires 1 argument".to_string()) },
//         _ => return Err(format!("Unsupported operator: {}", operator)),
//     };
 
//     Ok(builder.add(op))
//  }

//  pub fn split_arguments(args: &str) -> Result<Vec<String>, String> {
//     let mut result = Vec::new();
//     let mut depth = 0;
//     let mut current = String::new();
    
//     for c in args.chars() {
//         match c {
//             '(' => {
//                 depth += 1;
//                 current.push(c);
//             }
//             ')' => {
//                 depth -= 1;
//                 current.push(c);
//             }
//             ' ' if depth == 0 && !current.is_empty() => {
//                 result.push(current.clone());
//                 current.clear();
//             }
//             _ => current.push(c)
//         }
//     }
    
//     // Add the last part if there's anything left
//     if !current.is_empty() {
//         result.push(current);
//     }
    
//     // Handle any unmatched parentheses (optional)
//     if depth != 0 {
//         return Err("Unmatched parentheses in arguments".to_string());
//     }
    
//     Ok(result)
// }


pub fn load_expressions(file_path: &str) -> Result<Vec<RecExpr<SmtLang>>, String> {
    let content = fs::read_to_string(file_path)
        .map_err(|e| format!("Failed to read file: {}", e))?;
 
    let mut expressions = Vec::new();
    
    for line in content.lines() {
        let line = line.trim();
        if line.starts_with("(assert ") {
            let inner = line
                .strip_prefix("(assert ")
                .and_then(|s| s.strip_suffix(")"))
                .ok_or("Invalid assert format")?;
                
            println!("Parsing assert: {}", inner);
            
            let mut builder = RecExpr::default();
            parse_smt_expression(inner, &mut builder)?;
            expressions.push(builder);
        }
    }
    Ok(expressions)
 }