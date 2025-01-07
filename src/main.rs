/* 主流程 */ 
use std::env;
use std::process;
use env_logger;


mod smt_lang;
mod smt_parser;
mod smt_rewrite; 
mod smt_generator;


fn main() {
    env_logger::init(); // 初始化日志

    let args: Vec<String> = env::args().collect();
    if args.len() != 3 {
        eprintln!("Usage: {} <input_file> <output_file>", args[0]);
        process::exit(1);
    }

    let input_file = &args[1];
    let output_file = &args[2];

    // 从 SMT 文件中解析表达式
    let expressions = match smt_parser::load_expressions(input_file) {
        Ok(exprs) => exprs,
        Err(e) => {
            eprintln!("Error loading expressions: {}", e);
            process::exit(1);
        }
    };

    // 批量应用重写规则
    let rewritten_expressions = smt_rewrite::rewrite_expressions(expressions);

    // 将 Vec<String> 转换为 Vec<&str>
    let rewritten_expressions_refs: Vec<&str> = rewritten_expressions.iter().map(|s| s.as_str()).collect();

    // 加载原始 SMT 文件并生成新的 SMT 文件
    let generator = match smt_generator::SMTGenerator::from_file(input_file) {
        Ok(gen) => gen,
        Err(e) => {
            eprintln!("Error loading SMT file: {}", e);
            process::exit(1);
        }
    };

    if let Err(e) = generator.generate_with_rewrites(rewritten_expressions_refs, output_file) {
        eprintln!("Error generating rewritten SMT file: {}", e);
        process::exit(1);
    }

    println!("Rewritten SMT file has been saved to {}", output_file);
}