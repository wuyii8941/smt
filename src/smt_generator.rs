use std::fs::File;
use std::io::{self, BufRead, Write};

pub struct SMTGenerator {
    pub original_lines: Vec<String>,  // 原始 SMT 文件的内容
}

impl SMTGenerator {
    /// 从文件加载原始 SMT 内容
    pub fn from_file(file_path: &str) -> io::Result<Self> {
        let file = File::open(file_path)?;
        let reader = io::BufReader::new(file);

        // 逐行读取文件内容
        let lines: Vec<String> = reader.lines().filter_map(Result::ok).collect();
        Ok(SMTGenerator {
            original_lines: lines,
        })
    }

    /// 替换 assert 行并生成新的 SMT 文件
    pub fn generate_with_rewrites(
        &self,
        rewritten_expressions: Vec<&str>,
        output_path: &str,
    ) -> io::Result<()> {
        let mut rewritten_lines = Vec::new();
        let mut expr_index = 0;

        // 遍历原始 SMT 文件的每一行
        for line in &self.original_lines {
            if line.trim().starts_with("(assert ") {
                // 如果是 assert 行，用重写表达式替换
                if expr_index < rewritten_expressions.len() {
                    rewritten_lines.push(format!("(assert {})", rewritten_expressions[expr_index]));
                    expr_index += 1;
                } else {
                    // 如果没有对应的重写表达式，保留原始 assert 行
                    rewritten_lines.push(line.clone());
                }
            } else {
                // 非 assert 行直接保留
                rewritten_lines.push(line.clone());
            }
        }

        // 将重写后的内容写入新的文件
        let mut file = File::create(output_path)?;
        for rewritten_line in rewritten_lines {
            writeln!(file, "{}", rewritten_line)?;
        }

        Ok(())
    }
}
